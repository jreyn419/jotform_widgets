#!/usr/bin/env python3
"""
EMS Inventory JSON Editor v4.0.0 (PyQt6)
A GUI tool for managing EMS inventory checklist JSON files
with a master list as the canonical item registry.

Place this file in the root of your GitHub Pages repo (parent of
data/checklists/{rig}/*.json) and run it.

Requirements: pip3 install PyQt6 PyQt6-WebEngine pdfplumber
"""

import os
import sys
import re
import shutil
import tempfile
import time
import webbrowser
import subprocess
import json
import threading
import hashlib
import base64
import ssl
import http.cookiejar
import urllib.request
import urllib.error
from urllib.parse import urlparse
from datetime import datetime
from collections import defaultdict
from copy import deepcopy
import html as html_module

os.environ["QTWEBENGINE_CHROMIUM_FLAGS"] = "--disable-logging"

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QTabWidget, QSplitter,
    QTreeWidget, QTreeWidgetItem, QVBoxLayout, QHBoxLayout, QFormLayout,
    QLabel, QLineEdit, QPushButton, QComboBox, QSpinBox, QCheckBox,
    QGroupBox, QScrollArea, QProgressBar, QStatusBar, QToolBar,
    QFileDialog, QInputDialog, QMessageBox, QMenu, QSizePolicy, QFrame,
    QTableWidget, QTableWidgetItem, QHeaderView, QAbstractItemView,
    QStyledItemDelegate, QCompleter, QDialog, QDialogButtonBox,
    QAbstractItemDelegate
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal, QTimer, QUrl
from PyQt6.QtGui import QAction, QShortcut, QKeySequence, QColor, QBrush, QPalette, QPainter, QPixmap, QPen, QIcon, QFont

try:
    from PyQt6.QtWebEngineWidgets import QWebEngineView
    HAS_WEBENGINE = True
except ImportError:
    HAS_WEBENGINE = False


def _emoji_icon(char, size=16):
    """Render an emoji character to a QIcon."""
    px = QPixmap(size, size)
    px.fill(QColor(0, 0, 0, 0))
    p = QPainter(px)
    font = QFont()
    font.setPixelSize(size - 2)
    p.setFont(font)
    p.drawText(px.rect(), Qt.AlignmentFlag.AlignCenter, char)
    p.end()
    return QIcon(px)


# Cached icons — populated after QApplication is created
_ICONS = {}

def _init_icons():
    global _ICONS
    _ICONS = {
        "area": _emoji_icon("\U0001f4e6"),
        "cat": _emoji_icon("\U0001f4c2"),
        "group": _emoji_icon("\U0001f4c1"),
        "seal": _emoji_icon("\U0001f512"),
        "warn": _emoji_icon("\u26a0"),
    }


class DragDropTree(QTreeWidget):
    """QTreeWidget with multi-select, drag-drop, inline rename, and state persistence."""
    ROLE_CLEAN_NAME = Qt.ItemDataRole.UserRole + 1
    itemsDropped = pyqtSignal(list, object)  # (source_data_list, target_data)
    itemRenamed = pyqtSignal(QTreeWidgetItem, str)     # (item, new_text)
    focusGained = pyqtSignal()                          # emitted on focus-in

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setColumnCount(2)
        self.setHeaderHidden(True)
        self.header().setStretchLastSection(False)
        self.header().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        self.header().setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        self.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setDragDropMode(QAbstractItemView.DragDropMode.DragDrop)
        self.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self._renaming = False
        self._rename_guard = False
        self._drag_source_items = []
        self._drag_hover_item = None
        self._editor_closed_at = 0  # monotonic timestamp
        self._pre_rename_expanded = None
        self.itemChanged.connect(self._on_item_changed)
        self.itemDoubleClicked.connect(self._on_double_click)

    def startDrag(self, supportedActions):
        """Capture selected items before Qt might clear selection during drag."""
        self._drag_source_items = list(self.selectedItems())
        super().startDrag(supportedActions)

    def dragEnterEvent(self, event):
        event.acceptProposedAction()

    def dragMoveEvent(self, event):
        event.acceptProposedAction()
        # Highlight drop target
        target = self.itemAt(event.position().toPoint())
        if target is not self._drag_hover_item:
            if self._drag_hover_item:
                self._drag_hover_item.setBackground(0, QBrush())
                self._drag_hover_item.setBackground(1, QBrush())
            self._drag_hover_item = target
            if target and target not in self._drag_source_items:
                target.setBackground(0, QBrush(QColor("#45475a")))
                target.setBackground(1, QBrush(QColor("#45475a")))

    def _clear_drag_highlight(self):
        if self._drag_hover_item:
            try:
                self._drag_hover_item.setBackground(0, QBrush())
                self._drag_hover_item.setBackground(1, QBrush())
            except RuntimeError:
                pass
            self._drag_hover_item = None

    def dragLeaveEvent(self, event):
        self._clear_drag_highlight()
        super().dragLeaveEvent(event)

    def dropEvent(self, event):
        self._clear_drag_highlight()
        if event.source() is not self:
            event.ignore()
            return
        target = self.itemAt(event.position().toPoint())
        if not target:
            event.ignore()
            return
        source_items = self.selectedItems()
        if not source_items:
            source_items = getattr(self, '_drag_source_items', [])
        if not source_items or target in source_items:
            event.ignore()
            return
        # Serialize all data BEFORE accepting — Qt may delete items after accept
        target_data = target.data(0, Qt.ItemDataRole.UserRole)
        source_data = []
        for si in source_items:
            try:
                source_data.append(si.data(0, Qt.ItemDataRole.UserRole))
            except RuntimeError:
                source_data.append(None)
        # Prevent Qt from touching the tree
        event.setDropAction(Qt.DropAction.IgnoreAction)
        event.accept()
        self.itemsDropped.emit(source_data, target_data)

    def _on_double_click(self, item, column):
        """Start inline rename on double-click."""
        if not item:
            return
        try:
            # Save expand state — Qt toggles it on double-click before this fires
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data and data[0] in ("cat", "area", "group"):
                # Qt already toggled, so invert to get the original state
                self._pre_rename_expanded = not item.isExpanded()
                item.setExpanded(self._pre_rename_expanded)
            else:
                self._pre_rename_expanded = None
        except RuntimeError:
            return
        QTimer.singleShot(0, lambda: self._startRename(item))

    def _startRename(self, item):
        """Begin inline rename on the given item."""
        try:
            # Guard: block itemChanged while we set up the edit field
            self._rename_guard = True
            self._renaming = True
            clean = item.data(0, self.ROLE_CLEAN_NAME)
            if clean:
                item.setText(0, clean)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsEditable)
            self._rename_guard = False
            # Force edit even with NoEditTriggers
            self.setEditTriggers(QAbstractItemView.EditTrigger.AllEditTriggers)
            self.editItem(item, 0)
            self.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        except RuntimeError:
            self._renaming = False
            self._rename_guard = False

    def _on_item_changed(self, item, column):
        """Handle inline rename completion."""
        if self._rename_guard:
            return
        if self._renaming and column == 0:
            self._renaming = False
            self._editor_closed_at = time.monotonic()
            try:
                new_text = item.text(0).strip()
            except RuntimeError:
                return
            if new_text:
                self.itemRenamed.emit(item, new_text)

    def closeEditor(self, editor, hint):
        """Called by Qt when inline editor closes. Record timestamp."""
        super().closeEditor(editor, hint)
        self._editor_closed_at = time.monotonic()

    def commitData(self, editor):
        """Called by Qt when editor data is committed. Also record timestamp."""
        super().commitData(editor)
        self._editor_closed_at = time.monotonic()

    def event(self, event):
        """Intercept keyboard events for rename, copy, and Enter suppression."""
        from PyQt6.QtCore import QEvent
        if event.type() == QEvent.Type.KeyPress:
            key = event.key()
            mods = event.modifiers()
            # Ctrl+R: rename current item
            if key == Qt.Key.Key_R and mods & Qt.KeyboardModifier.ControlModifier:
                item = self.currentItem()
                if item:
                    self._startRename(item)
                return True
            # Ctrl+C: copy selected items
            if key == Qt.Key.Key_C and mods & Qt.KeyboardModifier.ControlModifier:
                self._copySelected()
                return True
            # Enter/Return handling
            if key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                # Suppress if currently editing or editor just closed
                if self.state() == QAbstractItemView.State.EditingState:
                    return super().event(event)  # let Qt handle editor commit
                if time.monotonic() - self._editor_closed_at < 0.3:
                    return True  # consumed — don't toggle
                item = self.currentItem()
                if item:
                    try:
                        data = item.data(0, Qt.ItemDataRole.UserRole)
                    except RuntimeError:
                        pass
                    else:
                        if data and data[0] in ("cat", "area", "group"):
                            item.setExpanded(not item.isExpanded())
                            return True  # consumed
        return super().event(event)

    def _copySelected(self):
        """Copy selected items to clipboard as tab-separated text."""
        from PyQt6.QtWidgets import QApplication as QApp
        lines = []
        for item in self.selectedItems():
            try:
                col0 = item.data(0, self.ROLE_CLEAN_NAME) or item.text(0)
                col1 = item.text(1).strip()
                line = f"{col0}\t{col1}" if col1 else col0
                lines.append(line)
            except RuntimeError:
                continue
        if lines:
            QApp.clipboard().setText("\n".join(lines))

    def save_expanded_state(self):
        """Save expanded state of all nodes, keyed by UserRole data."""
        state = set()
        def _collect(item):
            if item.isExpanded():
                data = item.data(0, Qt.ItemDataRole.UserRole)
                if data:
                    state.add(str(data))
            for i in range(item.childCount()):
                _collect(item.child(i))
        for i in range(self.topLevelItemCount()):
            _collect(self.topLevelItem(i))
        return state

    def restore_expanded_state(self, state):
        """Restore expanded state from a saved set."""
        def _restore(item):
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data and str(data) in state:
                item.setExpanded(True)
            for i in range(item.childCount()):
                _restore(item.child(i))
        for i in range(self.topLevelItemCount()):
            _restore(self.topLevelItem(i))

    def beginRebuild(self):
        """Call before clearing and rebuilding tree. Returns state to pass to endRebuild."""
        self._rename_guard = True
        return self.save_expanded_state()

    def endRebuild(self, state):
        """Call after rebuilding tree to restore state."""
        self.restore_expanded_state(state)
        self._rename_guard = False

    def select_by_data(self, target_data):
        """Select and scroll to the tree item whose UserRole data matches target_data."""
        def _find(item):
            try:
                if item.data(0, Qt.ItemDataRole.UserRole) == target_data:
                    return item
            except RuntimeError:
                return None
            for i in range(item.childCount()):
                found = _find(item.child(i))
                if found:
                    return found
            return None
        for i in range(self.topLevelItemCount()):
            found = _find(self.topLevelItem(i))
            if found:
                self.setCurrentItem(found)
                self.scrollToItem(found)
                return

    def focusInEvent(self, event):
        super().focusInEvent(event)
        self.focusGained.emit()


class ManagedTableWidget(QTableWidget):
    """QTableWidget that signals when any editor closes, for any reason."""
    editorClosed = pyqtSignal()  # emitted after closeEditor completes

    def closeEditor(self, editor, hint):
        super().closeEditor(editor, hint)
        self.editorClosed.emit()


class DesignationDelegate(QStyledItemDelegate):
    """Dropdown delegate for the Status column.
    Number keys 1-4 select items directly. Popup auto-shows on edit.
    """
    def __init__(self, options, parent=None):
        super().__init__(parent)
        self._options = options
        self._active_editor = None

    def createEditor(self, parent, option, index):
        combo = QComboBox(parent)
        combo.addItems(self._options)
        combo.setMaxVisibleItems(10)
        combo.setFrame(False)
        self._active_editor = combo
        combo.installEventFilter(self)
        combo.view().installEventFilter(self)
        # Auto-commit when user selects from popup
        combo.activated.connect(self._on_item_selected)
        # Auto-show popup unless triggered by typing
        table = self.parent()
        if not getattr(table, '_suppress_popup', False):
            from PyQt6.QtCore import QTimer
            QTimer.singleShot(0, lambda: self._show_popup_if_active(combo))
        return combo

    def _show_popup_if_active(self, combo):
        if combo is self._active_editor and combo.isVisible():
            combo.showPopup()

    def destroyEditor(self, editor, index):
        if editor is self._active_editor:
            self._active_editor = None
        super().destroyEditor(editor, index)

    def _commit_number_select(self):
        """Deferred commit after number key selection."""
        combo = self._active_editor
        if combo:
            self.commitData.emit(combo)
            self.closeEditor.emit(combo, QAbstractItemDelegate.EndEditHint.NoHint)

    def _on_item_selected(self, idx):
        """Called when user selects an item from the popup. Commit and close."""
        from PyQt6.QtCore import QTimer
        QTimer.singleShot(0, self._commit_number_select)

    def eventFilter(self, obj, event):
        from PyQt6.QtCore import QEvent
        if self._active_editor and event.type() == QEvent.Type.KeyPress:
            key = event.key()
            # Number keys 1-4 select items directly
            if Qt.Key.Key_1 <= key <= Qt.Key.Key_4:
                combo = self._active_editor
                idx = key - Qt.Key.Key_1 + 1
                if idx < combo.count():
                    combo.setCurrentIndex(idx)
                    combo.hidePopup()
                    # Defer commit to after popup event processing completes
                    from PyQt6.QtCore import QTimer
                    QTimer.singleShot(0, self._commit_number_select)
                    return True
            # Escape: close popup + editor in one press
            if key == Qt.Key.Key_Escape:
                combo = self._active_editor
                if combo.view().isVisible():
                    combo.hidePopup()
                self.closeEditor.emit(combo, QAbstractItemDelegate.EndEditHint.NoHint)
                return True
        # Only call super() for the combo editor itself.
        if obj is self._active_editor:
            return super().eventFilter(obj, event)
        return False

    def setEditorData(self, editor, index):
        val = index.data(Qt.ItemDataRole.DisplayRole) or ""
        idx = editor.findText(val)
        editor.setCurrentIndex(idx if idx >= 0 else 0)

    def setModelData(self, editor, model, index):
        model.setData(index, editor.currentText(), Qt.ItemDataRole.EditRole)

    def updateEditorGeometry(self, editor, option, index):
        editor.setGeometry(option.rect)


class CategoryDelegate(QStyledItemDelegate):
    """Searchable dropdown delegate for Category and Master Name columns.

    Shows an editable combo box that filters as the user types.
    Popup auto-shows on edit, limited to 10 visible items.
    Escape closes popup + editor in one press.
    """
    def __init__(self, get_categories_fn, parent=None):
        super().__init__(parent)
        self._get_categories = get_categories_fn
        self._active_editor = None

    def createEditor(self, parent, option, index):
        combo = QComboBox(parent)
        combo.setEditable(True)
        combo.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        combo.setMaxVisibleItems(10)
        categories = sorted(self._get_categories(), key=str.lower)
        combo.addItems(categories)
        completer = QCompleter(categories, combo)
        completer.setFilterMode(Qt.MatchFlag.MatchContains)
        completer.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        completer.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        completer.setMaxVisibleItems(10)
        combo.setCompleter(completer)
        combo.setFrame(False)
        self._active_editor = combo
        combo.installEventFilter(self)
        combo.view().installEventFilter(self)
        if combo.lineEdit():
            combo.lineEdit().installEventFilter(self)
        # Auto-commit when user selects from popup
        combo.activated.connect(self._on_item_selected)
        # Auto-show popup unless triggered by typing
        table = self.parent()
        if not getattr(table, '_suppress_popup', False):
            from PyQt6.QtCore import QTimer
            QTimer.singleShot(100, lambda: self._show_popup_if_active(combo))
        else:
            # Typing initiated: ensure line edit has focus
            from PyQt6.QtCore import QTimer
            QTimer.singleShot(0, lambda: combo.lineEdit().setFocus() if combo.lineEdit() else None)
        return combo

    def _show_popup_if_active(self, combo):
        """Show popup only if this combo is still the active editor."""
        if combo is self._active_editor and combo.isVisible():
            combo.showPopup()

    def destroyEditor(self, editor, index):
        if editor is self._active_editor:
            self._active_editor = None
        super().destroyEditor(editor, index)

    def _commit_selection(self):
        """Deferred commit after popup selection."""
        combo = self._active_editor
        if combo:
            self.commitData.emit(combo)
            self.closeEditor.emit(combo, QAbstractItemDelegate.EndEditHint.NoHint)

    def _on_item_selected(self, idx):
        """Called when user selects an item from the popup. Commit and close."""
        from PyQt6.QtCore import QTimer
        QTimer.singleShot(0, self._commit_selection)

    def eventFilter(self, obj, event):
        from PyQt6.QtCore import QEvent
        if self._active_editor and event.type() == QEvent.Type.KeyPress:
            if event.key() == Qt.Key.Key_Escape:
                combo = self._active_editor
                # If popup is visible, close everything in one Escape press
                if combo.view().isVisible():
                    combo.hidePopup()
                # Close the editor without committing
                self.closeEditor.emit(combo, QAbstractItemDelegate.EndEditHint.NoHint)
                return True
        # Only call super() for the combo editor itself, not popup view or line edit
        if obj is self._active_editor:
            return super().eventFilter(obj, event)
        return False

    def setEditorData(self, editor, index):
        val = index.data(Qt.ItemDataRole.DisplayRole) or ""
        idx = editor.findText(val)
        if idx >= 0:
            editor.setCurrentIndex(idx)
        else:
            editor.setCurrentText(val)

    def setModelData(self, editor, model, index):
        model.setData(index, editor.currentText(), Qt.ItemDataRole.EditRole)

    def updateEditorGeometry(self, editor, option, index):
        editor.setGeometry(option.rect)


class MoveToCategoryDialog(QDialog):
    """Searchable category picker dialog with editable combo + MatchContains completer."""
    def __init__(self, categories, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Move to Category")
        self.setMinimumWidth(350)
        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("Select target category:"))

        self._combo = QComboBox()
        self._combo.setEditable(True)
        self._combo.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self._combo.setMaxVisibleItems(10)
        sorted_cats = sorted(categories, key=str.lower)
        self._combo.addItems(sorted_cats)

        completer = QCompleter(sorted_cats, self._combo)
        completer.setFilterMode(Qt.MatchFlag.MatchContains)
        completer.setCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        completer.setCompletionMode(QCompleter.CompletionMode.PopupCompletion)
        completer.setMaxVisibleItems(10)
        self._combo.setCompleter(completer)
        self._combo.setCurrentIndex(-1)
        self._combo.lineEdit().clear()
        layout.addWidget(self._combo)

        # Auto-accept when user clicks dropdown item or picks from completer
        self._combo.view().clicked.connect(lambda: QTimer.singleShot(0, self.accept))
        completer.activated.connect(lambda: QTimer.singleShot(0, self.accept))

        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok |
            QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

        # Focus line edit and auto-show popup after dialog is shown
        QTimer.singleShot(100, self._show_and_focus)

    def _show_and_focus(self):
        self._combo.lineEdit().setFocus()

    def selected_category(self):
        return self._combo.currentText()


class SplitDialog(QDialog):
    """Dialog for manually splitting a compound item into multiple items."""
    def __init__(self, original_name, original_qty, parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"Split Item: {original_name}")
        self.setMinimumWidth(450)
        self._entries = []
        self._result = []

        layout = QVBoxLayout(self)
        layout.addWidget(QLabel(f"Original: <b>{original_name}</b>  (qty: {original_qty})"))
        layout.addWidget(QLabel("Enter the individual item names and quantities:"))

        self._entries_layout = QVBoxLayout()
        layout.addLayout(self._entries_layout)

        # Start with 2 entries
        self._add_entry(original_name, original_qty)
        self._add_entry("", original_qty)

        add_btn = QPushButton("+ Add Another")
        add_btn.clicked.connect(lambda: self._add_entry("", original_qty))
        layout.addWidget(add_btn)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok |
                                   QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def _add_entry(self, name="", qty=1):
        row = QHBoxLayout()
        name_edit = QLineEdit(name)
        name_edit.setPlaceholderText("Item name")
        name_edit.setMinimumWidth(300)
        row.addWidget(name_edit)
        qty_spin = QSpinBox()
        qty_spin.setRange(0, 9999)
        qty_spin.setValue(qty)
        qty_spin.setFixedWidth(70)
        row.addWidget(qty_spin)
        self._entries_layout.addLayout(row)
        self._entries.append((name_edit, qty_spin))

    def _on_accept(self):
        self._result = []
        for name_edit, qty_spin in self._entries:
            name = name_edit.text().strip()
            if name:
                self._result.append({"name": name, "qty": qty_spin.value()})
        if len(self._result) < 2:
            QMessageBox.warning(self, "Split", "Need at least 2 items to split.")
            return
        self.accept()

    def get_items(self):
        return self._result


VERSION = "5.0.0"
# == LEMSA / State EMS directory ===============================================

_LEMSA_DATA_DEFAULT = [
    # -- Alabama --
    {"name": "Alabama Office of EMS", "state": "Alabama", "counties": [], "url": "https://www.alabamapublichealth.gov/ems/"},
    # -- Alaska --
    {"name": "Alaska EMS Program", "state": "Alaska", "counties": [], "url": "https://dhss.alaska.gov/dph/Emergency/Pages/ems/default.aspx"},
    # -- Arizona --
    {"name": "Arizona Bureau of EMS & Trauma System", "state": "Arizona", "counties": [], "url": "https://www.azdhs.gov/preparedness/emergency-medical-services-trauma-system/"},
    # -- Arkansas --
    {"name": "Arkansas Dept. of Health – EMS", "state": "Arkansas", "counties": [], "url": "https://www.healthy.arkansas.gov/programs-services/topics/emergency-medical-services"},
    # -- California (LEMSAs) --
    {"name": "Alameda County EMS", "state": "California", "counties": ["Alameda"], "url": "https://ems.acgov.org/"},
    {"name": "Central California EMS Agency", "state": "California", "counties": ["Fresno", "Kings", "Madera", "Tulare"], "url": "https://www.fresnocountyca.gov/Departments/Public-Health/Emergency-Services"},
    {"name": "Coastal Valleys EMS Agency", "state": "California", "counties": ["Mendocino", "Sonoma"], "url": "https://www.coastalvalleysems.org/"},
    {"name": "Contra Costa EMS Agency", "state": "California", "counties": ["Contra Costa"], "url": "https://www.cchealth.org/about-contra-costa-health/divisions/ems"},
    {"name": "El Dorado County EMS Agency", "state": "California", "counties": ["El Dorado"], "url": "https://www.eldoradocounty.ca.gov/Public-Safety-Justice/Emergency-Medical-Services"},
    {"name": "Imperial County EMS Agency", "state": "California", "counties": ["Imperial"], "url": "https://www.icphd.org/emergency-medical-services/"},
    {"name": "Inland Counties Emergency Medical Agency (ICEMA)", "state": "California", "counties": ["Inyo", "Mono", "San Bernardino"], "url": "https://icema.sbcounty.gov/"},
    {"name": "Kern County EMS Agency", "state": "California", "counties": ["Kern"], "url": "https://www.kernpublichealth.com/emergency-medical-services"},
    {"name": "Los Angeles County EMS Agency", "state": "California", "counties": ["Los Angeles"], "url": "https://dhs.lacounty.gov/emergency-medical-services-agency/"},
    {"name": "Marin County EMS Agency", "state": "California", "counties": ["Marin"], "url": "https://ems.marinhhs.org/"},
    {"name": "Merced County EMS Agency", "state": "California", "counties": ["Merced"], "url": "https://www.countyofmerced.com/2261/Emergency-Medical-Services"},
    {"name": "Monterey County EMS Agency", "state": "California", "counties": ["Monterey"], "url": "https://www.co.monterey.ca.us/government/departments-a-h/health/emergency-medical-services"},
    {"name": "Mountain Counties EMS Agency (MCEMSA)", "state": "California", "counties": ["Alpine", "Amador", "Calaveras", "Mariposa"], "url": "https://www.mvemsa.org/"},
    {"name": "Napa County EMS Agency", "state": "California", "counties": ["Napa"], "url": "https://www.napacounty.gov/756/Emergency-Medical-Services-EMS-Agency"},
    {"name": "North Coast EMS", "state": "California", "counties": ["Del Norte", "Humboldt", "Lake"], "url": "http://www.northcoastems.com/"},
    {"name": "Northern California EMS Inc.", "state": "California", "counties": ["Lassen", "Modoc", "Plumas", "Sierra", "Trinity"], "url": "https://norcalems.org/"},
    {"name": "Orange County EMS Agency", "state": "California", "counties": ["Orange"], "url": "https://www.ochealthinfo.com/providers-partners/emergency-medical-services"},
    {"name": "Riverside County EMS Agency", "state": "California", "counties": ["Riverside"], "url": "https://www.rivcoems.org/"},
    {"name": "Sacramento County EMS Agency", "state": "California", "counties": ["Sacramento"], "url": "https://dhs.saccounty.gov/PUB/EMS/Pages/EMS-Home.aspx"},
    {"name": "San Benito County EMS Agency", "state": "California", "counties": ["San Benito"], "url": "https://www.cosb.us/departments/office-of-emergency-services-oes-and-emergency-medical-services/emergency-medical-services-ems"},
    {"name": "San Diego County EMS Agency", "state": "California", "counties": ["San Diego"], "url": "https://www.sandiegocounty.gov/content/sdc/ems.html"},
    {"name": "San Francisco EMS Agency", "state": "California", "counties": ["San Francisco"], "url": "https://sf.gov/departments/department-emergency-management/emergency-medical-services-agency"},
    {"name": "San Joaquin EMS Agency", "state": "California", "counties": ["San Joaquin"], "url": "https://www.sjgov.org/department/ems"},
    {"name": "San Luis Obispo County EMS Agency", "state": "California", "counties": ["San Luis Obispo"], "url": "https://www.slocounty.ca.gov/Departments/Health-Agency/Public-Health/Emergency-Medical-Services/Emergency-Medical-Services-Agency.aspx"},
    {"name": "San Mateo County EMS Agency", "state": "California", "counties": ["San Mateo"], "url": "https://www.smchealth.org/ems"},
    {"name": "Santa Barbara County EMS Agency", "state": "California", "counties": ["Santa Barbara"], "url": "https://www.countyofsb.org/412/Emergency-Medical-Services"},
    {"name": "Santa Clara County EMS Agency", "state": "California", "counties": ["Santa Clara"], "url": "https://emsagency.sccgov.org/home"},
    {"name": "Santa Cruz County EMS Agency", "state": "California", "counties": ["Santa Cruz"], "url": "https://www.santacruzhealth.org/HSAHome/HSADivisions/PublicHealth/EmergencyMedicalServices.aspx"},
    {"name": "Sierra-Sacramento Valley EMS Agency", "state": "California", "counties": ["Butte", "Colusa", "Glenn", "Nevada", "Placer", "Shasta", "Siskiyou", "Sutter", "Tehama", "Yuba"], "url": "https://www.ssvems.com/"},
    {"name": "Solano County EMS Agency", "state": "California", "counties": ["Solano"], "url": "https://www.solanocounty.com/depts/ems/default.asp"},
    {"name": "Stanislaus County EMS Agency", "state": "California", "counties": ["Stanislaus"], "url": "https://stanems.com/"},
    {"name": "Tuolumne County EMS Agency", "state": "California", "counties": ["Tuolumne"], "url": "https://www.tuolumnecounty.ca.gov/302/Emergency-Medical-Services"},
    {"name": "Ventura County EMS Agency", "state": "California", "counties": ["Ventura"], "url": "https://vchca.org/ems"},
    {"name": "Yolo County EMS Agency", "state": "California", "counties": ["Yolo"], "url": "https://www.yolocounty.org/government/general-government-departments/health-human-services/providers-partners/yolo-emergency-medical-services-agency-yemsa"},
    # -- Colorado --
    {"name": "Colorado Dept. of Public Health & Environment – EMS", "state": "Colorado", "counties": [], "url": "https://cdphe.colorado.gov/emergency-care/emergency-medical-services"},
    # -- Connecticut --
    {"name": "Connecticut Office of EMS", "state": "Connecticut", "counties": [], "url": "https://portal.ct.gov/dph/emergency-medical-services/ems/office-of-emergency-medical-services"},
    # -- Delaware --
    {"name": "Delaware Office of EMS", "state": "Delaware", "counties": [], "url": "https://dhss.delaware.gov/dhss/dph/ems/ems.html"},
    # -- District of Columbia --
    {"name": "DC Fire & EMS", "state": "District of Columbia", "counties": [], "url": "https://fems.dc.gov/"},
    # -- Florida --
    {"name": "Florida Bureau of EMS", "state": "Florida", "counties": [], "url": "https://www.floridahealth.gov/licensing-and-regulation/ems-system/index.html"},
    # -- Georgia --
    {"name": "Georgia Office of EMS & Trauma", "state": "Georgia", "counties": [], "url": "https://dph.georgia.gov/EMS"},
    # -- Hawaii --
    {"name": "Hawaii EMS & Injury Prevention System Branch", "state": "Hawaii", "counties": [], "url": "https://health.hawaii.gov/ems/"},
    # -- Idaho --
    {"name": "Idaho EMS Bureau", "state": "Idaho", "counties": [], "url": "https://healthandwelfare.idaho.gov/providers/emergency-medical-services-ems/emergency-medical-services"},
    # -- Illinois --
    {"name": "Illinois Dept. of Public Health – EMS", "state": "Illinois", "counties": [], "url": "https://dph.illinois.gov/topics-services/emergency-preparedness-response/ems.html"},
    # -- Indiana --
    {"name": "Indiana Dept. of Homeland Security – EMS", "state": "Indiana", "counties": [], "url": "https://www.in.gov/dhs/fire-prevention-and-public-safety/ems/"},
    # -- Iowa --
    {"name": "Iowa Dept. of Public Health – Bureau of EMS", "state": "Iowa", "counties": [], "url": "https://idph.iowa.gov/bureau-of-emergency-and-trauma-services"},
    # -- Kansas --
    {"name": "Kansas Board of EMS", "state": "Kansas", "counties": [], "url": "https://www.ksbems.org/"},
    # -- Kentucky --
    {"name": "Kentucky Board of EMS", "state": "Kentucky", "counties": [], "url": "https://kbems.ky.gov/"},
    # -- Louisiana --
    {"name": "Louisiana Bureau of EMS", "state": "Louisiana", "counties": [], "url": "https://ldh.la.gov/page/bureau-of-emergency-medical-services"},
    # -- Maine --
    {"name": "Maine EMS", "state": "Maine", "counties": [], "url": "https://www.maine.gov/ems/"},
    # -- Maryland --
    {"name": "Maryland Institute for EMS Systems (MIEMSS)", "state": "Maryland", "counties": [], "url": "https://www.miemss.org/"},
    # -- Massachusetts --
    {"name": "Massachusetts Dept. of Public Health – Office of EMS", "state": "Massachusetts", "counties": [], "url": "https://www.mass.gov/orgs/office-of-emergency-medical-services"},
    # -- Michigan --
    {"name": "Michigan Dept. of Health & Human Services – EMS", "state": "Michigan", "counties": [], "url": "https://www.michigan.gov/mdhhs/doing-business/providers/ems"},
    # -- Minnesota --
    {"name": "Minnesota EMS Regulatory Board (EMSRB)", "state": "Minnesota", "counties": [], "url": "https://mn.gov/emsrb/"},
    # -- Mississippi --
    {"name": "Mississippi Bureau of EMS", "state": "Mississippi", "counties": [], "url": "https://www.ems.ms.gov/"},
    # -- Missouri --
    {"name": "Missouri Bureau of EMS & Trauma", "state": "Missouri", "counties": [], "url": "https://health.mo.gov/safety/ems/"},
    # -- Montana --
    {"name": "Montana EMS & Trauma Systems", "state": "Montana", "counties": [], "url": "https://dphhs.mt.gov/publichealth/emsts"},
    # -- Nebraska --
    {"name": "Nebraska Dept. of Health & Human Services – EMS", "state": "Nebraska", "counties": [], "url": "https://dhhs.ne.gov/Pages/Emergency-Medical-Services.aspx"},
    # -- Nevada --
    {"name": "Nevada Dept. of Health & Human Services – EMS", "state": "Nevada", "counties": [], "url": "https://dpbh.nv.gov/Reg/EMS/EMS_-_Home/"},
    # -- New Hampshire --
    {"name": "New Hampshire Bureau of EMS", "state": "New Hampshire", "counties": [], "url": "https://www.nh.gov/safety/divisions/fstems/ems/"},
    # -- New Jersey --
    {"name": "New Jersey Office of EMS", "state": "New Jersey", "counties": [], "url": "https://www.nj.gov/health/ems/"},
    # -- New Mexico --
    {"name": "New Mexico EMS Bureau", "state": "New Mexico", "counties": [], "url": "https://www.nmhealth.org/about/erd/ecss/ems/"},
    # -- New York --
    {"name": "New York Bureau of EMS & Trauma Systems", "state": "New York", "counties": [], "url": "https://www.health.ny.gov/professionals/ems/"},
    # -- North Carolina --
    {"name": "North Carolina Office of EMS", "state": "North Carolina", "counties": [], "url": "https://www.ncdhhs.gov/divisions/health-service-regulation/north-carolina-office-emergency-medical-services"},
    # -- North Dakota --
    {"name": "North Dakota Dept. of Health – EMS", "state": "North Dakota", "counties": [], "url": "https://www.health.nd.gov/epr/emergency-medical-systems/"},
    # -- Ohio --
    {"name": "Ohio Division of EMS", "state": "Ohio", "counties": [], "url": "https://www.ems.ohio.gov/"},
    # -- Oklahoma --
    {"name": "Oklahoma Dept. of Health – EMS Division", "state": "Oklahoma", "counties": [], "url": "https://oklahoma.gov/health/protective-health/emergency-systems/ems-division.html"},
    # -- Oregon --
    {"name": "Oregon EMS & Trauma Systems", "state": "Oregon", "counties": [], "url": "https://www.oregon.gov/oha/ph/providerpartnerresources/emstraumasystems/"},
    # -- Pennsylvania --
    {"name": "Pennsylvania Bureau of EMS", "state": "Pennsylvania", "counties": [], "url": "https://www.health.pa.gov/topics/EMS/Pages/EMS.aspx"},
    # -- Rhode Island --
    {"name": "Rhode Island Division of EMS", "state": "Rhode Island", "counties": [], "url": "https://health.ri.gov/programs/emergencymedicalservices/"},
    # -- South Carolina --
    {"name": "South Carolina DHEC – Bureau of EMS", "state": "South Carolina", "counties": [], "url": "https://scdhec.gov/health/health-professionals-hpcs/emergency-medical-services-ems"},
    # -- South Dakota --
    {"name": "South Dakota EMS Program", "state": "South Dakota", "counties": [], "url": "https://doh.sd.gov/providers/licensure-certification/emergency-medical-services/"},
    # -- Tennessee --
    {"name": "Tennessee Office of EMS", "state": "Tennessee", "counties": [], "url": "https://www.tn.gov/health/health-program-areas/health-professional-boards/ems-board.html"},
    # -- Texas --
    {"name": "Texas DSHS – EMS/Trauma Systems", "state": "Texas", "counties": [], "url": "https://www.dshs.texas.gov/dshs-ems-trauma-systems"},
    # -- Utah --
    {"name": "Utah Bureau of EMS & Preparedness", "state": "Utah", "counties": [], "url": "https://bemsp.utah.gov/"},
    # -- Vermont --
    {"name": "Vermont EMS", "state": "Vermont", "counties": [], "url": "https://healthvermont.gov/emergency/ems"},
    # -- Virginia --
    {"name": "Virginia Office of EMS", "state": "Virginia", "counties": [], "url": "https://www.vdh.virginia.gov/emergency-medical-services/"},
    # -- Washington --
    {"name": "Washington Dept. of Health – Office of Community Health Systems (EMS & Trauma)", "state": "Washington", "counties": [], "url": "https://doh.wa.gov/public-health-provider-resources/emergency-medical-services-ems-systems"},
    # -- West Virginia --
    {"name": "West Virginia Office of EMS", "state": "West Virginia", "counties": [], "url": "https://oems.wv.gov/"},
    # -- Wisconsin --
    {"name": "Wisconsin Dept. of Health Services – EMS", "state": "Wisconsin", "counties": [], "url": "https://www.dhs.wisconsin.gov/ems/index.htm"},
    # -- Wyoming --
    {"name": "Wyoming Office of EMS", "state": "Wyoming", "counties": [], "url": "https://health.wyo.gov/publichealth/ems/"},
]

# == Data model ==============================================================

class Item:
    __slots__ = ("name", "qty", "group")
    def __init__(self, name, qty, group=None):
        self.name = name
        self.qty = qty
        self.group = group

class Category:
    __slots__ = ("name", "items")
    def __init__(self, name):
        self.name = name
        self.items = []

class Area:
    __slots__ = ("name", "sealable", "child_of", "categories")
    def __init__(self, name):
        self.name = name
        self.sealable = False
        self.child_of = None
        self.categories = []

class InventoryFile:
    def __init__(self, path):
        self.path = path
        self.areas = []

    @property
    def filename(self):
        return os.path.basename(self.path)

    @classmethod
    def from_file(cls, path):
        inv = cls(path)
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        inv.areas = cls._parse_json(data)
        return inv

    @staticmethod
    def _parse_json(data):
        """Parse JSON array into list of Area objects."""
        areas = []
        for area_obj in data:
            area_name = area_obj.get("area", "")
            if not area_name:
                continue
            area = Area(area_name)
            area.sealable = bool(area_obj.get("sealable", False))
            area.child_of = area_obj.get("childOf") or None
            for cat_obj in area_obj.get("categories", []):
                cat = Category(cat_obj.get("name", "General"))
                for item_obj in cat_obj.get("items", []):
                    cat.items.append(Item(
                        item_obj.get("name", ""),
                        item_obj.get("qty", 1),
                        item_obj.get("group")
                    ))
                area.categories.append(cat)
            areas.append(area)
        return areas

    def to_json_data(self):
        """Return JSON-serializable list of area dicts."""
        result = []
        for area in self.areas:
            area_obj = {"area": area.name}
            if area.sealable:
                area_obj["sealable"] = True
            if area.child_of:
                area_obj["childOf"] = area.child_of
            cats = []
            for cat in area.categories:
                cat_obj = {"name": cat.name}
                if cat.items:
                    items = []
                    for it in cat.items:
                        item_obj = {"name": it.name, "qty": it.qty}
                        if it.group:
                            item_obj["group"] = it.group
                        items.append(item_obj)
                    cat_obj["items"] = items
                cats.append(cat_obj)
            area_obj["categories"] = cats
            result.append(area_obj)
        return result

    def save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump(self.to_json_data(), f, indent=2, ensure_ascii=False)
            f.write("\n")

    def all_item_names(self):
        return {item.name for area in self.areas for cat in area.categories for item in cat.items}

    def rename_item_everywhere(self, old_name, new_name):
        count = 0
        for area in self.areas:
            for cat in area.categories:
                for item in cat.items:
                    if item.name == old_name:
                        item.name = new_name
                        count += 1
        return count

    def item_locations(self, item_name):
        locs = []
        for area in self.areas:
            for cat in area.categories:
                for item in cat.items:
                    if item.name == item_name:
                        locs.append({"area": area.name, "category": cat.name,
                                     "qty": item.qty, "item_ref": item})
        return locs


# == Master list model ========================================================

class MasterItem:
    __slots__ = ("name", "emsa_min", "group")
    def __init__(self, name, emsa_min, group=None):
        self.name = name
        self.emsa_min = emsa_min
        self.group = group

class MasterCategory:
    __slots__ = ("name", "items")
    def __init__(self, name):
        self.name = name
        self.items = []

class MasterList:
    def __init__(self, path):
        self.path = path
        self.categories = []

    @classmethod
    def from_file(cls, path):
        ml = cls(path)
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        for cat_obj in data.get("categories", []):
            cat = MasterCategory(cat_obj.get("name", "Uncategorized"))
            for item_obj in cat_obj.get("items", []):
                cat.items.append(MasterItem(
                    item_obj.get("name", ""),
                    item_obj.get("emsa_min", 1),
                    item_obj.get("group")
                ))
            ml.categories.append(cat)
        return ml

    def to_json_data(self):
        result = {"categories": []}
        for cat in self.categories:
            items = []
            for it in cat.items:
                item_obj = {"name": it.name, "emsa_min": it.emsa_min}
                if it.group:
                    item_obj["group"] = it.group
                items.append(item_obj)
            result["categories"].append({"name": cat.name, "items": items})
        return result

    def save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump(self.to_json_data(), f, indent=2, ensure_ascii=False)
            f.write("\n")

    def all_item_names(self):
        return {item.name for cat in self.categories for item in cat.items}

    def find_item(self, name):
        for cat in self.categories:
            for item in cat.items:
                if item.name == name:
                    return cat, item
        return None, None

    def rename_item(self, old_name, new_name):
        for cat in self.categories:
            for item in cat.items:
                if item.name == old_name:
                    item.name = new_name
                    return True
        return False

    def iter_all_items(self):
        """Yield (cat, item) for every item."""
        for cat in self.categories:
            for item in cat.items:
                yield cat, item


# == Application ==============================================================


# == Worker thread for LEMSA checks ========================================

class CheckWorker(QThread):
    """Background thread for LEMSA document checks."""
    progress = pyqtSignal(int, str)   # (step, message)
    finished = pyqtSignal(dict)       # results dict
    error = pyqtSignal(str)           # error message

    def __init__(self, app, items):
        super().__init__()
        self.app = app
        self.items = items  # list of (lemsa_data, conf) tuples

    def run(self):
        results = {"changed": [], "baselined": [], "unchanged": [], "errors": []}
        total = len(self.items)
        for i, (lemsa, conf) in enumerate(self.items):
            name = lemsa["name"]
            self.progress.emit(i, f"{i+1}/{total}: {name}")
            conf["last_checked"] = datetime.now().strftime("%Y-%m-%d %H:%M")
            try:
                doc_url = self.app._resolve_doc_url(conf["page_url"], conf["link_text"])
                conf["resolved_url"] = doc_url
                doc_data = self.app._fetch_url(doc_url)
                new_hash = hashlib.sha256(doc_data).hexdigest()
                old_hash = conf.get("last_hash", "")
                if not old_hash:
                    conf["last_hash"] = new_hash
                    self.app._save_lemsa_pdf(name, doc_data)
                    results["baselined"].append(name)
                elif new_hash != old_hash:
                    conf["last_hash"] = new_hash
                    self.app._save_lemsa_pdf(name, doc_data)
                    results["changed"].append(name)
                else:
                    results["unchanged"].append(name)
            except Exception as e:
                results["errors"].append(f"{name}: {e}")
        self.app._save_lemsa_config()
        self.finished.emit(results)


class SingleCheckWorker(QThread):
    """Background thread for single LEMSA check."""
    progress = pyqtSignal(str)
    finished = pyqtSignal(str)
    error = pyqtSignal(str)

    def __init__(self, app, name, conf):
        super().__init__()
        self.app = app
        self.name = name
        self.conf = conf

    def run(self):
        conf = self.conf
        name = self.name
        conf["last_checked"] = datetime.now().strftime("%Y-%m-%d %H:%M")
        try:
            self.progress.emit(f"{name}: resolving link...")
            page_url = conf.get("page_url", "")
            link_text = conf.get("link_text", "")
            if not page_url or not link_text:
                raise Exception("Missing page URL or link text")
            doc_url = self.app._resolve_doc_url(page_url, link_text)
            conf["resolved_url"] = doc_url

            self.progress.emit(f"{name}: downloading...")
            doc_data = self.app._fetch_url(doc_url)

            self.progress.emit(f"{name}: comparing...")
            new_hash = hashlib.sha256(doc_data).hexdigest()
            old_hash = conf.get("last_hash", "")

            if not old_hash:
                conf["last_hash"] = new_hash
                saved = self.app._save_lemsa_pdf(name, doc_data)
                msg = f"{name}: baseline captured ({len(doc_data)} bytes)"
                if saved: msg += f" — saved to {os.path.basename(saved)}"
            elif new_hash != old_hash:
                conf["last_hash"] = new_hash
                saved = self.app._save_lemsa_pdf(name, doc_data)
                msg = f"{name}: DOCUMENT CHANGED"
                if saved: msg += f" — saved to {os.path.basename(saved)}"
            else:
                msg = f"{name}: no changes detected"
            self.app._save_lemsa_config()
            self.finished.emit(msg)
        except Exception as e:
            self.app._save_lemsa_config()
            self.error.emit(f"{name}: {e}")


class CompareWorker(QThread):
    """Background thread for PDF extraction and comparison."""
    progress = pyqtSignal(int, int, str)  # (step, total, message)
    finished = pyqtSignal(dict)            # {"all_lemsa": {...}, "new": [...], "missing": [...], "qty_diffs": [...]}
    error = pyqtSignal(str)

    def __init__(self, app, pdfs, dl_dir):
        super().__init__()
        self.app = app
        self.pdfs = pdfs
        self.dl_dir = dl_dir

    def run(self):
        total = len(self.pdfs)
        all_lemsa = {}
        errors = []
        for i, pdf_name in enumerate(self.pdfs):
            self.progress.emit(i, total, f"Extracting {i+1}/{total}: {pdf_name}")
            try:
                items = self.app._extract_pdf_items(os.path.join(self.dl_dir, pdf_name))
                source = pdf_name.replace(".pdf", "").replace("_", " ")
                for name, qty in items:
                    key = name.lower()
                    if key not in all_lemsa:
                        all_lemsa[key] = {"name": name, "qty": qty, "sources": [source]}
                    else:
                        existing = all_lemsa[key]
                        existing["qty"] = max(existing["qty"], qty)
                        if source not in existing["sources"]:
                            existing["sources"].append(source)
            except Exception as e:
                errors.append(f"{pdf_name}: {e}")

        if errors and not all_lemsa:
            self.error.emit(f"Extraction failed: {'; '.join(errors)}")
            return

        # Compare against master
        master_names = {}
        for cat, item in self.app.master_list.iter_all_items():
            master_names[item.name.lower()] = (cat.name, item)

        new_items = []
        qty_diffs = []
        for key, data in sorted(all_lemsa.items(), key=lambda x: x[1]["name"].lower()):
            if key in master_names:
                cat_name, master_item = master_names[key]
                if data["qty"] != master_item.emsa_min:
                    qty_diffs.append({
                        "name": master_item.name, "master_qty": master_item.emsa_min,
                        "lemsa_qty": data["qty"], "sources": data["sources"],
                        "cat": cat_name, "item_ref": master_item,
                    })
            else:
                new_items.append(data)

        missing_items = []
        lemsa_keys = set(all_lemsa.keys())
        for key, (cat_name, item) in sorted(master_names.items(), key=lambda x: x[1][1].name.lower()):
            if key not in lemsa_keys:
                missing_items.append({"name": item.name, "cat": cat_name})

        # Serializable version for caching (no item_ref)
        cache_lemsa = {}
        for k, v in all_lemsa.items():
            cache_lemsa[k] = {"name": v["name"], "qty": v["qty"], "sources": v["sources"]}

        self.finished.emit({
            "all_lemsa": cache_lemsa,
            "new": new_items, "missing": missing_items, "qty_diffs": qty_diffs,
            "pdf_count": len(self.pdfs), "errors": errors,
        })


# == Confirmation Dialog =====================================================

class ConfirmDialog(QDialog):
    """Dialog with keyboard shortcuts: Y=Yes, N=No, arrow keys navigate, Enter selects."""

    def __init__(self, parent, title, text, buttons=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(350)
        self.setStyleSheet("""
            QDialog {
                background-color: #1e1e2e;
                color: #cdd6f4;
            }
            QLabel {
                color: #cdd6f4;
                font-size: 13px;
            }
            QPushButton {
                background-color: #313244;
                color: #cdd6f4;
                border: 1px solid #45475a;
                border-radius: 4px;
                padding: 6px 16px;
                min-width: 80px;
                font-size: 13px;
            }
            QPushButton:hover {
                background-color: #45475a;
            }
            QPushButton:focus {
                border: 2px solid #89b4fa;
                background-color: #45475a;
            }
        """)

        layout = QVBoxLayout(self)
        layout.setSpacing(12)
        layout.setContentsMargins(16, 16, 16, 12)

        label = QLabel(text)
        label.setWordWrap(True)
        layout.addWidget(label)

        btn_layout = QHBoxLayout()
        btn_layout.addStretch()

        if buttons is None:
            buttons = [("&Yes", True), ("&No", False)]

        self._result = None
        self._buttons = []
        for i, (label_text, value) in enumerate(buttons):
            btn = QPushButton(label_text)
            btn.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
            btn.setMinimumWidth(80)
            btn.clicked.connect(lambda checked=False, v=value: self._pick(v))
            btn_layout.addWidget(btn)
            self._buttons.append((btn, value))
            # Focus the last button (No) by default for safety
            if i == len(buttons) - 1:
                btn.setDefault(True)
                btn.setFocus()

        btn_layout.addStretch()
        layout.addLayout(btn_layout)

        # Install event filter on each button to intercept arrow keys
        for btn, _ in self._buttons:
            btn.installEventFilter(self)

    def _pick(self, value):
        self._result = value
        self.accept()

    def eventFilter(self, obj, event):
        """Intercept arrow keys on buttons to prevent Qt's built-in focus cycling."""
        from PyQt6.QtCore import QEvent
        if event.type() == QEvent.Type.KeyPress:
            key = event.key()
            # Find which button has focus
            focused = None
            for i, (btn, _) in enumerate(self._buttons):
                if btn is obj:
                    focused = i
                    break
            if focused is not None:
                if key == Qt.Key.Key_Right:
                    if focused < len(self._buttons) - 1:
                        self._buttons[focused + 1][0].setFocus()
                    return True  # always consume
                elif key == Qt.Key.Key_Left:
                    if focused > 0:
                        self._buttons[focused - 1][0].setFocus()
                    return True  # always consume
                elif key in (Qt.Key.Key_Up, Qt.Key.Key_Down, Qt.Key.Key_Tab, Qt.Key.Key_Backtab):
                    return True  # consume, no action
        return super().eventFilter(obj, event)

    def keyPressEvent(self, event):
        key = event.key()
        text = event.text().lower()

        # Single-key shortcuts from button labels (the char after &)
        for btn, value in self._buttons:
            label = btn.text()
            amp = label.find("&")
            if amp >= 0 and amp + 1 < len(label):
                shortcut = label[amp + 1].lower()
                if text == shortcut:
                    self._pick(value)
                    return

        # Enter/Return selects focused button
        if key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            for btn, value in self._buttons:
                if btn.hasFocus():
                    self._pick(value)
                    return

        # Escape = reject (same as No/Cancel)
        if key == Qt.Key.Key_Escape:
            self._result = False
            self.reject()
            return

        super().keyPressEvent(event)

    @staticmethod
    def confirm(parent, title, text):
        """Show a Yes/No dialog. Returns True if Yes."""
        dlg = ConfirmDialog(parent, title, text)
        dlg.exec()
        return dlg._result is True

    @staticmethod
    def confirm_three(parent, title, text, btn_labels):
        """Show a 3-button dialog. Returns the value of the clicked button."""
        dlg = ConfirmDialog(parent, title, text, btn_labels)
        dlg.exec()
        return dlg._result


# == Application (PyQt6) =====================================================

class App(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"EMS Inventory Editor v{VERSION}")
        self.resize(1150, 750)
        self.setMinimumSize(900, 550)

        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.normpath(os.path.join(self.base_dir, "..", ".."))
        self.checklists_dir = os.path.join(self.repo_root, "data", "checklists")
        self.master_list_path = os.path.join(self.checklists_dir, "master_list.json")
        self.master_list = None
        self.current_rig = None
        self.current_file = None
        self.rig_files = []
        self.dirty = False
        self.dirty_master = False
        self.lemsa_config_path = os.path.join(self.repo_root, "reference", "lemsa_config.json")
        self.lemsa_directory_path = os.path.join(self.repo_root, "reference", "lemsa_directory.json")
        self.lemsa_data = []
        self.lemsa_config = {}
        self._checking = False
        self._worker = None
        self._compiled_list_path = None
        self._edit_guard = False  # prevents re-entrant cell-change handling
        self._edit_dir = "across"   # "across" = row-first, "down" = column-first
        self._edit_scope = "empty"  # "empty" = skip filled cells, "all" = visit every cell
        self._editing_cell = None   # (row, col) when a cell edit is in progress
        self._ui_state_path = os.path.join(self.base_dir, "ui_state.json")

        # Undo/redo stacks (separate per tree, snapshot-based)
        self._rig_undo_stack = []
        self._rig_redo_stack = []
        self._rig_last_snap = None
        self._master_undo_stack = []
        self._master_redo_stack = []
        self._master_last_snap = None
        self._undo_suppress = False  # suppress during undo/redo restore
        self._undo_max = 50

        # Clipboard
        self._clipboard = None  # {"items": [...], "mode": "copy"/"cut", "source": "rig"/"master"}
        self._last_focused_tree = "rig"  # track which tree was last focused

        # Preview panel debounce timer
        self._preview_timer = QTimer()
        self._preview_timer.setSingleShot(True)
        self._preview_timer.setInterval(500)
        self._preview_timer.timeout.connect(self._refresh_preview)
        self._preview_html_cache = None  # cached widget HTML template

        self._build_ui()
        self._load_lemsa_directory()
        self._load_lemsa_config()
        self._rebuild_lemsa_list()
        self._load_master()
        self._refresh_rigs()
        self._restore_ui_state()

    def _build_ui(self):
        # Menu bar
        menubar = self.menuBar()
        file_menu = menubar.addMenu("File")
        self._save_action = QAction("Save All", self)
        self._save_action.setShortcut(QKeySequence("Ctrl+S"))
        self._save_action.setEnabled(False)
        self._save_action.triggered.connect(self._save_all)
        file_menu.addAction(self._save_action)
        file_menu.addSeparator()
        quit_action = QAction("Quit", self)
        quit_action.setShortcut(QKeySequence("Ctrl+Q"))
        quit_action.triggered.connect(self.close)
        file_menu.addAction(quit_action)

        edit_menu = menubar.addMenu("Edit")
        self._undo_action = QAction("Undo", self)
        self._undo_action.setShortcut(QKeySequence("Ctrl+Z"))
        self._undo_action.triggered.connect(self._smart_undo)
        edit_menu.addAction(self._undo_action)
        self._redo_action = QAction("Redo", self)
        self._redo_action.setShortcut(QKeySequence("Ctrl+Shift+Z"))
        self._redo_action.triggered.connect(self._smart_redo)
        edit_menu.addAction(self._redo_action)
        edit_menu.addSeparator()
        self._cut_action = QAction("Cut", self)
        self._cut_action.setShortcut(QKeySequence("Ctrl+X"))
        self._cut_action.triggered.connect(self._smart_cut)
        edit_menu.addAction(self._cut_action)
        self._copy_action = QAction("Copy", self)
        self._copy_action.setShortcut(QKeySequence("Ctrl+C"))
        self._copy_action.triggered.connect(self._smart_copy)
        edit_menu.addAction(self._copy_action)
        self._paste_action = QAction("Paste", self)
        self._paste_action.setShortcut(QKeySequence("Ctrl+V"))
        self._paste_action.triggered.connect(self._smart_paste)
        edit_menu.addAction(self._paste_action)
        edit_menu.addSeparator()
        self._rename_action = QAction("Rename", self)
        self._rename_action.setShortcut(QKeySequence("Ctrl+R"))
        self._rename_action.triggered.connect(self._do_rename)
        edit_menu.addAction(self._rename_action)

        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)
        main_layout.setContentsMargins(4, 4, 4, 0)

        # Tabs
        self._tabs = QTabWidget()
        main_layout.addWidget(self._tabs)

        self._lemsa_tab = QWidget()
        self._tabs.addTab(self._lemsa_tab, "LEMSA Selection")
        self._build_lemsa_tab()

        self._master_tab = QWidget()
        self._tabs.addTab(self._master_tab, "Master List")
        self._build_master_tab()

        self._rig_tab = QWidget()
        self._tabs.addTab(self._rig_tab, "Rig Files")
        self._build_rig_tab()

        # Ctrl+1/2/3: quick tab navigation
        for i in range(self._tabs.count()):
            sc = QShortcut(QKeySequence(f"Ctrl+{i+1}"), self)
            sc.activated.connect(lambda idx=i: self._tabs.setCurrentIndex(idx))

        # Status bar
        self._status = self.statusBar()
        self._status.showMessage("Ready")

        # Global progress bar (in status bar area)
        self._progress_widget = QWidget()
        progress_layout = QHBoxLayout(self._progress_widget)
        progress_layout.setContentsMargins(0, 0, 0, 0)
        self._g_progress = QProgressBar()
        self._g_progress.setTextVisible(True)
        self._g_progress.setFormat("")
        self._g_progress.setMinimumWidth(300)
        self._g_progress.setFixedHeight(20)
        progress_layout.addWidget(self._g_progress)
        self._g_spinner = QLabel("")
        self._g_spinner.setFixedWidth(30)
        progress_layout.addWidget(self._g_spinner)
        self._status.addPermanentWidget(self._progress_widget)
        self._progress_widget.hide()
        self._spinner_frames = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
        self._spinner_idx = 0
        self._spinner_timer = None

        # Ctrl+F shortcut
        find_shortcut = QShortcut(QKeySequence("Ctrl+F"), self)
        find_shortcut.activated.connect(self._toggle_find_bar)

        # Ctrl+M: move selected to existing category
        move_shortcut = QShortcut(QKeySequence("Ctrl+M"), self)
        move_shortcut.activated.connect(self._do_move_to_category)

        # Ctrl+N: move selected to new category
        move_new_shortcut = QShortcut(QKeySequence("Ctrl+N"), self)
        move_new_shortcut.activated.connect(self._do_move_to_new_category)

    # -- LEMSA Equipment tab -------------------------------------------------

    def _build_lemsa_tab(self):
        layout = QVBoxLayout(self._lemsa_tab)
        layout.setContentsMargins(0, 0, 0, 0)
        self._lemsa_splitter = QSplitter(Qt.Orientation.Horizontal)
        layout.addWidget(self._lemsa_splitter)

        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(4, 4, 4, 4)

        # Search
        sf = QHBoxLayout()
        sf.addWidget(QLabel("Search:"))
        self._l_search = QLineEdit()
        self._l_search.textChanged.connect(lambda: self._rebuild_lemsa_list())
        self._l_search._paired_tree = '_l_tree'
        self._l_search.installEventFilter(self)
        sf.addWidget(self._l_search)
        clear_btn = QPushButton("✕")
        clear_btn.setFixedWidth(30)
        clear_btn.setStyleSheet("padding: 2px;")
        clear_btn.clicked.connect(lambda: self._l_search.setText(""))
        sf.addWidget(clear_btn)
        left_layout.addLayout(sf)

        # Filter + check button
        ff = QHBoxLayout()
        self._l_tracked_only = QCheckBox("Show tracked only")
        self._l_tracked_only.stateChanged.connect(lambda: self._rebuild_lemsa_list())
        ff.addWidget(self._l_tracked_only)
        check_btn = QPushButton("Check Tracked for Updates")
        check_btn.clicked.connect(lambda: self._check_lemsa_updates())
        ff.addWidget(check_btn)
        ff.addStretch()
        left_layout.addLayout(ff)

        # Download dir
        df = QHBoxLayout()
        df.addWidget(QLabel("Save PDFs to:"))
        self._l_dl_dir = QLineEdit()
        self._l_dl_dir.setPlaceholderText("Select a directory…")
        df.addWidget(self._l_dl_dir)
        dl_browse = QPushButton("Browse…")
        dl_browse.clicked.connect(self._browse_lemsa_dl_dir)
        df.addWidget(dl_browse)
        left_layout.addLayout(df)

        # Tree
        self._l_tree = QTreeWidget()
        self._l_tree.setHeaderHidden(True)
        self._l_tree.itemClicked.connect(self._on_lemsa_select)
        self._l_tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self._l_tree._paired_search = '_l_search'
        self._l_tree.installEventFilter(self)
        left_layout.addWidget(self._l_tree)

        self._lemsa_splitter.addWidget(left)

        # Right: detail
        right = QWidget()
        right_layout = QVBoxLayout(right)
        self._l_detail_title = QLabel("Select a LEMSA")
        self._l_detail_title.setStyleSheet("font-size: 14px; font-weight: bold;")
        right_layout.addWidget(self._l_detail_title)
        self._l_editor_area = QScrollArea()
        self._l_editor_area.setWidgetResizable(True)
        self._l_editor_widget = QWidget()
        self._l_editor_layout = QVBoxLayout(self._l_editor_widget)
        self._l_editor_area.setWidget(self._l_editor_widget)
        right_layout.addWidget(self._l_editor_area)
        self._lemsa_splitter.addWidget(right)
        self._lemsa_splitter.setSizes([400, 500])

    # -- Master List tab -----------------------------------------------------

    def _build_master_tab(self):
        layout = QVBoxLayout(self._master_tab)
        layout.setContentsMargins(0, 0, 0, 0)
        self._master_splitter = QSplitter(Qt.Orientation.Horizontal)
        layout.addWidget(self._master_splitter)

        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(4, 4, 4, 4)

        sf = QHBoxLayout()
        sf.addWidget(QLabel("Search:"))
        self._m_search = QLineEdit()
        self._m_search.textChanged.connect(lambda: self._rebuild_master_tree())
        self._m_search._paired_tree = '_m_tree'
        self._m_search.installEventFilter(self)
        sf.addWidget(self._m_search)
        clear_btn = QPushButton("✕")
        clear_btn.setFixedWidth(30)
        clear_btn.setStyleSheet("padding: 2px;")
        clear_btn.clicked.connect(lambda: self._m_search.setText(""))
        sf.addWidget(clear_btn)
        left_layout.addLayout(sf)

        self._m_tree = DragDropTree()
        self._m_tree.setIndentation(20)
        self._m_tree.setRootIsDecorated(True)
        self._m_tree.itemClicked.connect(self._on_master_select)
        self._m_tree.itemClicked.connect(lambda: setattr(self, '_last_focused_tree', 'master'))
        self._m_tree.focusGained.connect(lambda: setattr(self, '_last_focused_tree', 'master'))
        self._m_tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self._m_tree.customContextMenuRequested.connect(self._on_master_right_click)
        self._m_tree.itemsDropped.connect(self._on_master_drop)
        self._m_tree.itemRenamed.connect(self._on_master_renamed)
        self._m_tree._paired_search = '_m_search'
        self._m_tree.installEventFilter(self)
        left_layout.addWidget(self._m_tree)

        # Placeholder shown when no master list exists
        self._m_no_master = QWidget()
        no_master_layout = QVBoxLayout(self._m_no_master)
        no_master_layout.addStretch()
        create_btn = QPushButton("Create List from Rig Files")
        create_btn.setStyleSheet("padding: 12px 24px; font-size: 14px;")
        create_btn.clicked.connect(self._create_master_from_rigs)
        no_master_layout.addWidget(create_btn, alignment=Qt.AlignmentFlag.AlignCenter)
        no_master_layout.addStretch()
        self._m_no_master.hide()
        left_layout.addWidget(self._m_no_master)

        self._master_splitter.addWidget(left)

        # Right side: two panels with maximize toggles
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(4, 4, 4, 4)

        self._m_right_splitter = QSplitter(Qt.Orientation.Vertical)

        # Top panel: Editor
        editor_panel = QWidget()
        ep_layout = QVBoxLayout(editor_panel)
        ep_layout.setContentsMargins(0, 0, 0, 0)
        ep_header = QHBoxLayout()
        self._m_detail_title = QLabel("Select an item")
        self._m_detail_title.setStyleSheet("font-size: 14px; font-weight: bold;")
        ep_header.addWidget(self._m_detail_title)
        ep_header.addStretch()
        self._m_editor_max_btn = QPushButton("⤢")
        self._m_editor_max_btn.setFixedSize(24, 24)
        self._m_editor_max_btn.setStyleSheet("padding: 2px;")
        self._m_editor_max_btn.setToolTip("Maximize/restore editor panel")
        self._m_editor_max_btn.clicked.connect(lambda: self._toggle_master_panel("editor"))
        ep_header.addWidget(self._m_editor_max_btn)
        ep_layout.addLayout(ep_header)
        self._m_editor_area = QScrollArea()
        self._m_editor_area.setWidgetResizable(True)
        self._m_editor_widget = QWidget()
        self._m_editor_layout = QVBoxLayout(self._m_editor_widget)
        self._m_editor_area.setWidget(self._m_editor_widget)
        ep_layout.addWidget(self._m_editor_area)
        self._m_right_splitter.addWidget(editor_panel)

        # Bottom panel: LEMSA List
        lemsa_panel = QWidget()
        lp_layout = QVBoxLayout(lemsa_panel)
        lp_layout.setContentsMargins(0, 0, 0, 0)

        # Header with title, buttons, and maximize
        lp_header = QHBoxLayout()
        self._m_lemsa_title = QLabel("LEMSA List")
        self._m_lemsa_title.setStyleSheet("font-size: 14px; font-weight: bold;")
        lp_header.addWidget(self._m_lemsa_title)
        lp_header.addStretch()
        compile_btn = QPushButton("Compile New")
        compile_btn.setToolTip("Check for updates and extract items from LEMSA PDFs")
        compile_btn.clicked.connect(self._compare_with_lemsas)
        lp_header.addWidget(compile_btn)
        existing_btn = QPushButton("Use Existing")
        existing_btn.setToolTip("Load previously compiled LEMSA item list")
        existing_btn.clicked.connect(self._use_existing_compiled)
        lp_header.addWidget(existing_btn)
        apply_btn = QPushButton("Apply Changes")
        apply_btn.setToolTip("Apply table edits to the master list")
        apply_btn.clicked.connect(self._apply_changes_to_master)
        lp_header.addWidget(apply_btn)
        self._m_lemsa_max_btn = QPushButton("⤢")
        self._m_lemsa_max_btn.setFixedSize(24, 24)
        self._m_lemsa_max_btn.setStyleSheet("padding: 2px;")
        self._m_lemsa_max_btn.setToolTip("Maximize/restore LEMSA list panel")
        self._m_lemsa_max_btn.clicked.connect(lambda: self._toggle_master_panel("lemsa"))
        lp_header.addWidget(self._m_lemsa_max_btn)
        lp_layout.addLayout(lp_header)

        # Tab widget: All Items | Not in LEMSA
        self._m_lemsa_tabs = QTabWidget()

        # Table styling now handled by global Catppuccin stylesheet

        # All Items table
        all_container = QWidget()
        all_container_layout = QVBoxLayout(all_container)
        all_container_layout.setContentsMargins(0, 0, 0, 0)

        self._m_all_table = ManagedTableWidget()
        self._m_all_table._suppress_popup = False
        self._m_all_table.setColumnCount(8)
        # Column order: Type | Agency | Item Name | LEMSA Qty | Master Name | Master Qty | Category | Status
        self._m_all_table.setHorizontalHeaderLabels(
            ["Type", "Agency", "Item Name", "LEMSA Qty", "Master Name",
             "Master Qty", "Category", "Status"])
        hdr = self._m_all_table.horizontalHeader()
        hdr.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        hdr.setCascadingSectionResizes(False)
        hdr.setStretchLastSection(True)
        self._m_all_table.setColumnWidth(0, 70)
        self._m_all_table.setColumnWidth(1, 80)
        self._m_all_table.setColumnWidth(2, 180)
        self._m_all_table.setColumnWidth(3, 70)
        self._m_all_table.setColumnWidth(4, 150)
        self._m_all_table.setColumnWidth(5, 70)
        self._m_all_table.setColumnWidth(6, 100)
        self._m_all_table.setColumnWidth(7, 110)
        self._m_all_table.setSortingEnabled(True)
        self._m_all_table.setAlternatingRowColors(False)
        self._m_all_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self._m_all_table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self._m_all_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self._m_all_table.setMouseTracking(True)
        self._m_all_table.doubleClicked.connect(self._on_all_table_double_click)
        self._m_all_table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self._m_all_table.customContextMenuRequested.connect(self._on_all_table_right_click)
        self._m_all_table.viewport().installEventFilter(self)
        self._m_all_table.installEventFilter(self)
        self._m_all_table.editorClosed.connect(self._on_editor_closed)

        # Readonly columns: 0=Type, 1=Agency, 2=Item Name, 3=LEMSA Qty
        self._readonly_cols = {0, 1, 2, 3}

        # ComboBox delegate for Status column (col 7)
        desig_delegate = DesignationDelegate(["", "New", "Optional", "Name Difference", "Exclude"], self._m_all_table)
        self._m_all_table.setItemDelegateForColumn(7, desig_delegate)

        # Searchable delegate for Master Name column (col 4)
        master_name_delegate = CategoryDelegate(self._get_master_item_names, self._m_all_table)
        self._m_all_table.setItemDelegateForColumn(4, master_name_delegate)

        # Searchable category delegate for Category column (col 6)
        cat_delegate = CategoryDelegate(self._get_master_categories, self._m_all_table)
        self._m_all_table.setItemDelegateForColumn(6, cat_delegate)

        all_container_layout.addWidget(self._m_all_table)
        self._m_lemsa_tabs.addTab(all_container, "All Items")

        # Not in LEMSA table
        self._m_missing_table = QTableWidget()
        self._m_missing_table.setColumnCount(2)
        self._m_missing_table.setHorizontalHeaderLabels(["Item Name", "Category"])
        mhdr = self._m_missing_table.horizontalHeader()
        mhdr.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        mhdr.setCascadingSectionResizes(False)
        mhdr.setStretchLastSection(True)
        self._m_missing_table.setColumnWidth(0, 300)
        self._m_missing_table.setSortingEnabled(True)
        self._m_missing_table.setAlternatingRowColors(True)
        self._m_missing_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self._m_missing_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self._m_lemsa_tabs.addTab(self._m_missing_table, "Not in LEMSA")

        lp_layout.addWidget(self._m_lemsa_tabs)

        # Find bar (hidden by default)
        self._m_find_bar = QWidget()
        find_layout = QHBoxLayout(self._m_find_bar)
        find_layout.setContentsMargins(4, 2, 4, 2)
        find_layout.addWidget(QLabel("Find:"))
        self._m_find_edit = QLineEdit()
        self._m_find_edit.setPlaceholderText("Search items…")
        self._m_find_edit.textChanged.connect(self._filter_lemsa_tables)
        find_layout.addWidget(self._m_find_edit)
        find_close = QPushButton("✕")
        find_close.setFixedWidth(24)
        find_close.setStyleSheet("padding: 2px;")
        find_close.clicked.connect(self._toggle_find_bar)
        find_layout.addWidget(find_close)
        self._m_find_bar.hide()
        lp_layout.addWidget(self._m_find_bar)

        # Corner toolbar: find + edit-direction + edit-scope toggles
        corner_widget = QWidget()
        corner_layout = QHBoxLayout(corner_widget)
        corner_layout.setContentsMargins(0, 0, 4, 0)
        corner_layout.setSpacing(2)

        find_btn = QPushButton("🔍")
        find_btn.setFixedSize(28, 22)
        find_btn.setStyleSheet("padding: 2px;")
        find_btn.setToolTip("Find (Ctrl+F)")
        find_btn.clicked.connect(self._toggle_find_bar)
        corner_layout.addWidget(find_btn)

        self._edit_dir_btn = QPushButton("→")
        self._edit_dir_btn.setFixedSize(28, 22)
        self._edit_dir_btn.setStyleSheet("padding: 2px;")
        self._edit_dir_btn.setToolTip("Edit direction: across (click to switch to down)")
        self._edit_dir_btn.clicked.connect(self._toggle_edit_dir)
        corner_layout.addWidget(self._edit_dir_btn)

        self._edit_scope_btn = QPushButton("∅")
        self._edit_scope_btn.setFixedSize(28, 22)
        self._edit_scope_btn.setStyleSheet("padding: 2px;")
        self._edit_scope_btn.setToolTip("Edit scope: empty cells only (click to switch to all cells)")
        self._edit_scope_btn.clicked.connect(self._toggle_edit_scope)
        corner_layout.addWidget(self._edit_scope_btn)

        self._m_lemsa_tabs.setCornerWidget(corner_widget)

        self._m_right_splitter.addWidget(lemsa_panel)

        self._m_right_splitter.setSizes([300, 300])
        self._m_maximized_panel = None  # tracks which panel is maximized
        self._m_editor_panel = editor_panel
        self._m_lemsa_panel = lemsa_panel

        right_layout.addWidget(self._m_right_splitter)
        self._master_splitter.addWidget(right)
        self._master_splitter.setSizes([400, 500])

    # -- Rig Files tab -------------------------------------------------------

    def _build_rig_tab(self):
        layout = QVBoxLayout(self._rig_tab)
        layout.setContentsMargins(4, 4, 4, 0)

        # Row 1: Dir + Rig selection
        dir_row = QHBoxLayout()
        dir_row.addWidget(QLabel("Dir:"))
        self._dir_edit = QLineEdit(self.checklists_dir)
        self._dir_edit.setMinimumWidth(250)
        dir_row.addWidget(self._dir_edit)
        browse_btn = QPushButton("Browse…")
        browse_btn.clicked.connect(self._browse_dir)
        dir_row.addWidget(browse_btn)

        sep1 = QFrame(); sep1.setFrameShape(QFrame.Shape.VLine); dir_row.addWidget(sep1)

        dir_row.addWidget(QLabel("Rig:"))
        self._rig_combo = QComboBox()
        self._rig_combo.setMinimumWidth(80)
        self._rig_combo.currentTextChanged.connect(self._on_rig_selected)
        dir_row.addWidget(self._rig_combo)
        dup_btn = QPushButton("Duplicate Rig…")
        dup_btn.clicked.connect(self._duplicate_rig)
        dir_row.addWidget(dup_btn)
        dir_row.addStretch()
        layout.addLayout(dir_row)

        # Row 2: File selection
        file_row = QHBoxLayout()
        file_row.addWidget(QLabel("File:"))
        self._file_combo = QComboBox()
        self._file_combo.setMinimumWidth(180)
        self._file_combo.currentTextChanged.connect(self._on_file_selected)
        file_row.addWidget(self._file_combo)
        file_row.addStretch()
        layout.addLayout(file_row)

        self._rig_splitter = QSplitter(Qt.Orientation.Horizontal)
        layout.addWidget(self._rig_splitter)

        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(4, 4, 4, 4)

        sf = QHBoxLayout()
        sf.addWidget(QLabel("Search:"))
        self._r_search = QLineEdit()
        self._r_search.textChanged.connect(lambda: self._rebuild_rig_tree())
        self._r_search._paired_tree = '_r_tree'
        self._r_search.installEventFilter(self)
        sf.addWidget(self._r_search)
        clear_btn = QPushButton("✕")
        clear_btn.setFixedWidth(30)
        clear_btn.setStyleSheet("padding: 2px;")
        clear_btn.clicked.connect(lambda: self._r_search.setText(""))
        sf.addWidget(clear_btn)
        left_layout.addLayout(sf)

        self._r_tree = DragDropTree()
        self._r_tree.setIndentation(20)
        self._r_tree.setRootIsDecorated(True)
        self._r_tree.itemClicked.connect(self._on_rig_tree_select)
        self._r_tree.itemClicked.connect(lambda: setattr(self, '_last_focused_tree', 'rig'))
        self._r_tree.focusGained.connect(lambda: setattr(self, '_last_focused_tree', 'rig'))
        self._r_tree.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self._r_tree.customContextMenuRequested.connect(self._on_rig_right_click)
        self._r_tree.itemsDropped.connect(self._on_rig_drop)
        self._r_tree.itemRenamed.connect(self._on_rig_renamed)
        self._r_tree._paired_search = '_r_search'
        self._r_tree.installEventFilter(self)
        left_layout.addWidget(self._r_tree)
        self._rig_splitter.addWidget(left)

        # Right side: two panels with maximize toggles (mirrors master list tab)
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(4, 4, 4, 4)

        self._r_right_splitter = QSplitter(Qt.Orientation.Vertical)

        # Top panel: Editor
        editor_panel = QWidget()
        ep_layout = QVBoxLayout(editor_panel)
        ep_layout.setContentsMargins(0, 0, 0, 0)
        ep_header = QHBoxLayout()
        self._r_detail_title = QLabel("Select an item")
        self._r_detail_title.setStyleSheet("font-size: 14px; font-weight: bold;")
        ep_header.addWidget(self._r_detail_title)
        ep_header.addStretch()
        self._r_editor_max_btn = QPushButton("⤢")
        self._r_editor_max_btn.setFixedSize(24, 24)
        self._r_editor_max_btn.setStyleSheet("padding: 2px;")
        self._r_editor_max_btn.setToolTip("Maximize/restore editor panel")
        self._r_editor_max_btn.clicked.connect(lambda: self._toggle_rig_panel("editor"))
        ep_header.addWidget(self._r_editor_max_btn)
        ep_layout.addLayout(ep_header)
        self._r_editor_area = QScrollArea()
        self._r_editor_area.setWidgetResizable(True)
        self._r_editor_widget = QWidget()
        self._r_editor_layout = QVBoxLayout(self._r_editor_widget)
        self._r_editor_area.setWidget(self._r_editor_widget)
        ep_layout.addWidget(self._r_editor_area)
        self._r_right_splitter.addWidget(editor_panel)

        # Bottom panel: Preview
        preview_panel = QWidget()
        pp_layout = QVBoxLayout(preview_panel)
        pp_layout.setContentsMargins(0, 0, 0, 0)
        pp_header = QHBoxLayout()
        preview_label = QLabel("Preview")
        preview_label.setStyleSheet("font-size: 14px; font-weight: bold;")
        pp_header.addWidget(preview_label)
        pp_header.addStretch()
        sim_btn = QPushButton("Open in Browser")
        sim_btn.setToolTip("Open preview in external browser")
        sim_btn.clicked.connect(self._simulate)
        pp_header.addWidget(sim_btn)
        if HAS_WEBENGINE:
            self._preview_refresh_btn = QPushButton("↻")
            self._preview_refresh_btn.setFixedSize(24, 24)
            self._preview_refresh_btn.setStyleSheet("padding: 2px;")
            self._preview_refresh_btn.setToolTip("Refresh preview")
            self._preview_refresh_btn.clicked.connect(self._refresh_preview)
            pp_header.addWidget(self._preview_refresh_btn)
        self._r_preview_max_btn = QPushButton("⤢")
        self._r_preview_max_btn.setFixedSize(24, 24)
        self._r_preview_max_btn.setStyleSheet("padding: 2px;")
        self._r_preview_max_btn.setToolTip("Maximize/restore preview panel")
        self._r_preview_max_btn.clicked.connect(lambda: self._toggle_rig_panel("preview"))
        pp_header.addWidget(self._r_preview_max_btn)
        pp_layout.addLayout(pp_header)

        if HAS_WEBENGINE:
            self._preview_web = QWebEngineView()
            pp_layout.addWidget(self._preview_web)
        else:
            self._preview_web = None
            no_preview = QLabel("Install PyQt6-WebEngine for inline preview")
            no_preview.setAlignment(Qt.AlignmentFlag.AlignCenter)
            no_preview.setStyleSheet("color: #6c7086; font-style: italic; padding: 20px;")
            pp_layout.addWidget(no_preview)

        self._r_right_splitter.addWidget(preview_panel)
        self._r_right_splitter.setSizes([300, 300])
        self._r_maximized_panel = None
        self._r_editor_panel = editor_panel
        self._r_preview_panel = preview_panel

        right_layout.addWidget(self._r_right_splitter)
        self._rig_splitter.addWidget(right)
        self._rig_splitter.setSizes([400, 500])

    # -- Helpers -------------------------------------------------------------

    def _clear_layout(self, layout):
        """Remove all widgets from a layout."""
        while layout.count():
            child = layout.takeAt(0)
            if child.widget():
                child.widget().deleteLater()
            elif child.layout():
                self._clear_layout(child.layout())

    def _clear_editor(self, title_label, editor_widget, editor_layout, title="Select an item"):
        title_label.setText(title)
        self._clear_layout(editor_layout)

    def _get_master_categories(self):
        """Return sorted list of category names from master list + table edits."""
        cats = set()
        if self.master_list:
            cats.update(c.name for c in self.master_list.categories)
        # Also include any categories already entered in the table (col 6)
        for row in range(self._m_all_table.rowCount()):
            cell = self._m_all_table.item(row, 6)
            if cell:
                val = cell.text().strip()
                if val:
                    cats.add(val)
        return sorted(cats, key=str.lower)

    def _get_master_item_names(self):
        """Return sorted list of all item names from master list + table edits."""
        names = set()
        if self.master_list:
            names.update(self.master_list.all_item_names())
        # Also include any master names already entered in the table (col 4)
        for row in range(self._m_all_table.rowCount()):
            cell = self._m_all_table.item(row, 4)
            if cell:
                val = cell.text().strip()
                if val:
                    names.add(val)
        return sorted(names, key=str.lower)

    def _build_source_acronym_map(self):
        """Build a map from PDF-derived source strings to LEMSA acronyms.

        PDF filenames are generated from LEMSA names via _save_lemsa_pdf:
          name → strip non-word/space/hyphen → replace spaces with _ → .pdf
        When reading back, source = filename.replace('.pdf','').replace('_',' ')

        This method reverses that to match source strings to config acronyms.
        """
        source_map = {}  # source_string → {"acronym": str, "full_name": str}
        for lemsa in self.lemsa_data:
            name = lemsa["name"]
            conf = self._get_lemsa_conf(name)
            acronym = conf.get("acronym", "")
            if not acronym:
                continue
            # Reproduce the same sanitization as _save_lemsa_pdf
            safe_name = re.sub(r'[^\w\s\-]', '', name).strip().replace(' ', '_')
            source_string = safe_name.replace('_', ' ')
            source_map[source_string] = {"acronym": acronym, "full_name": name}
        return source_map

    # -- UI state persistence ------------------------------------------------

    def _save_ui_state(self):
        """Save splitter sizes and panel maximize state."""
        state = {
            "lemsa_splitter": self._lemsa_splitter.sizes(),
            "master_splitter": self._master_splitter.sizes(),
            "master_right_splitter": self._m_right_splitter.sizes(),
            "rig_splitter": self._rig_splitter.sizes(),
            "rig_right_splitter": self._r_right_splitter.sizes(),
            "maximized_panel": self._m_maximized_panel,
            "rig_maximized_panel": self._r_maximized_panel,
            "window_geometry": [self.x(), self.y(), self.width(), self.height()],
        }
        try:
            os.makedirs(os.path.dirname(self._ui_state_path), exist_ok=True)
            with open(self._ui_state_path, "w", encoding="utf-8") as f:
                json.dump(state, f, indent=2)
        except Exception:
            pass

    def _restore_ui_state(self):
        """Restore splitter sizes and panel maximize state from saved config."""
        if not os.path.isfile(self._ui_state_path):
            return
        try:
            with open(self._ui_state_path, "r", encoding="utf-8") as f:
                state = json.load(f)
        except Exception:
            return

        if "window_geometry" in state:
            g = state["window_geometry"]
            if len(g) == 4:
                self.setGeometry(g[0], g[1], g[2], g[3])

        if "lemsa_splitter" in state:
            self._lemsa_splitter.setSizes(state["lemsa_splitter"])
        if "master_splitter" in state:
            self._master_splitter.setSizes(state["master_splitter"])
        if "master_right_splitter" in state:
            self._m_right_splitter.setSizes(state["master_right_splitter"])
        if "rig_splitter" in state:
            saved = state["rig_splitter"]
            if len(saved) == self._rig_splitter.count():
                self._rig_splitter.setSizes(saved)
            # else: panel count changed (e.g. preview added), keep defaults

        saved_max = state.get("maximized_panel")
        if saved_max in ("editor", "lemsa"):
            self._m_maximized_panel = None  # reset so toggle works
            self._toggle_master_panel(saved_max)

        if "rig_right_splitter" in state:
            self._r_right_splitter.setSizes(state["rig_right_splitter"])
        saved_rig_max = state.get("rig_maximized_panel")
        if saved_rig_max in ("editor", "preview"):
            self._r_maximized_panel = None  # reset so toggle works
            self._toggle_rig_panel(saved_rig_max)

    def _toggle_master_panel(self, which):
        """Toggle maximize/restore for editor or lemsa panel."""
        if self._m_maximized_panel == which:
            # Restore
            self._m_editor_panel.show()
            self._m_lemsa_panel.show()
            self._m_right_splitter.setSizes([300, 300])
            self._m_maximized_panel = None
            self._m_editor_max_btn.setText("⤢")
            self._m_lemsa_max_btn.setText("⤢")
        else:
            # Maximize the requested panel
            if which == "editor":
                self._m_lemsa_panel.hide()
                self._m_editor_panel.show()
                self._m_editor_max_btn.setText("⤡")
            else:
                self._m_editor_panel.hide()
                self._m_lemsa_panel.show()
                self._m_lemsa_max_btn.setText("⤡")
            self._m_maximized_panel = which

    def _toggle_rig_panel(self, which):
        """Toggle maximize/restore for editor or preview panel in rig tab."""
        if self._r_maximized_panel == which:
            # Restore
            self._r_editor_panel.show()
            self._r_preview_panel.show()
            self._r_right_splitter.setSizes([300, 300])
            self._r_maximized_panel = None
            self._r_editor_max_btn.setText("⤢")
            self._r_preview_max_btn.setText("⤢")
        else:
            # Maximize the requested panel
            if which == "editor":
                self._r_preview_panel.hide()
                self._r_editor_panel.show()
                self._r_editor_max_btn.setText("⤡")
            else:
                self._r_editor_panel.hide()
                self._r_preview_panel.show()
                self._r_preview_max_btn.setText("⤡")
            self._r_maximized_panel = which

    def _show_progress(self, maximum=0, text=""):
        """Show the global progress bar with optional text overlay."""
        self._g_progress.setMaximum(maximum)
        self._g_progress.setValue(0)
        self._g_progress.setFormat(text)
        self._spinner_idx = 0
        self._progress_widget.show()
        self._status.clearMessage()
        self._start_spinner()

    def _update_progress(self, value, text=""):
        self._g_progress.setValue(value)
        if text:
            self._g_progress.setFormat(text)

    def _hide_progress(self):
        self._stop_spinner()
        self._progress_widget.hide()
        self._g_progress.setValue(0)
        self._g_progress.setFormat("")

    def _start_spinner(self):
        if self._spinner_timer is None:
            from PyQt6.QtCore import QTimer
            self._spinner_timer = QTimer(self)
            self._spinner_timer.timeout.connect(self._tick_spinner)
        self._spinner_timer.start(100)

    def _stop_spinner(self):
        if self._spinner_timer:
            self._spinner_timer.stop()
        self._g_spinner.setText("")

    def _tick_spinner(self):
        self._spinner_idx = (self._spinner_idx + 1) % len(self._spinner_frames)
        self._g_spinner.setText(self._spinner_frames[self._spinner_idx])

    # -- Dir / rig / file management -----------------------------------------

    def _browse_dir(self):
        d = QFileDialog.getExistingDirectory(self, "Select Checklists Directory", self._dir_edit.text())
        if d:
            self._dir_edit.setText(d)
            self.checklists_dir = d
            self.master_list_path = os.path.join(d, "master_list.json")
            self._load_master()
            self._refresh_rigs()

    def _refresh_rigs(self):
        d = self.checklists_dir
        self._rig_combo.blockSignals(True)
        self._rig_combo.clear()
        if not os.path.isdir(d):
            self._rig_combo.blockSignals(False)
            return
        rigs = sorted([n for n in os.listdir(d) if os.path.isdir(os.path.join(d, n))], key=str.lower)
        self._rig_combo.addItems(rigs)
        self._rig_combo.blockSignals(False)
        if rigs:
            self._on_rig_selected()

    def _on_rig_selected(self):
        rig = self._rig_combo.currentText()
        if not rig:
            return
        self.current_rig = rig
        rig_dir = os.path.join(self.checklists_dir, rig)
        json_files = sorted([f for f in os.listdir(rig_dir) if f.endswith(".json")], key=str.lower)
        self._file_combo.blockSignals(True)
        self._file_combo.clear()
        self._file_combo.addItems(json_files)
        self._file_combo.blockSignals(False)
        self.rig_files = []
        for fn in json_files:
            try:
                self.rig_files.append(InventoryFile.from_file(os.path.join(rig_dir, fn)))
            except Exception:
                pass
        if json_files:
            self._on_file_selected()
        else:
            self.current_file = None
            self._rebuild_rig_tree()

    def _on_file_selected(self):
        fname = self._file_combo.currentText()
        if not fname or not self.current_rig:
            return
        path = os.path.join(self.checklists_dir, self.current_rig, fname)
        try:
            self.current_file = InventoryFile.from_file(path)
        except Exception as e:
            self.current_file = None
            self._status.showMessage(f"Parse error: {e}")
        # Reset undo stacks for new file
        self._rig_undo_stack.clear()
        self._rig_redo_stack.clear()
        self._rig_last_snap = json.dumps(self.current_file.to_json_data()) if self.current_file else None
        self._rebuild_rig_tree()
        self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        if self.current_file:
            total = sum(len(c.items) for a in self.current_file.areas for c in a.categories)
            flag = ""
            if self.master_list:
                mn = self.master_list.all_item_names()
                nim = sum(1 for a in self.current_file.areas for c in a.categories
                          for i in c.items if i.name not in mn)
                if nim:
                    flag = f", {nim} not in master"
            self._status.showMessage(f"{fname} — {total} items{flag}")
        self._refresh_preview()

    def _duplicate_rig(self):
        if not self.current_rig:
            return
        new_name, ok = QInputDialog.getText(self, "Duplicate Rig",
                                             f"Duplicating '{self.current_rig}'.\nNew rig number:")
        if not ok or not new_name.strip():
            return
        new_name = new_name.strip()
        src = os.path.join(self.checklists_dir, self.current_rig)
        dst = os.path.join(self.checklists_dir, new_name)
        if os.path.exists(dst):
            self._status.showMessage(f"Rig '{new_name}' already exists.")
            return
        try:
            shutil.copytree(src, dst)
        except Exception as e:
            self._status.showMessage(f"Error: {e}")
            return
        self._refresh_rigs()
        idx = self._rig_combo.findText(new_name)
        if idx >= 0:
            self._rig_combo.setCurrentIndex(idx)
        self._status.showMessage(f"Duplicated {self.current_rig} → {new_name}")

    def _load_master(self):
        if os.path.isfile(self.master_list_path):
            try:
                self.master_list = MasterList.from_file(self.master_list_path)
                self._rebuild_master_tree()
                n = sum(len(c.items) for c in self.master_list.categories)
                self._status.showMessage(f"Master list loaded: {n} items in {len(self.master_list.categories)} categories")
            except Exception as e:
                self.master_list = None
                self._status.showMessage(f"Master list error: {e}")
        else:
            self.master_list = None
            self._status.showMessage("No master_list.json found")
        # Reset master undo stacks
        self._master_undo_stack.clear()
        self._master_redo_stack.clear()
        self._master_last_snap = json.dumps(self.master_list.to_json_data()) if self.master_list else None
        self._update_master_visibility()

    def _update_master_visibility(self):
        """Show tree or 'Create' button depending on whether master list exists."""
        has_master = self.master_list is not None and any(
            c.items for c in self.master_list.categories
        ) if self.master_list else False
        self._m_tree.setVisible(has_master)
        self._m_no_master.setVisible(not has_master)

    def _create_master_from_rigs(self):
        """Show a rig selection dialog, then create a master list from
        the selected rigs' checklist files."""
        d = self.checklists_dir
        if not os.path.isdir(d):
            self._status.showMessage("Checklists directory not found.")
            return

        # Discover all rigs and their JSON files
        rig_info = {}  # rig_name -> [json_filenames]
        for name in sorted(os.listdir(d), key=str.lower):
            rig_dir = os.path.join(d, name)
            if not os.path.isdir(rig_dir):
                continue
            json_files = sorted([f for f in os.listdir(rig_dir) if f.endswith(".json")], key=str.lower)
            if json_files:
                rig_info[name] = json_files

        if not rig_info:
            self._status.showMessage("No rigs with JSON files found.")
            return

        # Build selection dialog
        dlg = QDialog(self)
        dlg.setWindowTitle("Select Rigs for Master List")
        dlg.setMinimumWidth(400)
        layout = QVBoxLayout(dlg)
        layout.addWidget(QLabel("Select which rigs to include:"))

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll_widget = QWidget()
        scroll_layout = QVBoxLayout(scroll_widget)

        checkboxes = {}  # rig_name -> QCheckBox
        for rig_name, files in rig_info.items():
            file_list = ", ".join(files)
            cb = QCheckBox(f"{rig_name}  ({len(files)} files: {file_list})")
            cb.setChecked(True)
            scroll_layout.addWidget(cb)
            checkboxes[rig_name] = cb

        scroll_layout.addStretch()
        scroll.setWidget(scroll_widget)
        layout.addWidget(scroll)

        # Select all / none
        btn_row = QHBoxLayout()
        select_all = QPushButton("Select All")
        select_all.clicked.connect(lambda: [cb.setChecked(True) for cb in checkboxes.values()])
        btn_row.addWidget(select_all)
        select_none = QPushButton("Select None")
        select_none.clicked.connect(lambda: [cb.setChecked(False) for cb in checkboxes.values()])
        btn_row.addWidget(select_none)
        btn_row.addStretch()
        layout.addLayout(btn_row)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok |
                                   QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(dlg.accept)
        buttons.rejected.connect(dlg.reject)
        layout.addWidget(buttons)

        if dlg.exec() != QDialog.DialogCode.Accepted:
            return

        selected_rigs = [name for name, cb in checkboxes.items() if cb.isChecked()]
        if not selected_rigs:
            self._status.showMessage("No rigs selected.")
            return

        # Load inventory files from selected rigs
        rig_files = []
        for rig_name in selected_rigs:
            rig_dir = os.path.join(d, rig_name)
            for fn in rig_info[rig_name]:
                try:
                    rig_files.append(InventoryFile.from_file(os.path.join(rig_dir, fn)))
                except Exception:
                    pass

        if not rig_files:
            self._status.showMessage("No items found in selected rigs.")
            return

        # Collect all items: name_lower -> (name, max_qty, group_or_None)
        items = {}
        for rf in rig_files:
            for area in rf.areas:
                for cat in area.categories:
                    for item in cat.items:
                        key = item.name.lower()
                        if key in items:
                            existing_name, existing_qty, existing_group = items[key]
                            items[key] = (existing_name, max(existing_qty, item.qty),
                                          item.group or existing_group)
                        else:
                            items[key] = (item.name, item.qty, item.group)

        # Create master list with single Uncategorized category
        self.master_list = MasterList(self.master_list_path)
        uncat = MasterCategory("Uncategorized")
        for name, qty, group in sorted(items.values(), key=lambda x: x[0].lower()):
            uncat.items.append(MasterItem(name, qty, group))
        self.master_list.categories.append(uncat)
        n_grouped = sum(1 for it in uncat.items if it.group)
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()
        self._status.showMessage(
            f"Created master list with {len(uncat.items)} items "
            f"({n_grouped} grouped) from {len(selected_rigs)} rig(s)")

    # -- LEMSA directory -------------------------------------------------------

    def _load_lemsa_directory(self):
        """Load agency list from external JSON, falling back to built-in default."""
        if os.path.isfile(self.lemsa_directory_path):
            try:
                with open(self.lemsa_directory_path, "r", encoding="utf-8") as f:
                    self.lemsa_data = json.load(f)
                return
            except Exception:
                pass
        # Fall back to built-in default and write it out
        self.lemsa_data = list(_LEMSA_DATA_DEFAULT)
        self._save_lemsa_directory()

    def _save_lemsa_directory(self):
        """Persist the agency list to data/lemsa_directory.json."""
        try:
            os.makedirs(os.path.dirname(self.lemsa_directory_path), exist_ok=True)
            with open(self.lemsa_directory_path, "w", encoding="utf-8") as f:
                json.dump(self.lemsa_data, f, indent=2, ensure_ascii=False)
                f.write("\n")
        except Exception as e:
            self._status.showMessage(f"Failed to save LEMSA directory: {e}")

    # -- LEMSA config --------------------------------------------------------

    def _load_lemsa_config(self):
        if os.path.isfile(self.lemsa_config_path):
            try:
                with open(self.lemsa_config_path, "r", encoding="utf-8") as f:
                    self.lemsa_config = json.load(f)
            except Exception:
                self.lemsa_config = {}
        else:
            self.lemsa_config = {}
        if hasattr(self, '_l_dl_dir'):
            self._l_dl_dir.setText(self.lemsa_config.get("_download_dir", ""))

    def _save_lemsa_config(self):
        os.makedirs(os.path.dirname(self.lemsa_config_path), exist_ok=True)
        with open(self.lemsa_config_path, "w", encoding="utf-8") as f:
            json.dump(self.lemsa_config, f, indent=2)

    def _get_lemsa_conf(self, name):
        if name not in self.lemsa_config:
            self.lemsa_config[name] = {
                "tracked": False, "page_url": "", "link_text": "",
                "last_hash": "", "last_checked": "", "resolved_url": "",
                "acronym": ""
            }
        conf = self.lemsa_config[name]
        if "equip_url" in conf and "page_url" not in conf:
            conf["page_url"] = conf.pop("equip_url")
        elif "equip_url" in conf:
            conf.pop("equip_url")
        if "acronym" not in conf:
            conf["acronym"] = ""
        return conf

    def _browse_lemsa_dl_dir(self):
        d = QFileDialog.getExistingDirectory(self, "Save PDFs to", self._l_dl_dir.text() or self.base_dir)
        if d:
            self._l_dl_dir.setText(d)
            self.lemsa_config["_download_dir"] = d
            self._save_lemsa_config()

    def _get_lemsa_dl_dir(self):
        d = self._l_dl_dir.text().strip()
        return d if d and os.path.isdir(d) else None

    def _save_lemsa_pdf(self, name, doc_data):
        dl_dir = self._get_lemsa_dl_dir()
        if not dl_dir:
            return None
        safe_name = re.sub(r'[^\w\s\-]', '', name).strip().replace(' ', '_')
        filepath = os.path.join(dl_dir, f"{safe_name}.pdf")
        with open(filepath, "wb") as f:
            f.write(doc_data)
        return filepath

    def _get_compiled_list_path(self):
        d = self._get_lemsa_dl_dir()
        if d:
            return os.path.join(d, "lemsa_compiled_items.json")
        return None

    def _save_compiled_list(self, all_lemsa):
        path = self._get_compiled_list_path()
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            json.dump(all_lemsa, f, indent=2)

    def _load_compiled_list(self):
        path = self._get_compiled_list_path()
        if path and os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return None

    # -- Table edits persistence ---------------------------------------------

    def _get_table_edits_path(self):
        return os.path.join(self.repo_root, "reference", "lemsa_table_edits.json")

    def _load_table_edits(self):
        path = self._get_table_edits_path()
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def _save_table_edits(self, edits):
        path = self._get_table_edits_path()
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(edits, f, indent=2)
        except Exception:
            pass

    def _save_row_edit(self, row):
        """Persist the editable columns of a single row to the edits file."""
        name_item = self._m_all_table.item(row, 2)  # Item Name
        if not name_item:
            return
        key = name_item.text().strip().lower()
        if not key:
            return
        edits = self._load_table_edits()
        master_name = (self._m_all_table.item(row, 4).text().strip()
                       if self._m_all_table.item(row, 4) else "")
        status = (self._m_all_table.item(row, 7).text().strip()
                  if self._m_all_table.item(row, 7) else "")
        edits[key] = {
            "master_name": master_name,
            "master_qty": (self._m_all_table.item(row, 5).text().strip()
                           if self._m_all_table.item(row, 5) else ""),
            "category": (self._m_all_table.item(row, 6).text().strip()
                         if self._m_all_table.item(row, 6) else ""),
            "status": status,
        }
        self._save_table_edits(edits)

        # Update aliases: add if Name Difference with a master name, remove otherwise
        lemsa_name = name_item.text().strip()
        aliases = self._load_name_aliases()
        if status == "Name Difference" and master_name:
            aliases[key] = {
                "lemsa_name": lemsa_name,
                "master_name": master_name,
            }
        elif key in aliases:
            del aliases[key]
        self._save_name_aliases(aliases)

        # Update exclusions: add if Error, remove otherwise
        exclusions = self._load_exclusions()
        if status == "Exclude":
            exclusions[key] = name_item.text().strip()
        elif key in exclusions:
            del exclusions[key]
        self._save_exclusions(exclusions)

    # -- Name alias persistence -----------------------------------------------

    def _get_aliases_path(self):
        return os.path.join(self.repo_root, "reference", "lemsa_name_aliases.json")

    def _load_name_aliases(self):
        path = self._get_aliases_path()
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def _save_name_aliases(self, aliases):
        path = self._get_aliases_path()
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(aliases, f, indent=2)
        except Exception:
            pass

    def _rebuild_aliases_from_edits(self):
        """Rebuild the alias file from all table edits with status 'Name Difference'."""
        edits = self._load_table_edits()
        aliases = {}
        # Try to recover original LEMSA names from compiled list
        cached = self._load_compiled_list()
        for key, data in edits.items():
            if data.get("status") == "Name Difference" and data.get("master_name"):
                lemsa_name = cached[key]["name"] if cached and key in cached else key
                aliases[key] = {
                    "lemsa_name": lemsa_name,
                    "master_name": data["master_name"],
                }
        self._save_name_aliases(aliases)
        return aliases

    # -- Exclusions persistence -----------------------------------------------

    def _get_exclusions_path(self):
        return os.path.join(self.repo_root, "reference", "lemsa_exclusions.json")

    def _load_exclusions(self):
        path = self._get_exclusions_path()
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def _save_exclusions(self, exclusions):
        path = self._get_exclusions_path()
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(exclusions, f, indent=2)
        except Exception:
            pass

    # -- Splits persistence ---------------------------------------------------

    def _get_splits_path(self):
        return os.path.join(self.repo_root, "reference", "lemsa_splits.json")

    def _load_splits(self):
        path = self._get_splits_path()
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def _save_splits(self, splits):
        path = self._get_splits_path()
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(splits, f, indent=2)
        except Exception:
            pass

    # -- LEMSA list ----------------------------------------------------------

    def _rebuild_lemsa_list(self):
        self._l_tree.clear()
        q = self._l_search.text().strip().lower()
        tracked_only = self._l_tracked_only.isChecked()

        # Group by state, preserving order of first appearance
        state_order = []
        state_items = {}  # state -> [(index, lemsa, conf, tracked)]
        for i, lemsa in enumerate(self.lemsa_data):
            state = lemsa.get("state", "Other")
            name = lemsa["name"]
            counties = ", ".join(lemsa.get("counties", []))
            searchable = f"{name} {counties} {state}".lower()
            if q and q not in searchable:
                continue
            conf = self._get_lemsa_conf(name)
            tracked = conf.get("tracked", False)
            if tracked_only and not tracked:
                continue
            if state not in state_items:
                state_order.append(state)
                state_items[state] = []
            state_items[state].append((i, lemsa, conf, tracked))

        for state in state_order:
            entries = state_items[state]
            n_tracked = sum(1 for _, _, _, t in entries if t)
            state_label = f"{state} ({len(entries)})"
            if n_tracked:
                state_label += f"  [{n_tracked} tracked]"
            state_node = QTreeWidgetItem([state_label])
            state_node.setForeground(0, QBrush(QColor("#89b4fa")))
            font = state_node.font(0)
            font.setBold(True)
            state_node.setFont(0, font)
            for i, lemsa, conf, tracked in entries:
                name = lemsa["name"]
                prefix = "✓ " if tracked else "  "
                acronym_tag = f" [{conf.get('acronym', '')}]" if conf.get("acronym") else ""
                status = ""
                if conf.get("last_checked"):
                    status = f"  [{conf['last_checked']}]"
                if conf.get("last_hash"):
                    status += "  ✔"
                child = QTreeWidgetItem([f"{prefix}{name}{acronym_tag}{status}"])
                child.setData(0, Qt.ItemDataRole.UserRole, i)
                if tracked:
                    child.setForeground(0, QBrush(QColor("#a6e3a1")))
                state_node.addChild(child)
            self._l_tree.addTopLevelItem(state_node)
            state_node.setExpanded(True)

    def _on_lemsa_select(self, item):
        idx = item.data(0, Qt.ItemDataRole.UserRole)
        if idx is not None:
            self._show_lemsa_editor(self.lemsa_data[idx])

    def _show_lemsa_editor(self, lemsa):
        self._clear_layout(self._l_editor_layout)
        name = lemsa["name"]
        conf = self._get_lemsa_conf(name)
        self._l_detail_title.setText(name)
        layout = self._l_editor_layout

        form = QFormLayout()
        state = lemsa.get("state", "")
        if state:
            form.addRow("State:", QLabel(state))
        counties_str = ", ".join(lemsa.get("counties", []))
        if counties_str:
            form.addRow("Counties:", QLabel(counties_str))

        url_label = QLabel(f'<a href="{lemsa["url"]}">{lemsa["url"]}</a>')
        url_label.setOpenExternalLinks(True)
        url_label.setWordWrap(True)
        form.addRow("Website:", url_label)
        layout.addLayout(form)

        tracked_cb = QCheckBox("Track this LEMSA")
        tracked_cb.setChecked(conf.get("tracked", False))
        layout.addWidget(tracked_cb)

        form1b = QFormLayout()
        acronym_edit = QLineEdit(conf.get("acronym", ""))
        acronym_edit.setPlaceholderText("e.g. ACEMS, CCEMSA, ICEMA")
        acronym_edit.setMaximumWidth(200)
        form1b.addRow("Acronym:", acronym_edit)
        acronym_hint = QLabel("Short identifier shown in the Agency column of the LEMSA comparison table")
        acronym_hint.setStyleSheet("color: #6c7086; font-size: 11px;")
        form1b.addRow("", acronym_hint)
        layout.addLayout(form1b)

        form2 = QFormLayout()
        page_edit = QLineEdit(conf.get("page_url", ""))
        form2.addRow("Protocols Page URL:", page_edit)
        link_edit = QLineEdit(conf.get("link_text", ""))
        form2.addRow("Link Text:", link_edit)
        hint = QLabel("Text of the clickable link on the page (not the PDF title)")
        hint.setStyleSheet("color: #6c7086; font-size: 11px;")
        form2.addRow("", hint)
        layout.addLayout(form2)

        # Status
        last_checked = conf.get("last_checked", "Never")
        last_hash = conf.get("last_hash", "")
        doc_url = conf.get("resolved_url", "")
        status = f"Last checked: {last_checked}"
        if last_hash:
            status += f"\nDocument hash: {last_hash[:16]}..."
        if doc_url:
            status += f"\nResolved URL: {doc_url}"
        status_label = QLabel(status)
        status_label.setWordWrap(True)
        layout.addWidget(status_label)

        # Buttons
        btn_layout = QHBoxLayout()
        save_btn = QPushButton("Save Settings")
        def _save():
            conf["tracked"] = tracked_cb.isChecked()
            conf["acronym"] = acronym_edit.text().strip()
            conf["page_url"] = page_edit.text().strip()
            conf["link_text"] = link_edit.text().strip()
            self._save_lemsa_config()
            self._rebuild_lemsa_list()
            self._status.showMessage(f"LEMSA config updated: {name}")
        save_btn.clicked.connect(_save)
        btn_layout.addWidget(save_btn)

        check_btn = QPushButton("Check Now")
        def _check():
            url = page_edit.text().strip()
            lt = link_edit.text().strip()
            if not url or not lt:
                self._status.showMessage("Enter both a protocols page URL and link text first.")
                return
            conf["tracked"] = tracked_cb.isChecked()
            conf["acronym"] = acronym_edit.text().strip()
            conf["page_url"] = url
            conf["link_text"] = lt
            self._save_lemsa_config()
            self._check_single_lemsa(name, conf, lemsa)
        check_btn.clicked.connect(_check)
        btn_layout.addWidget(check_btn)
        btn_layout.addStretch()
        layout.addLayout(btn_layout)
        layout.addStretch()

    # -- LEMSA checking ------------------------------------------------------

    def _check_single_lemsa(self, name, conf, lemsa=None):
        if self._checking:
            return
        self._checking = True
        self._show_progress(3, f"Checking {name}...")

        worker = SingleCheckWorker(self, name, conf)
        def _on_progress(msg):
            self._update_progress(self._g_progress.value() + 1, msg)
        def _on_finished(msg):
            self._update_progress(3, "Done")
            self._status.showMessage(msg)
            self._rebuild_lemsa_list()
            if lemsa:
                self._show_lemsa_editor(lemsa)
            self._checking = False
            self._hide_progress()
        def _on_error(msg):
            self._status.showMessage(msg)
            self._rebuild_lemsa_list()
            self._checking = False
            self._hide_progress()
        worker.progress.connect(_on_progress)
        worker.finished.connect(_on_finished)
        worker.error.connect(_on_error)
        self._worker = worker
        worker.start()

    def _check_lemsa_updates(self, callback=None):
        """Check all tracked LEMSAs for updates. Optional callback(results) when done."""
        if self._checking:
            return
        tracked = [(l, self._get_lemsa_conf(l["name"]))
                    for l in self.lemsa_data if self._get_lemsa_conf(l["name"]).get("tracked")]
        if not tracked:
            self._status.showMessage("No tracked LEMSAs.")
            if callback:
                callback({"changed": [], "baselined": [], "unchanged": [], "errors": []})
            return
        ready = [(l, c) for l, c in tracked if c.get("page_url") and c.get("link_text")]
        if not ready:
            self._status.showMessage("No tracked LEMSAs with complete config.")
            if callback:
                callback({"changed": [], "baselined": [], "unchanged": [], "errors": []})
            return
        self._checking = True
        total = len(ready)
        self._show_progress(total, f"Checking 0/{total}...")

        worker = CheckWorker(self, ready)
        def _on_progress(step, msg):
            self._update_progress(step, msg)
            self._status.showMessage(msg)
        def _on_finished(results):
            self._update_progress(total, "Done")
            self._rebuild_lemsa_list()
            parts = []
            if results["changed"]:
                parts.append(f"CHANGED: {', '.join(results['changed'])}")
            if results["baselined"]:
                parts.append(f"Baselined: {', '.join(results['baselined'])}")
            if results["unchanged"]:
                parts.append(f"Unchanged: {', '.join(results['unchanged'])}")
            if results["errors"]:
                parts.append(f"Errors: {', '.join(results['errors'])}")
            self._status.showMessage(" | ".join(parts))
            self._checking = False
            self._hide_progress()
            if callback:
                callback(results)
        worker.progress.connect(_on_progress)
        worker.finished.connect(_on_finished)
        self._worker = worker
        worker.start()

    # -- Fetch methods (same logic as tkinter version) -----------------------

    def _fetch_url(self, url):
        headers = {
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/131.0.0.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,"
                      "application/pdf,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Referer": url,
        }
        def _try_urllib(ssl_context=None):
            cj = http.cookiejar.CookieJar()
            handlers = [urllib.request.HTTPCookieProcessor(cj)]
            if ssl_context:
                handlers.append(urllib.request.HTTPSHandler(context=ssl_context))
            opener = urllib.request.build_opener(*handlers)
            req = urllib.request.Request(url, headers=headers)
            with opener.open(req, timeout=15) as resp:
                return resp.read()
        try:
            return _try_urllib()
        except urllib.error.URLError as e:
            if "CERTIFICATE_VERIFY_FAILED" in str(e):
                ctx = ssl.create_default_context()
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
                try:
                    return _try_urllib(ssl_context=ctx)
                except Exception:
                    pass
        try:
            result = subprocess.run(
                ["curl", "-sL", "--max-time", "15",
                 "-H", f"User-Agent: {headers['User-Agent']}",
                 "-H", f"Accept: {headers['Accept']}",
                 "-H", f"Referer: {url}", url],
                capture_output=True, timeout=20)
            if result.returncode == 0 and result.stdout:
                snippet = result.stdout[:200].lower()
                if b"access denied" not in snippet and b"403" not in snippet:
                    return result.stdout
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        try:
            return self._fetch_via_browser(url)
        except Exception:
            pass
        raise Exception(f"Could not fetch {url}")

    def _fetch_via_browser(self, url):
        script = os.path.join(self.repo_root, "tools", "scraper", "fetch_page.js")
        if not os.path.isfile(script):
            raise Exception("fetch_page.js not found")
        result = subprocess.run(["node", script, "--download", url],
                                capture_output=True, timeout=45)
        if result.returncode != 0 or not result.stdout:
            err = result.stderr.decode("utf-8", errors="ignore").strip()
            raise Exception(f"Browser download failed: {err[:200]}")
        return base64.b64decode(result.stdout)

    def _fetch_rendered_html(self, url):
        script = os.path.join(self.repo_root, "tools", "scraper", "fetch_page.js")
        if not os.path.isfile(script):
            raise Exception("fetch_page.js not found")
        try:
            result = subprocess.run(["node", script, url],
                                    capture_output=True, timeout=45)
        except FileNotFoundError:
            raise Exception("Node.js not found.")
        except subprocess.TimeoutExpired:
            raise Exception("Page render timed out")
        if result.returncode != 0:
            err = result.stderr.decode("utf-8", errors="ignore").strip()
            if "Cannot find module" in err and "puppeteer" in err.lower():
                raise Exception("Puppeteer not installed. Run: npm install puppeteer")
            raise Exception(f"fetch_page.js failed: {err[:200]}")
        return result.stdout.decode("utf-8", errors="ignore")

    def _extract_links(self, html):
        pattern = r'<a\s[^>]*href=["\']([^"\']+)["\'][^>]*>([\s\S]*?)</a>'
        matches = re.findall(pattern, html, re.IGNORECASE)
        candidates = []
        for href, inner in matches:
            href = html_module.unescape(href)
            clean = re.sub(r"<[^>]+>", "", inner).strip()
            clean = re.sub(r"\s+", " ", clean)
            clean = html_module.unescape(clean)
            if clean:
                candidates.append((href, clean))
        return candidates

    def _resolve_doc_url(self, page_url, link_text):
        target = link_text.strip().lower()
        def _make_absolute(href):
            if href.startswith("http"): return href
            elif href.startswith("/"):
                p = urlparse(page_url)
                return f"{p.scheme}://{p.netloc}{href}"
            else: return page_url.rsplit("/", 1)[0] + "/" + href

        def _find_match(candidates):
            for href, text in candidates:
                if text.lower() == target: return _make_absolute(href)
            for href, text in candidates:
                if target in text.lower(): return _make_absolute(href)
            return None

        html_bytes = self._fetch_url(page_url)
        html = html_bytes.decode("utf-8", errors="ignore")
        candidates = self._extract_links(html)
        result = _find_match(candidates)
        if result: return result

        try:
            rendered = self._fetch_rendered_html(page_url)
            candidates = self._extract_links(rendered)
            result = _find_match(candidates)
            if result: return result
        except Exception:
            pass

        doc_links = [t for _, t in candidates
                     if any(k in t.lower() for k in
                            ("inventory", "equipment", "supply", "protocol",
                             "policy", "list", "manual", "ambulance"))]
        if not doc_links:
            doc_links = [t for _, t in candidates if len(t) > 3]
        hint = "\n".join(f"  • {t}" for t in doc_links[:20])
        if not hint: hint = "(no links found)"
        raise Exception(f"Could not find link containing '{link_text}'.\n\nLinks found:\n{hint}")

    # -- Master list tree ----------------------------------------------------

    def _rebuild_master_tree(self):
        # Auto-push undo if data changed since last snapshot
        if self.master_list and not self._undo_suppress:
            new_snap = json.dumps(self.master_list.to_json_data())
            if self._master_last_snap is not None and new_snap != self._master_last_snap:
                self._master_undo_stack.append(self._master_last_snap)
                if len(self._master_undo_stack) > self._undo_max:
                    self._master_undo_stack.pop(0)
                self._master_redo_stack.clear()
            self._master_last_snap = new_snap
        saved = self._m_tree.beginRebuild()
        self._m_tree.clear()
        if not self.master_list:
            self._m_tree.endRebuild(saved)
            return
        q = self._m_search.text().strip().lower()
        CN = DragDropTree.ROLE_CLEAN_NAME

        for ci, cat in enumerate(self.master_list.categories):
            cat_match = q and q in cat.name.lower()
            show = [(ii, it) for ii, it in enumerate(cat.items) if not q or cat_match
                    or q in it.name.lower()
                    or (it.group and q in it.group.lower())]
            if not show and q: continue

            # Separate into groups and ungrouped
            groups = {}  # group_name -> [(ii, item)]
            ungrouped = []
            for ii, it in show:
                if it.group:
                    groups.setdefault(it.group, []).append((ii, it))
                else:
                    ungrouped.append((ii, it))

            total = len(show)
            cat_item = QTreeWidgetItem([cat.name])
            cat_item.setText(1, f"({total})")
            cat_item.setIcon(0, _ICONS["cat"])
            cat_item.setData(0, Qt.ItemDataRole.UserRole, ("cat", ci))
            cat_item.setData(0, CN, cat.name)
            self._m_tree.addTopLevelItem(cat_item)
            if q:
                cat_item.setExpanded(True)

            # Group nodes
            for group_name in sorted(groups.keys(), key=str.lower):
                members = groups[group_name]
                g_item = QTreeWidgetItem([group_name])
                g_item.setText(1, f"({len(members)})")
                g_item.setIcon(0, _ICONS["group"])
                g_item.setData(0, Qt.ItemDataRole.UserRole, ("group", ci, group_name))
                g_item.setData(0, CN, group_name)
                cat_item.addChild(g_item)
                if q: g_item.setExpanded(True)
                for ii, it in members:
                    i_item = QTreeWidgetItem([it.name])
                    i_item.setText(1, f"min {it.emsa_min}")
                    i_item.setData(0, Qt.ItemDataRole.UserRole, ("item", ci, ii))
                    i_item.setData(0, CN, it.name)
                    g_item.addChild(i_item)

            # Ungrouped items
            for ii, it in sorted(ungrouped, key=lambda x: x[1].name.lower()):
                i_item = QTreeWidgetItem([it.name])
                i_item.setText(1, f"min {it.emsa_min}")
                i_item.setData(0, Qt.ItemDataRole.UserRole, ("item", ci, ii))
                i_item.setData(0, CN, it.name)
                cat_item.addChild(i_item)

        self._m_tree.endRebuild(saved)

    def _on_master_select(self, item):
        data = item.data(0, Qt.ItemDataRole.UserRole)
        if not data: return
        kind = data[0]
        ci = data[1]
        cat = self.master_list.categories[ci]
        if kind == "item":
            ii = data[2]
            self._show_master_item_editor(cat, cat.items[ii])
        elif kind == "group":
            group_name = data[2]
            members = [it for it in cat.items if it.group == group_name]
            self._show_master_group_editor(cat, group_name, members)
        elif kind == "cat":
            self._show_master_cat_editor(cat)

    def _on_master_renamed(self, tree_item, new_text):
        """Handle inline rename in master tree."""
        data = tree_item.data(0, Qt.ItemDataRole.UserRole)
        if not data: return
        kind = data[0]
        ci = data[1]
        cat = self.master_list.categories[ci]
        if kind == "item":
            ii = data[2]
            item = cat.items[ii]
            old_name = item.name
            if new_text != old_name:
                item.name = new_text
                total = sum(rf.rename_item_everywhere(old_name, new_text) for rf in self.rig_files)
                if total:
                    self.dirty = True
                self.dirty_master = True
                self._update_save_state()
        elif kind == "group":
            old_group = data[2]
            for it in cat.items:
                if it.group == old_group:
                    it.group = new_text
            self.dirty_master = True
            self._update_save_state()
        elif kind == "cat":
            cat.name = new_text
            self.dirty_master = True
            self._update_save_state()
        self._rebuild_master_tree()
        # Re-select the renamed item (group key uses new name)
        if kind == "group":
            self._m_tree.select_by_data(("group", ci, new_text))
        else:
            self._m_tree.select_by_data(data)

    def _show_master_item_editor(self, cat, item):
        self._clear_layout(self._m_editor_layout)
        f = self._m_editor_layout
        title_parts = [cat.name]
        if item.group:
            title_parts.append(item.group)
        self._m_detail_title.setText(f"Edit Master Item — {'  ›  '.join(title_parts)}")

        form = QFormLayout()
        name_edit = QLineEdit(item.name)
        form.addRow("Item Name:", name_edit)
        qty_spin = QSpinBox()
        qty_spin.setRange(0, 9999)
        qty_spin.setValue(item.emsa_min)
        form.addRow("EMSA Min Qty:", qty_spin)
        group_edit = QLineEdit(item.group or "")
        group_edit.setPlaceholderText("(none)")
        form.addRow("Group:", group_edit)
        cat_combo = QComboBox()
        cat_combo.addItems([c.name for c in self.master_list.categories])
        cat_combo.setCurrentText(cat.name)
        form.addRow("Category:", cat_combo)
        f.addLayout(form)

        # Rig locations
        f.addWidget(QLabel("<b>Rig Locations:</b>"))
        loc_widgets = []
        for rf in self.rig_files:
            for loc in rf.item_locations(item.name):
                lf = QHBoxLayout()
                lf.addWidget(QLabel(f"{rf.filename} › {loc['area']} › {loc['category']}"))
                lq = QSpinBox()
                lq.setRange(0, 9999)
                lq.setValue(loc["qty"])
                lf.addWidget(lq)
                f.addLayout(lf)
                loc_widgets.append((lq, loc["item_ref"]))
        if not loc_widgets:
            f.addWidget(QLabel("(not placed on current rig)"))

        old_name = item.name

        def _apply():
            new_name = name_edit.text().strip()
            if not new_name: return
            if new_name != old_name:
                item.name = new_name
                total = sum(rf.rename_item_everywhere(old_name, new_name) for rf in self.rig_files)
                if total:
                    self._status.showMessage(f"Renamed '{old_name}' → '{new_name}' in {total} loc(s)")
                self.dirty = True
            item.emsa_min = qty_spin.value()
            item.group = group_edit.text().strip() or None
            new_cat = cat_combo.currentText()
            if new_cat != cat.name:
                cat.items.remove(item)
                for c in self.master_list.categories:
                    if c.name == new_cat:
                        c.items.append(item)
                        break
            for lq, iref in loc_widgets:
                iref.qty = lq.value()
            self.dirty_master = True
            self.dirty = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._rebuild_rig_tree()

        btn = QPushButton("Apply Changes")
        btn.clicked.connect(_apply)
        f.addWidget(btn)

        def _delete():
            cat.items.remove(item)
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._update_master_visibility()
            self._clear_editor(self._m_detail_title, self._m_editor_widget, self._m_editor_layout)
        del_btn = QPushButton("Delete from Master")
        del_btn.clicked.connect(_delete)
        f.addWidget(del_btn)
        f.addStretch()

    def _show_master_group_editor(self, cat, group_name, members):
        self._clear_layout(self._m_editor_layout)
        self._m_detail_title.setText(f"Edit Group — {cat.name}")
        f = self._m_editor_layout
        form = QFormLayout()
        name_edit = QLineEdit(group_name)
        form.addRow("Group Name:", name_edit)
        form.addRow("Items:", QLabel(str(len(members))))
        f.addLayout(form)
        old_group = group_name

        def _apply():
            new_group = name_edit.text().strip()
            if not new_group or new_group == old_group: return
            # Update group field on all members, and propagate to rig files
            total_renames = 0
            for it in members:
                it.group = new_group
                # Also update rig items with the same name
                for rf in self.rig_files:
                    for area in rf.areas:
                        for rcat in area.categories:
                            for ri in rcat.items:
                                if ri.name == it.name and ri.group == old_group:
                                    ri.group = new_group
                                    total_renames += 1
            self.dirty_master = True
            self.dirty = bool(total_renames) or self.dirty
            self._update_save_state()
            self._rebuild_master_tree()
            self._rebuild_rig_tree()
            self._status.showMessage(f"Renamed group '{old_group}' → '{new_group}'")

        btn = QPushButton("Apply")
        btn.clicked.connect(_apply)
        f.addWidget(btn)

        def _delete():
            if ConfirmDialog.confirm(self, "Delete Group",
                    f"Delete '{group_name}' and all {len(members)} items?"):
                for it in list(members):
                    cat.items.remove(it)
                self.dirty_master = True
                self._update_save_state()
                self._rebuild_master_tree()
                self._update_master_visibility()
                self._clear_editor(self._m_detail_title, self._m_editor_widget, self._m_editor_layout)
        del_btn = QPushButton("Delete Group")
        del_btn.clicked.connect(_delete)
        f.addWidget(del_btn)
        f.addStretch()

    def _show_master_cat_editor(self, cat):
        self._clear_layout(self._m_editor_layout)
        self._m_detail_title.setText("Edit Category")
        f = self._m_editor_layout
        form = QFormLayout()
        name_edit = QLineEdit(cat.name)
        form.addRow("Name:", name_edit)
        form.addRow("Items:", QLabel(str(len(cat.items))))
        groups = {it.group for it in cat.items if it.group}
        if groups:
            form.addRow("Groups:", QLabel(", ".join(sorted(groups))))
        f.addLayout(form)

        def _apply():
            n = name_edit.text().strip()
            if n:
                cat.name = n
                self.dirty_master = True
                self._update_save_state()
                self._rebuild_master_tree()
        btn = QPushButton("Apply")
        btn.clicked.connect(_apply)
        f.addWidget(btn)

        f.addWidget(QLabel("<b>Add Item:</b>"))
        form2 = QFormLayout()
        new_name = QLineEdit()
        form2.addRow("Name:", new_name)
        new_qty = QSpinBox()
        new_qty.setRange(0, 9999)
        new_qty.setValue(1)
        form2.addRow("EMSA Min:", new_qty)
        new_group = QLineEdit()
        new_group.setPlaceholderText("(none)")
        form2.addRow("Group:", new_group)
        f.addLayout(form2)

        def _add():
            n = new_name.text().strip()
            if n:
                g = new_group.text().strip() or None
                cat.items.append(MasterItem(n, new_qty.value(), g))
                new_name.clear()
                self.dirty_master = True
                self._update_save_state()
                self._rebuild_master_tree()
        add_btn = QPushButton("Add Item")
        add_btn.clicked.connect(_add)
        f.addWidget(add_btn)
        f.addStretch()

    def _on_master_right_click(self, pos):
        self._last_focused_tree = "master"
        item = self._m_tree.itemAt(pos)
        if item:
            # Only change current item if the right-clicked item isn't already
            # part of the selection — otherwise multi-select gets collapsed
            if item not in self._m_tree.selectedItems():
                self._m_tree.setCurrentItem(item)
        selected = self._m_tree.selectedItems()
        menu = QMenu(self)

        # Classify all selected nodes
        selected_items = []   # (cat, item)
        selected_groups = []  # (cat, group_name, [items])
        selected_cats = []    # (cat,)
        for sel in selected:
            d = sel.data(0, Qt.ItemDataRole.UserRole)
            if not d:
                continue
            kind = d[0]
            ci = d[1]
            cat = self.master_list.categories[ci]
            if kind == "item":
                ii = d[2]
                selected_items.append((cat, cat.items[ii]))
            elif kind == "group":
                group_name = d[2]
                members = [it for it in cat.items if it.group == group_name]
                selected_groups.append((cat, group_name, members))
            elif kind == "cat":
                selected_cats.append(cat)

        total_selected = len(selected_items) + len(selected_groups) + len(selected_cats)

        if item:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data:
                kind = data[0]
                ci = data[1]
                cat = self.master_list.categories[ci]

                # Context-specific actions first
                if kind == "item" and total_selected <= 1:
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addSeparator()

                elif kind == "group":
                    group_name = data[2]
                    members = [it for it in cat.items if it.group == group_name]
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addAction("Add Item to Group…",
                        lambda gn=group_name: self._qadd_master_item_to_group(cat, gn))
                    menu.addAction("Ungroup Items",
                        lambda c=cat, gn=group_name: self._ungroup_master(c, gn))
                    if total_selected <= 1:
                        grp_list = [(cat, group_name, members)]
                        move_cat_menu = menu.addMenu("Move to Category…")
                        self._build_group_cat_submenu(move_cat_menu, grp_list)
                    menu.addSeparator()

                elif kind == "cat":
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addAction("Add Item…", lambda: self._qadd_master_item(cat))
                    menu.addAction("Add Group…", lambda: self._qadd_master_group(cat))
                    menu.addAction("Add Category…", self._add_master_cat)
                    menu.addSeparator()

        # Clipboard actions
        menu.addAction("Copy\tCtrl+C", self._do_copy)
        menu.addAction("Cut\tCtrl+X", self._do_cut)
        if self._clipboard and self._clipboard["items"]:
            n = len(self._clipboard["items"])
            mode = self._clipboard["mode"]
            menu.addAction(f"Paste ({n} item{'s' if n > 1 else ''}, {mode})\tCtrl+V", self._do_paste)
        menu.addSeparator()

        # Multi-select move/duplicate
        if selected_items and not selected_groups and not selected_cats:
            n = len(selected_items)
            if n >= 1:
                add_menu = menu.addMenu(f"Move {n} item(s) to…")
                self._build_target_submenu(add_menu, selected_items, move=True)
                dup_menu = menu.addMenu(f"Duplicate {n} item(s) to…")
                self._build_target_submenu(dup_menu, selected_items, move=False)
                menu.addSeparator()

        # Multi-group move to category
        if selected_groups and not selected_cats:
            ng = len(selected_groups)
            grp_move_menu = menu.addMenu(f"Move {ng} group(s) to Category…")
            self._build_group_cat_submenu(grp_move_menu, list(selected_groups))
            menu.addSeparator()

        # Quick move shortcuts (items or groups selected, no categories)
        if (selected_items or selected_groups) and not selected_cats:
            menu.addAction("Move to Category…\tCtrl+M", self._do_move_to_category)
            menu.addAction("Move to New Category…\tCtrl+N", self._do_move_to_new_category)
            menu.addSeparator()

        # Delete
        if total_selected > 1:
            menu.addAction(f"Delete {total_selected} selected",
                           lambda si=list(selected_items), sg=list(selected_groups),
                                  sc=list(selected_cats):
                               self._delete_selected_master_nodes(si, sg, sc))
        elif item:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data:
                kind = data[0]
                ci = data[1]
                cat = self.master_list.categories[ci]
                if kind == "item":
                    it = cat.items[data[2]]
                    menu.addAction(f"Delete '{it.name}'", lambda: self._del_master_item(cat, it))
                elif kind == "group":
                    group_name = data[2]
                    members = [it for it in cat.items if it.group == group_name]
                    menu.addAction(f"Delete group '{group_name}' ({len(members)} items)",
                                   lambda c=cat, gn=group_name, m=list(members):
                                       self._delete_selected_master_nodes([], [(c, gn, m)], []))
                elif kind == "cat":
                    menu.addAction(f"Delete '{cat.name}'", lambda: self._del_master_cat(cat))

        if not item:
            menu.addAction("Add Category…", self._add_master_cat)

        # Undo/Redo
        menu.addSeparator()
        menu.addAction("Undo\tCtrl+Z", self._master_undo)
        menu.addAction("Redo\tCtrl+Shift+Z", self._master_redo)

        menu.exec(self._m_tree.viewport().mapToGlobal(pos))

    def _build_target_submenu(self, parent_menu, items_list, move=True):
        """Build Category/Group submenu for Add or Duplicate operations."""
        # Category submenu: lists all existing categories + New Category
        cat_menu = parent_menu.addMenu("Category")
        for cat in self.master_list.categories:
            if move:
                cat_menu.addAction(cat.name,
                    lambda c=cat.name, il=list(items_list):
                        self._move_selected_to_master_cat_by_name(il, c))
            else:
                cat_menu.addAction(cat.name,
                    lambda c=cat.name, il=list(items_list):
                        self._duplicate_selected_to_master_cat(il, c))
        cat_menu.addSeparator()
        if move:
            cat_menu.addAction("New Category…",
                lambda il=list(items_list): self._move_selected_to_new_cat(il))
        else:
            cat_menu.addAction("New Category…",
                lambda il=list(items_list): self._duplicate_selected_to_new_cat(il))

        # Group option
        if move:
            parent_menu.addAction("Group…",
                lambda il=list(items_list): self._add_selected_to_master_group(il))
        else:
            parent_menu.addAction("Group…",
                lambda il=list(items_list): self._duplicate_selected_to_master_group(il))

    def _add_selected_to_master_group(self, items_list):
        """Set the group field on selected items."""
        group_name, ok = QInputDialog.getText(self, "Set Group",
            "Group name (items will be tagged with this group):")
        if not ok or not group_name.strip():
            return
        group = group_name.strip()
        for cat, item in items_list:
            item.group = group
            # Also update matching rig items
            for rf in self.rig_files:
                for area in rf.areas:
                    for rcat in area.categories:
                        for ri in rcat.items:
                            if ri.name == item.name:
                                ri.group = group
        self.dirty_master = True
        self.dirty = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._rebuild_rig_tree()
        self._status.showMessage(f"Set group '{group}' on {len(items_list)} item(s)")

    def _move_selected_to_master_cat_by_name(self, items_list, cat_name):
        """Move items to a named category."""
        target_cat = None
        for c in self.master_list.categories:
            if c.name == cat_name:
                target_cat = c
                break
        if not target_cat:
            return
        moved = 0
        for src_cat, item in items_list:
            if item in src_cat.items and src_cat is not target_cat:
                src_cat.items.remove(item)
                target_cat.items.append(item)
                moved += 1
        if moved:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._status.showMessage(f"Moved {moved} item(s) to '{cat_name}'")

    def _move_selected_to_new_cat(self, items_list):
        """Move items to a newly created category."""
        name, ok = QInputDialog.getText(self, "New Category", "Category name:")
        if not ok or not name.strip():
            return
        name = name.strip()
        # Create category if it doesn't exist
        target_cat = None
        for c in self.master_list.categories:
            if c.name == name:
                target_cat = c
                break
        if not target_cat:
            target_cat = MasterCategory(name)
            self.master_list.categories.append(target_cat)
        self._move_selected_to_master_cat_by_name(items_list, name)

    def _build_group_cat_submenu(self, parent_menu, groups_list):
        """Build Category submenu for moving group(s) to a different category.
        groups_list: list of (cat, group_name, [members])"""
        for cat in self.master_list.categories:
            parent_menu.addAction(cat.name,
                lambda c=cat.name, gl=list(groups_list):
                    self._move_groups_to_master_cat_by_name(gl, c))
        parent_menu.addSeparator()
        parent_menu.addAction("New Category…",
            lambda gl=list(groups_list): self._move_groups_to_new_cat(gl))

    def _move_groups_to_master_cat_by_name(self, groups_list, cat_name):
        """Move all member items of group(s) to a named category, preserving group tags.
        groups_list: list of (src_cat, group_name, [members])"""
        target_cat = None
        for c in self.master_list.categories:
            if c.name == cat_name:
                target_cat = c
                break
        if not target_cat:
            return
        moved = 0
        for src_cat, group_name, members in groups_list:
            if src_cat is target_cat:
                continue
            for item in list(members):
                if item in src_cat.items:
                    src_cat.items.remove(item)
                    target_cat.items.append(item)
                    moved += 1
        if moved:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            ng = len(groups_list)
            lbl = f"{ng} group(s)" if ng > 1 else f"group '{groups_list[0][1]}'"
            self._status.showMessage(
                f"Moved {moved} item(s) from {lbl} to '{cat_name}'")

    def _move_groups_to_new_cat(self, groups_list):
        """Move group(s) to a newly created category."""
        name, ok = QInputDialog.getText(self, "New Category", "Category name:")
        if not ok or not name.strip():
            return
        name = name.strip()
        target_cat = None
        for c in self.master_list.categories:
            if c.name == name:
                target_cat = c
                break
        if not target_cat:
            target_cat = MasterCategory(name)
            self.master_list.categories.append(target_cat)
        self._move_groups_to_master_cat_by_name(groups_list, name)

    def _duplicate_selected_to_master_cat(self, items_list, cat_name):
        """Duplicate items into a named category."""
        target_cat = None
        for c in self.master_list.categories:
            if c.name == cat_name:
                target_cat = c
                break
        if not target_cat:
            return
        duped = 0
        for _, item in items_list:
            # Check for duplicate names in target
            if not any(it.name.lower() == item.name.lower() for it in target_cat.items):
                target_cat.items.append(MasterItem(item.name, item.emsa_min))
                duped += 1
        if duped:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._status.showMessage(f"Duplicated {duped} item(s) to '{cat_name}'")

    def _duplicate_selected_to_new_cat(self, items_list):
        """Duplicate items into a newly created category."""
        name, ok = QInputDialog.getText(self, "New Category", "Category name:")
        if not ok or not name.strip():
            return
        name = name.strip()
        target_cat = None
        for c in self.master_list.categories:
            if c.name == name:
                target_cat = c
                break
        if not target_cat:
            target_cat = MasterCategory(name)
            self.master_list.categories.append(target_cat)
        self._duplicate_selected_to_master_cat(items_list, name)

    def _duplicate_selected_to_master_group(self, items_list):
        """Duplicate items with a group tag."""
        group_name, ok = QInputDialog.getText(self, "Duplicate to Group",
            "Group name for duplicated items:")
        if not ok or not group_name.strip():
            return
        group = group_name.strip()
        duped = 0
        for cat, item in items_list:
            # Avoid exact duplicates in same category
            if not any(it.name.lower() == item.name.lower() and it.group == group for it in cat.items):
                cat.items.append(MasterItem(item.name, item.emsa_min, group))
                duped += 1
        if duped:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._status.showMessage(f"Duplicated {duped} item(s) to group '{group}'")

    def _delete_selected_master_nodes(self, items_list, groups_list, cats_list):
        """Delete any mix of selected items, groups, and categories from master."""
        item_count = len(items_list)
        group_item_count = sum(len(members) for _, _, members in groups_list)
        cat_item_count = sum(len(c.items) for c in cats_list)
        total = item_count + len(groups_list) + len(cats_list)
        detail_parts = []
        if item_count:
            detail_parts.append(f"{item_count} item(s)")
        if groups_list:
            detail_parts.append(f"{len(groups_list)} group(s) ({group_item_count} items)")
        if cats_list:
            detail_parts.append(f"{len(cats_list)} category(ies) ({cat_item_count} items)")
        detail = ", ".join(detail_parts)

        if total > 1 or groups_list or cats_list:
            if not ConfirmDialog.confirm(self, "Delete",
                    f"Delete {detail}?"):
                return

        for cat, item in items_list:
            if item in cat.items:
                cat.items.remove(item)

        for cat, group_name, members in groups_list:
            for it in list(members):
                if it in cat.items:
                    cat.items.remove(it)

        for cat in cats_list:
            if cat in self.master_list.categories:
                self.master_list.categories.remove(cat)

        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()
        self._clear_editor(self._m_detail_title, self._m_editor_widget, self._m_editor_layout)
        self._status.showMessage(f"Deleted {detail}")

    def _on_master_drop(self, source_data_list, target_data):
        """Handle drag-drop in master tree. Receives pre-serialized UserRole data."""
        if not self.master_list or not target_data:
            return

        target_kind = target_data[0]
        target_ci = target_data[1]
        if target_ci >= len(self.master_list.categories):
            return
        target_cat = self.master_list.categories[target_ci]
        target_group = target_data[2] if target_kind == "group" else None

        # Check for group-to-group merge
        src_groups = [sd for sd in source_data_list if sd and sd[0] == "group"]
        if src_groups and target_kind == "group":
            src_group_names = [sd[2] for sd in src_groups if sd[2] != target_group]
            if src_group_names:
                names = ", ".join(src_group_names)
                if not ConfirmDialog.confirm(self, "Merge Groups",
                        f"Merge '{names}' into '{target_group}'?"):
                    return

        # Collect moves
        item_moves = []
        for src_data in source_data_list:
            if not src_data:
                continue
            src_kind = src_data[0]
            src_ci = src_data[1]
            if src_ci >= len(self.master_list.categories):
                continue
            src_cat = self.master_list.categories[src_ci]

            if src_kind == "item":
                ii = src_data[2]
                if ii < len(src_cat.items):
                    item = src_cat.items[ii]
                    if src_cat is not target_cat or target_group is not None:
                        item_moves.append((src_cat, item))
            elif src_kind == "group":
                src_gn = src_data[2]
                for it in list(src_cat.items):
                    if it.group == src_gn:
                        item_moves.append((src_cat, it))

        # Apply moves
        moved = 0
        for src_cat, item in item_moves:
            if src_cat is target_cat and item.group == target_group:
                continue  # already in target
            if item in src_cat.items:
                src_cat.items.remove(item)
            if target_group is not None:
                item.group = target_group
            if item not in target_cat.items:
                target_cat.items.append(item)
            moved += 1

        if moved:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._status.showMessage(f"Moved {moved} item(s) to '{target_cat.name}'")

    def _add_master_cat(self):
        if not self.master_list: return
        n, ok = QInputDialog.getText(self, "Add Category", "Category name:")
        if ok and n.strip():
            self.master_list.categories.append(MasterCategory(n.strip()))
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()

    def _qadd_master_item(self, cat):
        n, ok = QInputDialog.getText(self, "Add Item", "Item name:")
        if not ok or not n.strip(): return
        q, ok = QInputDialog.getInt(self, "EMSA Min", "EMSA minimum qty:", 1, 0, 9999)
        if not ok: return
        cat.items.append(MasterItem(n.strip(), q))
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()

    def _ungroup_master(self, cat, group_name):
        """Remove group tag from all items in a master list group."""
        count = 0
        for it in cat.items:
            if it.group == group_name:
                it.group = None
                count += 1
        if count:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._status.showMessage(f"Ungrouped {count} item(s) from '{group_name}'")

    def _ungroup_rig(self, cat, group_name):
        """Remove group tag from all items in a rig group."""
        count = 0
        for it in cat.items:
            if it.group == group_name:
                it.group = None
                count += 1
        if count:
            self._set_dirty()
            self._rebuild_rig_tree()
            self._status.showMessage(f"Ungrouped {count} item(s) from '{group_name}'")

    def _del_master_item(self, cat, item):
        cat.items.remove(item)
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()

    def _del_master_cat(self, cat):
        if cat.items:
            if not ConfirmDialog.confirm(self, "Delete",
                    f"Delete '{cat.name}' and {len(cat.items)} items?"):
                return
        self.master_list.categories.remove(cat)
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()

    # -- Rig tree ------------------------------------------------------------

    def _rebuild_rig_tree(self):
        # Auto-push undo if data changed since last snapshot
        if self.current_file and not self._undo_suppress:
            new_snap = json.dumps(self.current_file.to_json_data())
            if self._rig_last_snap is not None and new_snap != self._rig_last_snap:
                self._rig_undo_stack.append(self._rig_last_snap)
                if len(self._rig_undo_stack) > self._undo_max:
                    self._rig_undo_stack.pop(0)
                self._rig_redo_stack.clear()
            self._rig_last_snap = new_snap
        saved = self._r_tree.beginRebuild()
        self._r_tree.clear()
        if not self.current_file:
            self._r_tree.endRebuild(saved)
            return
        q = self._r_search.text().strip().lower()
        mn = self.master_list.all_item_names() if self.master_list else set()
        CN = DragDropTree.ROLE_CLEAN_NAME

        # Build area nodes, then nest children under parents
        area_nodes = {}  # ai -> QTreeWidgetItem
        child_areas = []  # [(ai, area)] — deferred until parents exist

        def _build_area_content(area_item, ai, area):
            """Populate an area node with categories, groups, and items."""
            area_match = q and q in area.name.lower()
            for ci, cat in enumerate(area.categories):
                cat_match = q and q in cat.name.lower()
                matches = [(ii, it) for ii, it in enumerate(cat.items)
                           if not q or area_match or cat_match
                           or q in it.name.lower() or (it.group and q in it.group.lower())]
                if not matches:
                    continue

                cat_item = QTreeWidgetItem([cat.name])
                cat_item.setText(1, f"({len(matches)})")
                cat_item.setIcon(0, _ICONS["cat"])
                cat_item.setData(0, Qt.ItemDataRole.UserRole, ("cat", ai, ci))
                cat_item.setData(0, CN, cat.name)
                area_item.addChild(cat_item)
                if q: cat_item.setExpanded(True)

                # Separate into groups and ungrouped
                groups = {}
                ungrouped = []
                for ii, it in matches:
                    if it.group:
                        groups.setdefault(it.group, []).append((ii, it))
                    else:
                        ungrouped.append((ii, it))

                # Group nodes
                for group_name in sorted(groups.keys(), key=str.lower):
                    members = groups[group_name]
                    g_item = QTreeWidgetItem([group_name])
                    g_item.setText(1, f"({len(members)})")
                    g_item.setIcon(0, _ICONS["group"])
                    g_item.setData(0, Qt.ItemDataRole.UserRole, ("group", ai, ci, group_name))
                    g_item.setData(0, CN, group_name)
                    cat_item.addChild(g_item)
                    if q: g_item.setExpanded(True)
                    for ii, it in members:
                        ok = it.name in mn
                        flag = "" if ok else "  ⚠"
                        i_item = QTreeWidgetItem([it.name])
                        i_item.setText(1, f"×{it.qty}{flag}")
                        i_item.setData(0, Qt.ItemDataRole.UserRole, ("item", ai, ci, ii))
                        i_item.setData(0, CN, it.name)
                        if not ok:
                            i_item.setForeground(0, QBrush(QColor("#f38ba8")))
                            i_item.setForeground(1, QBrush(QColor("#f38ba8")))
                        g_item.addChild(i_item)

                # Ungrouped items
                for ii, it in ungrouped:
                    ok = it.name in mn
                    flag = "" if ok else "  ⚠"
                    i_item = QTreeWidgetItem([it.name])
                    i_item.setText(1, f"×{it.qty}{flag}")
                    i_item.setData(0, Qt.ItemDataRole.UserRole, ("item", ai, ci, ii))
                    i_item.setData(0, CN, it.name)
                    if not ok:
                        i_item.setForeground(0, QBrush(QColor("#f38ba8")))
                        i_item.setForeground(1, QBrush(QColor("#f38ba8")))
                    cat_item.addChild(i_item)

            return area_item.childCount() > 0

        # First pass: create all area nodes
        for ai, area in enumerate(self.current_file.areas):
            seal = " 🔒" if area.sealable else ""
            area_item = QTreeWidgetItem([f"{area.name}{seal}"])
            area_item.setIcon(0, _ICONS["area"])
            area_item.setData(0, Qt.ItemDataRole.UserRole, ("area", ai))
            area_item.setData(0, CN, area.name)
            has_content = _build_area_content(area_item, ai, area)

            if not has_content and q and not (q in area.name.lower()):
                continue  # skip empty areas during search unless area name matches

            area_nodes[ai] = area_item
            if area.child_of:
                child_areas.append((ai, area))
            else:
                self._r_tree.addTopLevelItem(area_item)
                if q: area_item.setExpanded(True)

        # Second pass: nest child areas under parents
        for ai, area in child_areas:
            parent_node = None
            for pai, parea in enumerate(self.current_file.areas):
                if parea.name == area.child_of and pai in area_nodes:
                    parent_node = area_nodes[pai]
                    break
            if parent_node:
                parent_node.addChild(area_nodes[ai])
                if q: parent_node.setExpanded(True)
            else:
                # Parent not found — add as top-level
                self._r_tree.addTopLevelItem(area_nodes[ai])
            if q and ai in area_nodes:
                area_nodes[ai].setExpanded(True)

        self._r_tree.endRebuild(saved)

    def _on_rig_tree_select(self, item):
        data = item.data(0, Qt.ItemDataRole.UserRole)
        if not data: return
        kind = data[0]
        ai = data[1]
        area = self.current_file.areas[ai]
        if kind == "area":
            self._show_rig_area_editor(area)
        elif kind == "cat":
            ci = data[2]
            self._show_rig_cat_editor(area, area.categories[ci])
        elif kind == "group":
            ci = data[2]
            group_name = data[3]
            self._show_rig_group_editor(area, area.categories[ci], group_name)
        elif kind == "item":
            ci, ii = data[2], data[3]
            cat = area.categories[ci]
            self._show_rig_item_editor(area, cat, cat.items[ii])

    def _on_rig_renamed(self, tree_item, new_text):
        """Handle inline rename in rig tree."""
        data = tree_item.data(0, Qt.ItemDataRole.UserRole)
        if not data: return
        kind = data[0]
        ai = data[1]
        area = self.current_file.areas[ai]
        if kind == "item":
            ci, ii = data[2], data[3]
            item = area.categories[ci].items[ii]
            item.name = new_text
        elif kind == "cat":
            ci = data[2]
            area.categories[ci].name = new_text
        elif kind == "group":
            ci = data[2]
            old_group = data[3]
            for it in area.categories[ci].items:
                if it.group == old_group:
                    it.group = new_text
        elif kind == "area":
            area.name = new_text
        self._set_dirty()
        self._rebuild_rig_tree()
        # Re-select the renamed item (group key uses new name)
        if kind == "group":
            self._r_tree.select_by_data(("group", ai, data[2], new_text))
        else:
            self._r_tree.select_by_data(data)

    def _show_rig_item_editor(self, area, cat, item):
        """Edit an item."""
        self._clear_layout(self._r_editor_layout)
        self._r_detail_title.setText(f"Edit Item — {area.name} › {cat.name}")
        f = self._r_editor_layout
        mn = self.master_list.all_item_names() if self.master_list else set()

        if item.name not in mn:
            warn = QLabel("⚠ Not in master list")
            warn.setStyleSheet("color: #fab387; font-weight: bold;")
            f.addWidget(warn)

        form = QFormLayout()
        name_edit = QLineEdit(item.name)
        form.addRow("Name:", name_edit)
        qty_spin = QSpinBox()
        qty_spin.setRange(0, 9999)
        qty_spin.setValue(item.qty)
        form.addRow("Qty:", qty_spin)
        group_edit = QLineEdit(item.group or "")
        group_edit.setPlaceholderText("(none)")
        form.addRow("Group:", group_edit)

        # Build destinations
        dests = {}
        dest_combo = QComboBox()
        cur = f"{area.name} › {cat.name}"
        for a in self.current_file.areas:
            for c in a.categories:
                lb = f"{a.name} › {c.name}"
                dest_combo.addItem(lb)
                dests[lb] = (a, c)
        dest_combo.setCurrentText(cur)
        form.addRow("Move to:", dest_combo)
        f.addLayout(form)

        def _apply():
            nn = name_edit.text().strip()
            if not nn: return
            item.name = nn
            item.qty = qty_spin.value()
            item.group = group_edit.text().strip() or None
            dl = dest_combo.currentText()
            if dl != cur and dl in dests:
                cat.items.remove(item)
                dests[dl][1].items.append(item)
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
        btn = QPushButton("Apply")
        btn.clicked.connect(_apply)
        f.addWidget(btn)

        def _delete():
            cat.items.remove(item)
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
            self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        del_btn = QPushButton("Delete")
        del_btn.clicked.connect(_delete)
        f.addWidget(del_btn)
        f.addStretch()

    def _show_rig_area_editor(self, area):
        self._clear_layout(self._r_editor_layout)
        self._r_detail_title.setText("Edit Area")
        f = self._r_editor_layout
        form = QFormLayout()
        name_edit = QLineEdit(area.name)
        form.addRow("Name:", name_edit)
        seal_cb = QCheckBox("Sealable")
        seal_cb.setChecked(area.sealable)
        form.addRow("", seal_cb)
        parent_combo = QComboBox()
        parent_combo.addItem("(none)")
        for a in self.current_file.areas:
            if a is not area:
                parent_combo.addItem(a.name)
        parent_combo.setCurrentText(area.child_of or "(none)")
        form.addRow("Child of:", parent_combo)
        f.addLayout(form)

        def _apply():
            n = name_edit.text().strip()
            if n: area.name = n
            area.sealable = seal_cb.isChecked()
            p = parent_combo.currentText()
            area.child_of = p if p != "(none)" else None
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
        btn = QPushButton("Apply")
        btn.clicked.connect(_apply)
        f.addWidget(btn)

        f.addWidget(QLabel("<b>Add Category:</b>"))
        cat_edit = QLineEdit()
        f.addWidget(cat_edit)
        def _add_cat():
            n = cat_edit.text().strip()
            if n:
                area.categories.append(Category(n))
                cat_edit.clear()
                self.dirty = True
                self._update_save_state()
                self._rebuild_rig_tree()
        f.addWidget(QPushButton("Add Category", clicked=_add_cat))

        def _delete():
            if ConfirmDialog.confirm(self, "Delete", f"Delete area '{area.name}'?"):
                self.current_file.areas.remove(area)
                self.dirty = True
                self._update_save_state()
                self._rebuild_rig_tree()
                self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        del_btn = QPushButton("Delete Area")
        del_btn.clicked.connect(_delete)
        f.addWidget(del_btn)
        f.addStretch()

    def _show_rig_cat_editor(self, area, cat):
        self._clear_layout(self._r_editor_layout)
        self._r_detail_title.setText(f"Edit Category — {area.name}")
        f = self._r_editor_layout
        form = QFormLayout()
        name_edit = QLineEdit(cat.name)
        form.addRow("Name:", name_edit)
        f.addLayout(form)

        def _apply():
            n = name_edit.text().strip()
            if n: cat.name = n
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
        f.addWidget(QPushButton("Apply", clicked=_apply))

        f.addWidget(QLabel("<b>Add Item:</b>"))
        form2 = QFormLayout()
        item_edit = QLineEdit()
        form2.addRow("Name:", item_edit)
        item_qty = QSpinBox()
        item_qty.setRange(0, 9999)
        item_qty.setValue(1)
        form2.addRow("Qty:", item_qty)
        item_group = QLineEdit()
        item_group.setPlaceholderText("(none)")
        form2.addRow("Group:", item_group)
        f.addLayout(form2)

        def _add():
            n = item_edit.text().strip()
            if n:
                g = item_group.text().strip() or None
                cat.items.append(Item(n, item_qty.value(), g))
                item_edit.clear()
                self.dirty = True
                self._update_save_state()
                self._rebuild_rig_tree()
        f.addWidget(QPushButton("Add Item", clicked=_add))

        def _delete():
            if ConfirmDialog.confirm(self, "Delete", f"Delete '{cat.name}'?"):
                area.categories.remove(cat)
                self.dirty = True
                self._update_save_state()
                self._rebuild_rig_tree()
                self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        f.addWidget(QPushButton("Delete Category", clicked=_delete))
        f.addStretch()

    def _show_rig_group_editor(self, area, cat, group_name):
        """Editor for a group of items within a rig category."""
        members = [it for it in cat.items if it.group == group_name]
        self._clear_layout(self._r_editor_layout)
        self._r_detail_title.setText(f"Edit Group — {area.name} › {cat.name}")
        f = self._r_editor_layout
        form = QFormLayout()
        name_edit = QLineEdit(group_name)
        form.addRow("Group Name:", name_edit)
        form.addRow("Items:", QLabel(str(len(members))))
        f.addLayout(form)
        old_group = group_name

        def _apply():
            new_group = name_edit.text().strip()
            if not new_group or new_group == old_group: return
            for it in members:
                it.group = new_group
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
            self._status.showMessage(f"Renamed group '{old_group}' → '{new_group}'")
        f.addWidget(QPushButton("Apply", clicked=_apply))

        def _ungroup():
            for it in members:
                it.group = None
            self.dirty = True
            self._update_save_state()
            self._rebuild_rig_tree()
            self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
            self._status.showMessage(f"Ungrouped {len(members)} item(s)")
        f.addWidget(QPushButton("Ungroup Items", clicked=_ungroup))

        def _delete():
            if ConfirmDialog.confirm(self, "Delete",
                    f"Delete group '{group_name}' and {len(members)} items?"):
                for it in list(members):
                    cat.items.remove(it)
                self.dirty = True
                self._update_save_state()
                self._rebuild_rig_tree()
                self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        f.addWidget(QPushButton("Delete Group", clicked=_delete))
        f.addStretch()

    def _on_rig_right_click(self, pos):
        if not self.current_file:
            return
        self._last_focused_tree = "rig"
        item = self._r_tree.itemAt(pos)
        if item:
            # Only change current item if the right-clicked item isn't already
            # part of the selection — otherwise multi-select gets collapsed
            if item not in self._r_tree.selectedItems():
                self._r_tree.setCurrentItem(item)
        selected = self._r_tree.selectedItems()
        menu = QMenu(self)

        # Classify all selected nodes
        selected_items = []   # (area, cat, item)
        selected_cats = []    # (area, cat)
        selected_areas = []   # (area,)
        for sel in selected:
            d = sel.data(0, Qt.ItemDataRole.UserRole)
            if not d:
                continue
            kind = d[0]
            ai = d[1]
            area = self.current_file.areas[ai]
            if kind == "item":
                ci, ii = d[2], d[3]
                cat = area.categories[ci]
                selected_items.append((area, cat, cat.items[ii]))
            elif kind == "cat":
                ci = d[2]
                selected_cats.append((area, area.categories[ci]))
            elif kind == "area":
                selected_areas.append(area)

        total_selected = len(selected_items) + len(selected_cats) + len(selected_areas)

        if item:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data:
                kind = data[0]
                ai = data[1]
                area = self.current_file.areas[ai]

                # Context-specific actions first
                if kind == "item" and total_selected <= 1:
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addSeparator()

                elif kind == "group":
                    ci = data[2]; group_name = data[3]
                    cat = area.categories[ci]
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addAction("Add Item to Group…",
                        lambda c=cat, gn=group_name: self._radd_item_to_group(c, gn))
                    menu.addAction("Ungroup Items",
                        lambda c=cat, gn=group_name: self._ungroup_rig(c, gn))
                    menu.addSeparator()

                elif kind == "cat":
                    ci = data[2]; cat = area.categories[ci]
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addAction("Add Item…", lambda: self._radd_item(cat))
                    menu.addAction("Add Group…", lambda: self._radd_group(cat))
                    menu.addSeparator()

                elif kind == "area":
                    menu.addAction("Rename\tCtrl+R", self._do_rename)
                    menu.addAction("Add Category…", lambda: self._radd_cat(area))
                    menu.addAction("Add Area…", self._add_rig_area)
                    menu.addSeparator()

        # Clipboard actions
        menu.addAction("Copy\tCtrl+C", self._do_copy)
        menu.addAction("Cut\tCtrl+X", self._do_cut)
        if self._clipboard and self._clipboard["items"]:
            n = len(self._clipboard["items"])
            mode = self._clipboard["mode"]
            menu.addAction(f"Paste ({n} item{'s' if n > 1 else ''}, {mode})\tCtrl+V", self._do_paste)
        menu.addSeparator()

        # Move to area (items only)
        if selected_items and not selected_cats and not selected_areas:
            n = len(selected_items)
            area_names = [a.name for a in self.current_file.areas]
            move_menu = menu.addMenu(f"Move {n} item(s) to Area…")
            for area_name in area_names:
                move_menu.addAction(area_name,
                    lambda an=area_name, si=list(selected_items):
                        self._move_selected_to_rig_area(si, an))
            menu.addAction("Move to Category…\tCtrl+M", self._do_move_to_category)
            menu.addAction("Move to New Category…\tCtrl+N", self._do_move_to_new_category)
            menu.addSeparator()

        # Delete
        if total_selected > 1:
            menu.addAction(f"Delete {total_selected} selected",
                           lambda si=list(selected_items), sc=list(selected_cats),
                                  sa=list(selected_areas):
                               self._delete_selected_rig_nodes(si, sc, sa))
        elif item:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            if data:
                kind = data[0]
                ai = data[1]
                area = self.current_file.areas[ai]
                if kind == "item":
                    it = area.categories[data[2]].items[data[3]]
                    menu.addAction(f"Delete '{it.name}'",
                        lambda: self._delete_selected_rig_nodes([(area, area.categories[data[2]], it)], [], []))
                elif kind == "group":
                    cat = area.categories[data[2]]
                    members = [it for it in cat.items if it.group == data[3]]
                    menu.addAction(f"Delete group '{data[3]}' ({len(members)} items)",
                        lambda c=cat, m=list(members):
                            self._delete_selected_rig_nodes(
                                [(area, c, it) for it in m], [], []))
                elif kind == "cat":
                    cat = area.categories[data[2]]
                    menu.addAction(f"Delete '{cat.name}'",
                        lambda: self._delete_selected_rig_nodes([], [(area, cat)], []))
                elif kind == "area":
                    menu.addAction(f"Delete '{area.name}'",
                        lambda: self._delete_selected_rig_nodes([], [], [area]))

        if not item:
            menu.addAction("Add Area…", self._add_rig_area)

        # Undo/Redo
        menu.addSeparator()
        menu.addAction("Undo\tCtrl+Z", self._rig_undo)
        menu.addAction("Redo\tCtrl+Shift+Z", self._rig_redo)

        menu.exec(self._r_tree.viewport().mapToGlobal(pos))

    def _move_selected_to_rig_area(self, items_list, target_area_name):
        """Move items to the first category of the target area."""
        target_area = None
        for a in self.current_file.areas:
            if a.name == target_area_name:
                target_area = a
                break
        if not target_area:
            return
        # Ensure target has at least one category
        if not target_area.categories:
            target_area.categories.append(Category("General"))
        target_cat = target_area.categories[0]
        moved = 0
        for src_area, src_cat, item in items_list:
            if item in src_cat.items:
                src_cat.items.remove(item)
                target_cat.items.append(item)
                moved += 1
        if moved:
            self._set_dirty()
            self._rebuild_rig_tree()
            self._status.showMessage(f"Moved {moved} item(s) to '{target_area_name}'")

    def _delete_selected_rig_nodes(self, items_list, cats_list, areas_list):
        """Delete any mix of selected items, categories, and areas from rig file."""
        detail_parts = []
        if items_list:
            detail_parts.append(f"{len(items_list)} item(s)")
        if cats_list:
            cat_item_count = sum(len(c.items) for _, c in cats_list)
            detail_parts.append(f"{len(cats_list)} category(ies) ({cat_item_count} items)")
        if areas_list:
            area_item_count = sum(
                sum(len(c.items) for c in a.categories) for a in areas_list)
            detail_parts.append(f"{len(areas_list)} area(s) ({area_item_count} items)")
        detail = ", ".join(detail_parts)
        total = len(items_list) + len(cats_list) + len(areas_list)

        if total > 1 or cats_list or areas_list:
            if not ConfirmDialog.confirm(self, "Delete",
                    f"Delete {detail}?"):
                return

        for _, cat, item in items_list:
            if item in cat.items:
                cat.items.remove(item)

        for area, cat in cats_list:
            if cat in area.categories:
                area.categories.remove(cat)

        for area in areas_list:
            if area in self.current_file.areas:
                self.current_file.areas.remove(area)

        self._set_dirty()
        self._rebuild_rig_tree()
        self._clear_editor(self._r_detail_title, self._r_editor_widget, self._r_editor_layout)
        self._status.showMessage(f"Deleted {detail}")

    def _on_rig_drop(self, source_data_list, target_data):
        """Handle drag-drop in rig tree. Receives pre-serialized UserRole data."""
        if not self.current_file or not target_data:
            return

        target_kind = target_data[0]
        target_ai = target_data[1]
        if target_ai >= len(self.current_file.areas):
            return
        target_area = self.current_file.areas[target_ai]
        target_group = None

        if target_kind == "group":
            target_ci = target_data[2]
            if target_ci >= len(target_area.categories):
                return
            target_cat = target_area.categories[target_ci]
            target_group = target_data[3]
        elif target_kind in ("item", "cat"):
            target_ci = target_data[2]
            if target_ci >= len(target_area.categories):
                return
            target_cat = target_area.categories[target_ci]
        elif target_kind == "area":
            if not target_area.categories:
                target_area.categories.append(Category("General"))
            target_cat = target_area.categories[0]
        else:
            return

        # Check for group-to-group merge
        src_groups = []
        for src_data in source_data_list:
            if src_data and src_data[0] == "group":
                src_groups.append(src_data)

        if src_groups and target_kind == "group":
            src_group_names = []
            for sd in src_groups:
                if sd[3] != target_group:
                    src_group_names.append(sd[3])
            if src_group_names:
                names = ", ".join(src_group_names)
                if not ConfirmDialog.confirm(self, "Merge Groups",
                        f"Merge '{names}' into '{target_group}'?"):
                    return

        # Collect all moves
        item_moves = []
        cat_moves = []
        for src_data in source_data_list:
            if not src_data:
                continue
            src_kind = src_data[0]
            src_ai = src_data[1]
            if src_ai >= len(self.current_file.areas):
                continue
            src_area = self.current_file.areas[src_ai]

            if src_kind == "item":
                src_ci = src_data[2]
                if src_ci >= len(src_area.categories):
                    continue
                src_cat = src_area.categories[src_ci]
                ii = src_data[3]
                if ii < len(src_cat.items):
                    item = src_cat.items[ii]
                    if src_cat is not target_cat or target_group is not None:
                        item_moves.append((src_cat, item))
            elif src_kind == "group":
                src_ci = src_data[2]
                if src_ci >= len(src_area.categories):
                    continue
                src_cat = src_area.categories[src_ci]
                src_gn = src_data[3]
                for it in list(src_cat.items):
                    if it.group == src_gn:
                        item_moves.append((src_cat, it))
            elif src_kind == "cat":
                src_ci = src_data[2]
                if src_ci >= len(src_area.categories):
                    continue
                cat_to_move = src_area.categories[src_ci]
                if src_area is not target_area:
                    cat_moves.append((src_area, cat_to_move))

        # Apply moves
        moved = 0
        for src_cat, item in item_moves:
            if src_cat is target_cat and item.group == target_group:
                continue  # already in target group
            if item in src_cat.items:
                src_cat.items.remove(item)
            if target_group is not None:
                item.group = target_group
            if item not in target_cat.items:
                target_cat.items.append(item)
            moved += 1
        for src_area, cat_obj in cat_moves:
            if cat_obj in src_area.categories:
                src_area.categories.remove(cat_obj)
                target_area.categories.append(cat_obj)
                moved += len(cat_obj.items)

        if moved:
            self._set_dirty()
            self._rebuild_rig_tree()
            self._status.showMessage(f"Moved {moved} item(s) to '{target_area.name} › {target_cat.name}'")

    # -- Undo / Redo / Clipboard -----------------------------------------------

    def _focused_tree(self):
        """Return 'rig' or 'master' depending on which tree was last focused."""
        # Check live focus first
        if self._r_tree.hasFocus():
            return "rig"
        if self._m_tree.hasFocus():
            return "master"
        # Fall back to tracked value
        return self._last_focused_tree

    def _rig_undo(self):
        if not self._rig_undo_stack or not self.current_file:
            self._status.showMessage("Nothing to undo (rig)")
            return
        # Push current state to redo
        self._rig_redo_stack.append(
            json.dumps(self.current_file.to_json_data()))
        # Pop and restore
        snap = self._rig_undo_stack.pop()
        self._undo_suppress = True
        self.current_file.areas = InventoryFile._parse_json(json.loads(snap))
        self._rig_last_snap = snap
        self.dirty = True
        self._update_save_state()
        self._rebuild_rig_tree()
        self._undo_suppress = False
        self._status.showMessage(f"Undo (rig) — {len(self._rig_undo_stack)} remaining")

    def _rig_redo(self):
        if not self._rig_redo_stack or not self.current_file:
            self._status.showMessage("Nothing to redo (rig)")
            return
        self._rig_undo_stack.append(
            json.dumps(self.current_file.to_json_data()))
        snap = self._rig_redo_stack.pop()
        self._undo_suppress = True
        self.current_file.areas = InventoryFile._parse_json(json.loads(snap))
        self._rig_last_snap = snap
        self.dirty = True
        self._update_save_state()
        self._rebuild_rig_tree()
        self._undo_suppress = False
        self._status.showMessage(f"Redo (rig) — {len(self._rig_redo_stack)} remaining")

    def _master_undo(self):
        if not self._master_undo_stack or not self.master_list:
            self._status.showMessage("Nothing to undo (master)")
            return
        self._master_redo_stack.append(
            json.dumps(self.master_list.to_json_data()))
        snap = self._master_undo_stack.pop()
        self._undo_suppress = True
        data = json.loads(snap)
        self.master_list.categories = []
        for cat_obj in data.get("categories", []):
            cat = MasterCategory(cat_obj.get("name", "Uncategorized"))
            for item_obj in cat_obj.get("items", []):
                cat.items.append(MasterItem(
                    item_obj.get("name", ""),
                    item_obj.get("emsa_min", 1),
                    item_obj.get("group")))
            self.master_list.categories.append(cat)
        self._master_last_snap = snap
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()
        self._undo_suppress = False
        self._status.showMessage(f"Undo (master) — {len(self._master_undo_stack)} remaining")

    def _master_redo(self):
        if not self._master_redo_stack or not self.master_list:
            self._status.showMessage("Nothing to redo (master)")
            return
        self._master_undo_stack.append(
            json.dumps(self.master_list.to_json_data()))
        snap = self._master_redo_stack.pop()
        self._undo_suppress = True
        data = json.loads(snap)
        self.master_list.categories = []
        for cat_obj in data.get("categories", []):
            cat = MasterCategory(cat_obj.get("name", "Uncategorized"))
            for item_obj in cat_obj.get("items", []):
                cat.items.append(MasterItem(
                    item_obj.get("name", ""),
                    item_obj.get("emsa_min", 1),
                    item_obj.get("group")))
            self.master_list.categories.append(cat)
        self._master_last_snap = snap
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()
        self._update_master_visibility()
        self._undo_suppress = False
        self._status.showMessage(f"Redo (master) — {len(self._master_redo_stack)} remaining")

    def _smart_undo(self):
        self._do_undo()

    def _smart_redo(self):
        self._do_redo()

    def _smart_copy(self):
        try:
            if self._m_all_table.hasFocus() or self._m_missing_table.hasFocus():
                self._copy_cell()
                return
        except (AttributeError, RuntimeError):
            pass
        self._do_copy()

    def _smart_cut(self):
        self._do_cut()

    def _smart_paste(self):
        try:
            if self._m_all_table.hasFocus() or self._m_missing_table.hasFocus():
                self._paste_cell()
                return
        except (AttributeError, RuntimeError):
            pass
        self._do_paste()

    def _do_undo(self):
        ft = self._focused_tree()
        if ft == "rig":
            self._rig_undo()
        else:
            self._master_undo()

    def _do_redo(self):
        ft = self._focused_tree()
        if ft == "rig":
            self._rig_redo()
        else:
            self._master_redo()

    def _do_rename(self):
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        item = tree.currentItem()
        if item:
            tree._startRename(item)

    def _do_copy(self):
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        items = self._serialize_selected(tree, ft)
        if items:
            self._clipboard = {"items": items, "mode": "copy", "source": ft}
            self._status.showMessage(f"Copied {len(items)} item(s)")

    def _do_cut(self):
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        items = self._serialize_selected(tree, ft)
        if items:
            self._clipboard = {"items": items, "mode": "cut", "source": ft}
            self._status.showMessage(f"Cut {len(items)} item(s) — paste to move")

    def _do_paste(self):
        if not self._clipboard or not self._clipboard["items"]:
            self._status.showMessage("Nothing to paste")
            return
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        sel = tree.currentItem()

        # Determine target container
        target_cat = None
        target_group = None
        if sel:
            data = sel.data(0, Qt.ItemDataRole.UserRole)
            if data:
                kind = data[0]
                if kind == "item":
                    QMessageBox.warning(self, "Paste", "Cannot paste inside an item.\nSelect a category, group, or area.")
                    return
                target_cat, target_group = self._resolve_paste_target(ft, data)

        # If no target, create/find "Uncategorized"
        if target_cat is None:
            target_cat = self._get_or_create_uncategorized(ft)
            if target_cat is None:
                return

        clip_items = self._clipboard["items"]
        clip_source = self._clipboard["source"]
        is_cut = self._clipboard["mode"] == "cut"

        # Check for group-to-group merge
        if target_group is not None:
            src_groups = {ci.get("group") for ci in clip_items if ci.get("group")}
            src_groups.discard(target_group)
            src_groups.discard(None)
            if src_groups:
                names = ", ".join(sorted(src_groups))
                if not ConfirmDialog.confirm(self, "Merge Groups",
                        f"Merge '{names}' into '{target_group}'?"):
                    return

        # For cut: remove from source FIRST
        if is_cut:
            self._remove_cut_items(clip_items, clip_source)

        # Add to target
        pasted = 0
        for ci in clip_items:
            # Use target_group if pasting into a group, otherwise keep original
            group = target_group if target_group is not None else ci.get("group")
            if ft == "rig":
                target_cat.items.append(Item(
                    ci["name"], ci.get("qty", ci.get("emsa_min", 1)),
                    group))
            else:
                target_cat.items.append(MasterItem(
                    ci["name"], ci.get("emsa_min", ci.get("qty", 1)),
                    group))
            pasted += 1


        if is_cut:
            self._clipboard = None

        # Rebuild affected trees
        if ft == "rig" or (is_cut and clip_source == "rig"):
            self._set_dirty()
            self._rebuild_rig_tree()
        if ft == "master" or (is_cut and clip_source == "master"):
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._update_master_visibility()

        self._status.showMessage(f"Pasted {pasted} item(s)")

    def _classify_tree_selection(self, tree, tree_type):
        """Classify selected tree nodes into items and groups.
        Returns (items_list, groups_list) appropriate for the tree type.
        Master:  items=[(cat, item)],           groups=[(cat, group_name, [members])]
        Rig:     items=[(area, cat, item)],      groups=[(area, cat, group_name, [members])]
        """
        items_list = []
        groups_list = []
        for sel in tree.selectedItems():
            d = sel.data(0, Qt.ItemDataRole.UserRole)
            if not d:
                continue
            kind = d[0]
            if tree_type == "master" and self.master_list:
                ci = d[1]
                cat = self.master_list.categories[ci]
                if kind == "item":
                    items_list.append((cat, cat.items[d[2]]))
                elif kind == "group":
                    gn = d[2]
                    members = [it for it in cat.items if it.group == gn]
                    groups_list.append((cat, gn, members))
            elif tree_type == "rig" and self.current_file:
                ai = d[1]
                area = self.current_file.areas[ai]
                if kind == "item":
                    ci, ii = d[2], d[3]
                    cat = area.categories[ci]
                    items_list.append((area, cat, cat.items[ii]))
                elif kind == "group":
                    ci, gn = d[2], d[3]
                    cat = area.categories[ci]
                    members = [it for it in cat.items if it.group == gn]
                    groups_list.append((area, cat, gn, members))
        return items_list, groups_list

    def _get_category_names_for_move(self, tree_type, items_list, groups_list):
        """Return list of category names available as move targets.
        For master: all master categories.
        For rig: categories within the area of the first selected node."""
        if tree_type == "master" and self.master_list:
            return [c.name for c in self.master_list.categories]
        elif tree_type == "rig" and self.current_file:
            # Determine area from first selected item or group
            area = None
            if items_list:
                area = items_list[0][0]
            elif groups_list:
                area = groups_list[0][0]
            if area:
                return [c.name for c in area.categories]
        return []

    def _execute_move_to_category(self, tree_type, items_list, groups_list, cat_name):
        """Move items and/or group members to the named category."""
        moved = 0
        if tree_type == "master" and self.master_list:
            target_cat = None
            for c in self.master_list.categories:
                if c.name == cat_name:
                    target_cat = c
                    break
            if not target_cat:
                return
            # Move individual items
            for src_cat, item in items_list:
                if item in src_cat.items and src_cat is not target_cat:
                    src_cat.items.remove(item)
                    target_cat.items.append(item)
                    moved += 1
            # Move group members
            for src_cat, gn, members in groups_list:
                if src_cat is target_cat:
                    continue
                for item in list(members):
                    if item in src_cat.items:
                        src_cat.items.remove(item)
                        target_cat.items.append(item)
                        moved += 1
            if moved:
                self.dirty_master = True
                self._update_save_state()
                self._rebuild_master_tree()

        elif tree_type == "rig" and self.current_file:
            # Determine target area from first selection
            area = None
            if items_list:
                area = items_list[0][0]
            elif groups_list:
                area = groups_list[0][0]
            if not area:
                return
            target_cat = None
            for c in area.categories:
                if c.name == cat_name:
                    target_cat = c
                    break
            if not target_cat:
                return
            # Move individual items (within same area)
            for src_area, src_cat, item in items_list:
                if src_area is not area:
                    continue
                if item in src_cat.items and src_cat is not target_cat:
                    src_cat.items.remove(item)
                    target_cat.items.append(item)
                    moved += 1
            # Move group members (within same area)
            for src_area, src_cat, gn, members in groups_list:
                if src_area is not area:
                    continue
                if src_cat is target_cat:
                    continue
                for item in list(members):
                    if item in src_cat.items:
                        src_cat.items.remove(item)
                        target_cat.items.append(item)
                        moved += 1
            if moved:
                self._set_dirty()
                self._rebuild_rig_tree()

        if moved:
            self._status.showMessage(f"Moved {moved} item(s) to '{cat_name}'")

    def _do_move_to_category(self):
        """Ctrl+M — move selected items/groups to an existing category."""
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        items_list, groups_list = self._classify_tree_selection(tree, ft)
        if not items_list and not groups_list:
            self._status.showMessage("Select items or groups to move")
            return
        cat_names = self._get_category_names_for_move(ft, items_list, groups_list)
        if not cat_names:
            self._status.showMessage("No categories available")
            return
        dlg = MoveToCategoryDialog(cat_names, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            name = dlg.selected_category()
            if name:
                self._execute_move_to_category(ft, items_list, groups_list, name)

    def _do_move_to_new_category(self):
        """Ctrl+N — move selected items/groups to a new category."""
        ft = self._focused_tree()
        tree = self._r_tree if ft == "rig" else self._m_tree
        items_list, groups_list = self._classify_tree_selection(tree, ft)
        if not items_list and not groups_list:
            self._status.showMessage("Select items or groups to move")
            return
        name, ok = QInputDialog.getText(self, "Move to New Category",
            "New category name:")
        if not ok or not name.strip():
            return
        name = name.strip()
        # Create category if it doesn't exist
        if ft == "master" and self.master_list:
            if not any(c.name == name for c in self.master_list.categories):
                self.master_list.categories.append(MasterCategory(name))
        elif ft == "rig" and self.current_file:
            area = None
            if items_list:
                area = items_list[0][0]
            elif groups_list:
                area = groups_list[0][0]
            if area and not any(c.name == name for c in area.categories):
                area.categories.append(Category(name))
        self._execute_move_to_category(ft, items_list, groups_list, name)

    def _serialize_selected(self, tree, tree_type):
        """Serialize selected tree items to clipboard dicts."""
        items = []
        for sel in tree.selectedItems():
            data = sel.data(0, Qt.ItemDataRole.UserRole)
            if not data:
                continue
            kind = data[0]
            if tree_type == "rig" and self.current_file:
                ai = data[1]
                area = self.current_file.areas[ai]
                if kind == "item":
                    ci, ii = data[2], data[3]
                    it = area.categories[ci].items[ii]
                    items.append({"name": it.name, "qty": it.qty, "group": it.group,
                                  "_src": ("rig", ai, ci, ii)})
                elif kind == "group":
                    ci, gn = data[2], data[3]
                    for it in area.categories[ci].items:
                        if it.group == gn:
                            items.append({"name": it.name, "qty": it.qty, "group": it.group,
                                          "_src": ("rig", ai, ci, None)})
                elif kind == "cat":
                    ci = data[2]
                    for it in area.categories[ci].items:
                        items.append({"name": it.name, "qty": it.qty, "group": it.group,
                                      "_src": ("rig", ai, ci, None)})
            elif tree_type == "master" and self.master_list:
                ci = data[1]
                cat = self.master_list.categories[ci]
                if kind == "item":
                    ii = data[2]
                    it = cat.items[ii]
                    items.append({"name": it.name, "emsa_min": it.emsa_min, "group": it.group,
                                  "_src": ("master", ci, ii)})
                elif kind == "group":
                    gn = data[2]
                    for it in cat.items:
                        if it.group == gn:
                            items.append({"name": it.name, "emsa_min": it.emsa_min, "group": it.group,
                                          "_src": ("master", ci, None)})
                elif kind == "cat":
                    for it in cat.items:
                        items.append({"name": it.name, "emsa_min": it.emsa_min, "group": it.group,
                                      "_src": ("master", ci, None)})
        return items

    def _resolve_paste_target(self, tree_type, data):
        """Resolve a tree node to (Category, group_name_or_None) for pasting into."""
        kind = data[0]
        if tree_type == "rig" and self.current_file:
            ai = data[1]
            area = self.current_file.areas[ai]
            if kind == "cat":
                return area.categories[data[2]], None
            elif kind == "group":
                return area.categories[data[2]], data[3]  # ci, group_name
            elif kind == "area":
                if not area.categories:
                    area.categories.append(Category("General"))
                return area.categories[0], None
        elif tree_type == "master" and self.master_list:
            ci = data[1]
            if kind == "cat":
                return self.master_list.categories[ci], None
            elif kind == "group":
                return self.master_list.categories[ci], data[2]  # group_name
        return None, None

    def _get_or_create_uncategorized(self, tree_type):
        """Get or create an 'Uncategorized' container for paste with no selection."""
        if tree_type == "rig":
            if not self.current_file:
                return None
            for area in self.current_file.areas:
                for cat in area.categories:
                    if cat.name == "Uncategorized":
                        return cat
            # Create one in first area
            if not self.current_file.areas:
                self.current_file.areas.append(Area("Uncategorized"))
            cat = Category("Uncategorized")
            self.current_file.areas[0].categories.append(cat)
            return cat
        else:
            if not self.master_list:
                return None
            for cat in self.master_list.categories:
                if cat.name == "Uncategorized":
                    return cat
            cat = MasterCategory("Uncategorized")
            self.master_list.categories.append(cat)
            return cat

    def _remove_cut_items(self, clip_items, source_type):
        """Remove cut items from their source using stored source references."""
        if source_type == "rig" and self.current_file:
            # Group by (ai, ci) to remove from correct categories
            to_remove = {}  # (ai, ci) -> set of item names
            for ci_data in clip_items:
                src = ci_data.get("_src")
                if src and src[0] == "rig":
                    key = (src[1], src[2])  # (ai, ci)
                    to_remove.setdefault(key, set()).add(ci_data["name"])
            if to_remove:
                for (ai, ci), names in to_remove.items():
                    if ai < len(self.current_file.areas):
                        area = self.current_file.areas[ai]
                        if ci < len(area.categories):
                            cat = area.categories[ci]
                            cat.items = [it for it in cat.items if it.name not in names]
            else:
                # Fallback: remove by name globally
                names = {ci_data["name"] for ci_data in clip_items}
                for area in self.current_file.areas:
                    for cat in area.categories:
                        cat.items = [it for it in cat.items if it.name not in names]
        elif source_type == "master" and self.master_list:
            to_remove = {}  # ci -> set of item names
            for ci_data in clip_items:
                src = ci_data.get("_src")
                if src and src[0] == "master":
                    to_remove.setdefault(src[1], set()).add(ci_data["name"])
            if to_remove:
                for ci, names in to_remove.items():
                    if ci < len(self.master_list.categories):
                        cat = self.master_list.categories[ci]
                        cat.items = [it for it in cat.items if it.name not in names]
            else:
                names = {ci_data["name"] for ci_data in clip_items}
                for cat in self.master_list.categories:
                    cat.items = [it for it in cat.items if it.name not in names]

    def _set_dirty(self):
        self.dirty = True
        self._update_save_state()
        self._schedule_preview_refresh()

    def _add_rig_area(self):
        if not self.current_file: return
        n, ok = QInputDialog.getText(self, "Add Area", "Area name:")
        if ok and n.strip():
            self.current_file.areas.append(Area(n.strip()))
            self._set_dirty()
            self._rebuild_rig_tree()

    def _radd_item(self, cat):
        n, ok = QInputDialog.getText(self, "Add Item", "Item name:")
        if not ok or not n.strip(): return
        q, ok = QInputDialog.getInt(self, "Qty", "Quantity:", 1, 0, 9999)
        if not ok: return
        cat.items.append(Item(n.strip(), q))
        self._set_dirty()
        self._rebuild_rig_tree()

    def _radd_cat(self, area):
        n, ok = QInputDialog.getText(self, "Add Category", "Category name:")
        if ok and n.strip():
            area.categories.append(Category(n.strip()))
            self._set_dirty()
            self._rebuild_rig_tree()

    def _radd_group(self, cat):
        """Add a new group to a rig category (creates first item with group tag)."""
        group_name, ok = QInputDialog.getText(self, "Add Group", "Group name:")
        if not ok or not group_name.strip(): return
        group_name = group_name.strip()
        item_name, ok = QInputDialog.getText(self, "First Item", f"Item name for '{group_name}':")
        if not ok or not item_name.strip(): return
        q, ok = QInputDialog.getInt(self, "Qty", "Quantity:", 1, 0, 9999)
        if not ok: return
        cat.items.append(Item(item_name.strip(), q, group_name))
        self._set_dirty()
        self._rebuild_rig_tree()

    def _radd_item_to_group(self, cat, group_name):
        """Add an item pre-tagged with a group."""
        n, ok = QInputDialog.getText(self, "Add Item", f"Item name for '{group_name}':")
        if not ok or not n.strip(): return
        q, ok = QInputDialog.getInt(self, "Qty", "Quantity:", 1, 0, 9999)
        if not ok: return
        cat.items.append(Item(n.strip(), q, group_name))
        self._set_dirty()
        self._rebuild_rig_tree()

    def _qadd_master_group(self, cat):
        """Add a new group to a master category (creates first item with group tag)."""
        group_name, ok = QInputDialog.getText(self, "Add Group", "Group name:")
        if not ok or not group_name.strip(): return
        group_name = group_name.strip()
        item_name, ok = QInputDialog.getText(self, "First Item", f"Item name for '{group_name}':")
        if not ok or not item_name.strip(): return
        q, ok = QInputDialog.getInt(self, "EMSA Min", "EMSA minimum qty:", 1, 0, 9999)
        if not ok: return
        cat.items.append(MasterItem(item_name.strip(), q, group_name))
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()

    def _qadd_master_item_to_group(self, cat, group_name):
        """Add an item pre-tagged with a group to the master list."""
        n, ok = QInputDialog.getText(self, "Add Item", f"Item name for '{group_name}':")
        if not ok or not n.strip(): return
        q, ok = QInputDialog.getInt(self, "EMSA Min", "EMSA minimum qty:", 1, 0, 9999)
        if not ok: return
        cat.items.append(MasterItem(n.strip(), q, group_name))
        self.dirty_master = True
        self._update_save_state()
        self._rebuild_master_tree()

    # -- LEMSA PDF comparison ------------------------------------------------

    def _extract_pdf_items(self, pdf_path):
        try:
            import pdfplumber
        except ImportError:
            raise Exception("pdfplumber not installed. Run: pip3 install pdfplumber")
        items = []
        with pdfplumber.open(pdf_path) as pdf:
            for page in pdf.pages:
                tables = page.extract_tables()
                if tables:
                    for table in tables:
                        for row in table:
                            if not row or len(row) < 2: continue
                            cells = [c.strip() if c else "" for c in row]
                            name = None; qty = None
                            for cell in cells:
                                if not cell: continue
                                qty_match = re.match(r'^(\d+)\s*(each)?$', cell.strip(), re.I)
                                if qty_match and qty is None:
                                    qty = int(qty_match.group(1))
                                elif len(cell) > 2 and not cell.isdigit() and name is None:
                                    name = cell
                            if name and qty is not None:
                                name = re.sub(r'\s+', ' ', name).strip()
                                items.append((name, qty))
                else:
                    text = page.extract_text()
                    if not text: continue
                    for line in text.split("\n"):
                        line = line.strip()
                        if not line: continue
                        m = re.match(r'^(.+?)\s{2,}(\d+)\s*(each)?$', line, re.I)
                        if m:
                            n = m.group(1).strip()
                            if len(n) > 2: items.append((n, int(m.group(2))))
                            continue
                        m = re.match(r'^(.+?)\s*\|\s*(\d+)$', line)
                        if m:
                            n = m.group(1).strip()
                            if len(n) > 2: items.append((n, int(m.group(2))))
        seen = {}
        for name, qty in items:
            seen[name.lower()] = (name, qty)
        # Apply manual splits from lemsa_splits.json
        splits = self._load_splits()
        final = {}
        for key, (name, qty) in seen.items():
            if key in splits:
                for split_item in splits[key]["items"]:
                    skey = split_item["name"].lower()
                    final[skey] = (split_item["name"], split_item["qty"])
            else:
                final[key] = (name, qty)
        return list(final.values())

    def _compare_with_lemsas(self):
        if self._checking:
            self._status.showMessage("A check is already running.")
            return
        if not self.master_list:
            self._status.showMessage("No master list loaded.")
            return
        dl_dir = self._get_lemsa_dl_dir()
        if not dl_dir:
            self._status.showMessage("No LEMSA PDF directory set. Configure in LEMSA Equipment tab.")
            return

        # Step 1: Clear previous table edits and aliases
        self._save_table_edits({})
        self._save_name_aliases({})

        # Step 2: Check for updates first
        self._status.showMessage("Checking LEMSAs for updates before comparing...")
        self._check_lemsa_updates(callback=self._on_update_check_done)

    def _use_existing_compiled(self):
        """Load and display a previously compiled LEMSA item list."""
        if not self.master_list:
            self._status.showMessage("No master list loaded.")
            return
        cached = self._load_compiled_list()
        if not cached:
            self._status.showMessage("No compiled list found. Use 'Compile New' first.")
            return
        self._run_comparison_from_cache(cached)

    def _on_update_check_done(self, results):
        """Called after LEMSA update check completes."""
        changed = results.get("changed", []) + results.get("baselined", [])
        cached = self._load_compiled_list()

        if not changed and cached:
            # Nothing changed, use cached list
            self._status.showMessage("PDFs up to date — using cached comparison data.")
            self._run_comparison_from_cache(cached)
        else:
            # Something changed or no cache — re-extract
            reason = "PDFs updated" if changed else "No cached list"
            self._status.showMessage(f"{reason} — extracting items from PDFs...")
            self._run_extraction()

    def _run_extraction(self):
        dl_dir = self._get_lemsa_dl_dir()
        if not dl_dir:
            return
        pdfs = [f for f in os.listdir(dl_dir) if f.lower().endswith(".pdf")]
        if not pdfs:
            self._status.showMessage(f"No PDFs found in {dl_dir}")
            return

        self._show_progress(len(pdfs), f"Extracting 0/{len(pdfs)}...")

        worker = CompareWorker(self, pdfs, dl_dir)
        def _on_progress(step, total, msg):
            self._update_progress(step, msg)
        def _on_finished(data):
            self._hide_progress()
            # Save compiled list
            self._save_compiled_list(data["all_lemsa"])
            # Show results
            self._finalize_comparison(data["all_lemsa"], data["pdf_count"], data.get("errors", []))
        def _on_error(msg):
            self._hide_progress()
            self._status.showMessage(msg)
        worker.progress.connect(_on_progress)
        worker.finished.connect(_on_finished)
        worker.error.connect(_on_error)
        self._worker = worker
        worker.start()

    def _run_comparison_from_cache(self, all_lemsa):
        """Run comparison using cached extracted items, applying splits."""
        # Apply splits to cached data (splits may have been added after extraction)
        splits = self._load_splits()
        if splits:
            updated = {}
            for key, data in all_lemsa.items():
                if key in splits:
                    split_info = splits[key]
                    for split_item in split_info["items"]:
                        skey = split_item["name"].lower()
                        updated[skey] = {
                            "name": split_item["name"],
                            "qty": split_item["qty"],
                            "sources": data.get("sources", []),
                        }
                else:
                    updated[key] = data
            all_lemsa = updated

        pdf_count = len(set(
            s for data in all_lemsa.values()
            for s in data.get("sources", [])
        ))
        self._finalize_comparison(all_lemsa, pdf_count, [])

    def _finalize_comparison(self, all_lemsa, pdf_count, errors):
        """Compare extracted LEMSA items against master list and display."""
        # Filter out excluded items (status = Error)
        exclusions = self._load_exclusions()
        if exclusions:
            all_lemsa = {k: v for k, v in all_lemsa.items() if k not in exclusions}

        master_names = {}
        for cat, item in self.master_list.iter_all_items():
            master_names[item.name.lower()] = (cat.name, item)

        # Load name aliases for "Name Difference" items
        aliases = self._load_name_aliases()

        new_items = []
        qty_diffs = []
        alias_matched_master_keys = set()  # track master items matched via alias

        for key, data in sorted(all_lemsa.items(), key=lambda x: x[1]["name"].lower()):
            if key in master_names:
                # Direct match
                cat_name, master_item = master_names[key]
                if data["qty"] != master_item.emsa_min:
                    qty_diffs.append({
                        "name": master_item.name, "master_qty": master_item.emsa_min,
                        "lemsa_qty": data["qty"], "sources": data.get("sources", []),
                        "cat": cat_name, "item_ref": master_item,
                    })
            elif key in aliases:
                # Alias match — LEMSA name differs from master name
                alias = aliases[key]
                master_key = alias["master_name"].lower()
                if master_key in master_names:
                    cat_name, master_item = master_names[master_key]
                    alias_matched_master_keys.add(master_key)
                    if data["qty"] != master_item.emsa_min:
                        qty_diffs.append({
                            "name": master_item.name, "master_qty": master_item.emsa_min,
                            "lemsa_qty": data["qty"], "sources": data.get("sources", []),
                            "cat": cat_name, "item_ref": master_item,
                        })
                else:
                    # Alias target not in master (stale alias)
                    new_items.append(data)
            else:
                new_items.append(data)

        missing_items = []
        lemsa_keys = set(all_lemsa.keys())
        for key, (cat_name, item) in sorted(master_names.items(), key=lambda x: x[1][1].name.lower()):
            if key not in lemsa_keys and key not in alias_matched_master_keys:
                missing_items.append({"name": item.name, "cat": cat_name})

        if errors:
            self._status.showMessage(f"Extraction errors: {'; '.join(errors)}")

        self._show_comparison_results(new_items, missing_items, qty_diffs, pdf_count)

    def _show_comparison_results(self, new_items, missing_items, qty_diffs, pdf_count):
        self._m_lemsa_title.setText(f"LEMSA List ({pdf_count} PDFs)")

        # Make sure the LEMSA panel is visible
        if self._m_maximized_panel == "editor":
            self._toggle_master_panel("editor")

        # -- All Items table --
        all_rows = []
        master_names = {}
        for cat, item in self.master_list.iter_all_items():
            master_names[item.name.lower()] = (cat.name, item)

        # New items
        for data in new_items:
            all_rows.append({
                "name": data["name"],
                "lemsa_qty": data["qty"],
                "master_qty": "",
                "master_name": "",
                "sources": ", ".join(data.get("sources", [])),
                "category": "",
                "status": "No Match",
            })

        # Qty diffs
        for diff in qty_diffs:
            all_rows.append({
                "name": diff["name"],
                "lemsa_qty": diff["lemsa_qty"],
                "master_qty": diff["master_qty"],
                "master_name": diff["name"],
                "sources": ", ".join(diff.get("sources", [])),
                "category": diff["cat"],
                "status": "Qty Diff",
            })

        # Matches (direct + alias)
        new_keys = {d["name"].lower() for d in new_items}
        diff_master_keys = {d["name"].lower() for d in qty_diffs}
        aliases = self._load_name_aliases()
        cached = self._load_compiled_list()
        if cached:
            for key, data in cached.items():
                if key in new_keys:
                    continue
                # Direct match
                if key in master_names:
                    if key in diff_master_keys:
                        continue  # already shown as qty diff
                    cat_name, master_item = master_names[key]
                    all_rows.append({
                        "name": data["name"],
                        "lemsa_qty": data["qty"],
                        "master_qty": master_item.emsa_min,
                        "master_name": master_item.name,
                        "sources": ", ".join(data.get("sources", [])),
                        "category": cat_name,
                        "status": "Match",
                    })
                # Alias match
                elif key in aliases:
                    alias = aliases[key]
                    master_key = alias["master_name"].lower()
                    if master_key in diff_master_keys:
                        continue  # already shown as qty diff
                    if master_key in master_names:
                        cat_name, master_item = master_names[master_key]
                        all_rows.append({
                            "name": data["name"],
                            "lemsa_qty": data["qty"],
                            "master_qty": master_item.emsa_min,
                            "master_name": master_item.name,
                            "sources": ", ".join(data.get("sources", [])),
                            "category": cat_name,
                            "status": "Match",
                        })

        status_order = {"No Match": 0, "Qty Diff": 1, "Match": 2}
        all_rows.sort(key=lambda r: (status_order.get(r["status"], 9), r["name"].lower()))

        # Disconnect cellChanged during population
        try:
            self._m_all_table.cellChanged.disconnect(self._on_all_table_cell_changed)
        except TypeError:
            pass

        self._m_all_table.setSortingEnabled(False)
        self._m_all_table.setRowCount(len(all_rows))

        # Type color map
        type_colors = {
            "No Match": QColor("#74b9ff"),
            "Qty Diff": QColor("#fdcb6e"),
            "Match": QColor("#55efc4"),
        }
        # Per-cell backgrounds: readonly slightly lighter (faded), editable more prominent
        bg_editable_even = QBrush(QColor("#2a2a3c"))
        bg_editable_odd = QBrush(QColor("#252536"))
        bg_readonly_even = QBrush(QColor("#1e1e2e"))
        bg_readonly_odd = QBrush(QColor("#1a1a28"))

        # Build source→acronym map for agency display
        source_map = self._build_source_acronym_map()

        def _sources_to_acronyms(sources_str):
            """Convert comma-separated source string to acronym display + tooltip."""
            if not sources_str:
                return "", ""
            parts = [s.strip() for s in sources_str.split(",")]
            acronyms = []
            full_names = []
            for part in parts:
                info = source_map.get(part)
                if info:
                    acronyms.append(info["acronym"])
                    full_names.append(info["full_name"])
                else:
                    acronyms.append(part)
                    full_names.append(part)
            return ", ".join(acronyms), "\n".join(full_names)

        # Load saved edits to overlay
        saved_edits = self._load_table_edits()

        for i, row in enumerate(all_rows):
            acronym_display, agency_tooltip = _sources_to_acronyms(row["sources"])
            # col 0: Type, 1: Agency, 2: Item Name, 3: LEMSA Qty,
            # 4: Master Name, 5: Master Qty, 6: Category, 7: Status
            items = [
                QTableWidgetItem(row["status"]),            # 0 Type
                QTableWidgetItem(acronym_display),           # 1 Agency
                QTableWidgetItem(row["name"]),               # 2 Item Name
                QTableWidgetItem(str(row["lemsa_qty"])),     # 3 LEMSA Qty
                QTableWidgetItem(row["master_name"]),        # 4 Master Name
                QTableWidgetItem(str(row["master_qty"])),    # 5 Master Qty
                QTableWidgetItem(row["category"]),           # 6 Category
                QTableWidgetItem(""),                        # 7 Status
            ]
            # Qty Diff and Match rows get locked N/A status
            is_locked_status = row["status"] in ("Qty Diff", "Match")
            if is_locked_status:
                items[7].setText("N/A")

            # Overlay saved edits if present
            edit_key = row["name"].lower()
            is_exclude = False
            if edit_key in saved_edits:
                edits = saved_edits[edit_key]
                is_exclude = edits.get("status") == "Exclude"
                if not is_exclude:
                    if edits.get("master_name"):
                        items[4].setText(edits["master_name"])
                    if edits.get("master_qty"):
                        items[5].setText(edits["master_qty"])
                    if edits.get("category"):
                        items[6].setText(edits["category"])
                # Don't overlay status for locked rows
                if not is_locked_status and edits.get("status"):
                    items[7].setText(edits["status"])

            is_odd = i % 2 == 1
            for col, ti in enumerate(items):
                if col in (3, 5):
                    ti.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
                # Set background per cell
                if col in self._readonly_cols:
                    ti.setFlags(ti.flags() & ~Qt.ItemFlag.ItemIsEditable)
                    ti.setBackground(bg_readonly_odd if is_odd else bg_readonly_even)
                else:
                    ti.setBackground(bg_editable_odd if is_odd else bg_editable_even)
                # Type column color
                if col == 0:
                    color = type_colors.get(row["status"])
                    if color:
                        ti.setForeground(QBrush(color))
                # Agency tooltip: full LEMSA name(s)
                if col == 1 and agency_tooltip:
                    ti.setToolTip(agency_tooltip)
                # Lock status column for Qty Diff/Match rows
                if col == 7 and is_locked_status:
                    ti.setFlags(ti.flags() & ~Qt.ItemFlag.ItemIsEditable)
                    ti.setBackground(bg_readonly_odd if is_odd else bg_readonly_even)
                self._m_all_table.setItem(i, col, ti)
            # Lock cols 4-6 for Exclude rows
            if is_exclude:
                self._lock_exclude_row(i)
        self._m_all_table.setSortingEnabled(True)

        nomatch_count = sum(1 for r in all_rows if r["status"] == "No Match")
        diff_count = sum(1 for r in all_rows if r["status"] == "Qty Diff")
        self._m_lemsa_tabs.setTabText(0,
            f"All Items ({len(all_rows)}) — {nomatch_count} no match, {diff_count} qty diff")

        # -- Not in LEMSA table --
        self._m_missing_table.setSortingEnabled(False)
        self._m_missing_table.setRowCount(len(missing_items))
        for i, data in enumerate(sorted(missing_items, key=lambda d: d["name"].lower())):
            self._m_missing_table.setItem(i, 0, QTableWidgetItem(data["name"]))
            self._m_missing_table.setItem(i, 1, QTableWidgetItem(data["cat"]))
        self._m_missing_table.setSortingEnabled(True)
        self._m_lemsa_tabs.setTabText(1, f"Not in LEMSA ({len(missing_items)})")

        self._status.showMessage(
            f"Comparison: {nomatch_count} no match, {diff_count} qty diffs, "
            f"{len(missing_items)} not in LEMSA docs, {len(all_rows)} total items")

    def _apply_changes_to_master(self):
        """Apply table edits to the master list."""
        if not self.master_list:
            self._status.showMessage("No master list loaded.")
            return
        if self._m_all_table.rowCount() == 0:
            self._status.showMessage("No data in table. Load comparison first.")
            return

        added = 0
        updated = 0
        skipped = 0

        for row in range(self._m_all_table.rowCount()):
            status_item = self._m_all_table.item(row, 7)   # Status (designation)
            status = status_item.text().strip() if status_item else ""
            if status == "Optional":
                skipped += 1
                continue
            if status == "Exclude":
                skipped += 1
                continue

            master_name_item = self._m_all_table.item(row, 4)
            master_name = master_name_item.text().strip() if master_name_item else ""
            master_qty_item = self._m_all_table.item(row, 5)
            category_item = self._m_all_table.item(row, 6)
            category = category_item.text().strip() if category_item else ""

            try:
                qty = int(master_qty_item.text().strip()) if master_qty_item and master_qty_item.text().strip() else 0
            except ValueError:
                qty = 0

            if status == "New":
                # Add new item to master list
                item_name_item = self._m_all_table.item(row, 2)  # LEMSA Item Name
                new_name = master_name or (item_name_item.text().strip() if item_name_item else "")
                if not new_name or not category:
                    skipped += 1
                    continue
                # Find or create category
                target_cat = None
                for c in self.master_list.categories:
                    if c.name == category:
                        target_cat = c
                        break
                if not target_cat:
                    target_cat = MasterCategory(category)
                    self.master_list.categories.append(target_cat)
                # Check for duplicates across entire master list
                if new_name.lower() in {n.lower() for n in self.master_list.all_item_names()}:
                    skipped += 1
                    continue
                target_cat.items.append(MasterItem(new_name, qty))
                added += 1
            elif master_name:
                # Update existing master item
                cat_obj, master_item = self.master_list.find_item(master_name)
                if not master_item:
                    skipped += 1
                    continue
                changed = False
                if qty and qty != master_item.emsa_min:
                    master_item.emsa_min = qty
                    changed = True
                if category and cat_obj and category != cat_obj.name:
                    # Move to new category
                    new_cat = None
                    for c in self.master_list.categories:
                        if c.name == category:
                            new_cat = c
                            break
                    if not new_cat:
                        new_cat = MasterCategory(category)
                        self.master_list.categories.append(new_cat)
                    cat_obj.items.remove(master_item)
                    new_cat.items.append(master_item)
                    changed = True
                if changed:
                    updated += 1

        if added or updated:
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()

        # Rebuild alias file from current edits
        self._rebuild_aliases_from_edits()

        self._status.showMessage(
            f"Applied: {added} added, {updated} updated, {skipped} skipped")

    def _toggle_find_bar(self):
        """Toggle the find bar visibility."""
        if self._m_find_bar.isVisible():
            self._m_find_bar.hide()
            self._m_find_edit.clear()
        else:
            if self._tabs.currentWidget() != self._master_tab:
                self._tabs.setCurrentWidget(self._master_tab)
            self._m_find_bar.show()
            self._m_find_edit.setFocus()
            self._m_find_edit.selectAll()

    def _toggle_edit_dir(self):
        """Toggle edit advance direction between across and down."""
        if self._edit_dir == "across":
            self._edit_dir = "down"
            self._edit_dir_btn.setText("↓")
            self._edit_dir_btn.setToolTip("Edit direction: down (click to switch to across)")
        else:
            self._edit_dir = "across"
            self._edit_dir_btn.setText("→")
            self._edit_dir_btn.setToolTip("Edit direction: across (click to switch to down)")

    def _toggle_edit_scope(self):
        """Toggle edit advance scope between empty-only and all cells."""
        if self._edit_scope == "empty":
            self._edit_scope = "all"
            self._edit_scope_btn.setText("▣")
            self._edit_scope_btn.setToolTip("Edit scope: all cells (click to switch to empty only)")
        else:
            self._edit_scope = "empty"
            self._edit_scope_btn.setText("∅")
            self._edit_scope_btn.setToolTip("Edit scope: empty cells only (click to switch to all cells)")

    def _filter_lemsa_tables(self, text):
        """Filter both tables to show only rows matching the search text."""
        query = text.strip().lower()
        for row in range(self._m_all_table.rowCount()):
            match = not query
            if not match:
                for col in range(self._m_all_table.columnCount()):
                    cell = self._m_all_table.item(row, col)
                    if cell and query in cell.text().lower():
                        match = True
                        break
            self._m_all_table.setRowHidden(row, not match)
        for row in range(self._m_missing_table.rowCount()):
            match = not query
            if not match:
                for col in range(self._m_missing_table.columnCount()):
                    cell = self._m_missing_table.item(row, col)
                    if cell and query in cell.text().lower():
                        match = True
                        break
            self._m_missing_table.setRowHidden(row, not match)

    def _lock_exclude_row(self, row_idx):
        """Clear and lock cols 4-6 (Master Name, Master Qty, Category) for an Exclude row."""
        is_odd = row_idx % 2 == 1
        bg = QBrush(QColor("#1a1a28") if is_odd else QColor("#1e1e2e"))  # readonly dark bg
        for col in (4, 5, 6):
            cell = self._m_all_table.item(row_idx, col)
            if not cell:
                cell = QTableWidgetItem("")
                self._m_all_table.setItem(row_idx, col, cell)
            cell.setText("")
            cell.setFlags(cell.flags() & ~Qt.ItemFlag.ItemIsEditable)
            cell.setBackground(bg)

    def _unlock_exclude_row(self, row_idx):
        """Restore cols 4-6 to editable with editable background."""
        is_odd = row_idx % 2 == 1
        bg = QBrush(QColor("#252536") if is_odd else QColor("#2a2a3c"))  # editable dark bg
        for col in (4, 5, 6):
            cell = self._m_all_table.item(row_idx, col)
            if not cell:
                cell = QTableWidgetItem("")
                self._m_all_table.setItem(row_idx, col, cell)
            cell.setFlags(cell.flags() | Qt.ItemFlag.ItemIsEditable)
            cell.setBackground(bg)

    def eventFilter(self, obj, event):
        """Handle floating tooltips on viewport and keyboard navigation on table."""
        from PyQt6.QtCore import QEvent, QPoint

        # Search fields: down arrow jumps to paired tree
        if event.type() == QEvent.Type.KeyPress and event.key() == Qt.Key.Key_Down:
            tree_attr = getattr(obj, '_paired_tree', None)
            if tree_attr:
                tree = getattr(self, tree_attr, None)
                if tree and tree.topLevelItemCount() > 0:
                    tree.setFocus()
                    tree.setCurrentItem(tree.topLevelItem(0))
                    return True

        # Trees: up arrow from topmost item jumps to paired search
        if event.type() == QEvent.Type.KeyPress and event.key() == Qt.Key.Key_Up:
            search_attr = getattr(obj, '_paired_search', None)
            if search_attr and isinstance(obj, QTreeWidget):
                current = obj.currentItem()
                if current and current is obj.topLevelItem(0):
                    search = getattr(self, search_attr, None)
                    if search:
                        search.setFocus()
                        return True

        # Viewport: floating tooltip
        if hasattr(self, '_m_all_table') and obj == self._m_all_table.viewport():
            if event.type() == QEvent.Type.MouseMove:
                pos = event.position().toPoint()
                idx = self._m_all_table.indexAt(pos)
                if idx.isValid():
                    item = self._m_all_table.item(idx.row(), idx.column())
                    if item:
                        tip = item.toolTip() or item.text()
                        if tip:
                            self._show_float_tip(tip, event.globalPosition().toPoint() + QPoint(12, 20))
                            return False
                self._hide_float_tip()
            elif event.type() == QEvent.Type.Leave:
                self._hide_float_tip()
            elif event.type() == QEvent.Type.ToolTip:
                return True  # suppress default tooltip

        # Table: keyboard cell navigation (only when not editing)
        if hasattr(self, '_m_all_table') and obj == self._m_all_table and event.type() == QEvent.Type.KeyPress and self._editing_cell is None:
            row = self._m_all_table.currentRow()
            col = self._m_all_table.currentColumn()
            if row < 0:
                return super().eventFilter(obj, event)

            key = event.key()
            mods = event.modifiers()
            total_cols = self._m_all_table.columnCount()
            total_rows = self._m_all_table.rowCount()

            # Ctrl+C: copy cell text
            if key == Qt.Key.Key_C and mods & Qt.KeyboardModifier.ControlModifier:
                self._copy_cell()
                return True

            # Ctrl+V: paste into cell
            if key == Qt.Key.Key_V and mods & Qt.KeyboardModifier.ControlModifier:
                self._paste_cell()
                return True

            if key == Qt.Key.Key_Left:
                # Find previous editable cell in this row
                for c in range(col - 1, -1, -1):
                    if self._is_cell_editable(row, c):
                        self._m_all_table.setCurrentCell(row, c)
                        return True
                return True  # consume even if no target found

            elif key == Qt.Key.Key_Right:
                # Find next editable cell in this row
                for c in range(col + 1, total_cols):
                    if self._is_cell_editable(row, c):
                        self._m_all_table.setCurrentCell(row, c)
                        return True
                return True

            elif key == Qt.Key.Key_Up:
                # Move to same column in previous visible row
                for r in range(row - 1, -1, -1):
                    if not self._m_all_table.isRowHidden(r):
                        self._m_all_table.setCurrentCell(r, col)
                        return True
                return True

            elif key == Qt.Key.Key_Down:
                # Move to same column in next visible row
                for r in range(row + 1, total_rows):
                    if not self._m_all_table.isRowHidden(r):
                        self._m_all_table.setCurrentCell(r, col)
                        return True
                return True

            elif key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                self._begin_cell_edit(row, col)
                return True

            elif Qt.Key.Key_1 <= key <= Qt.Key.Key_4 and col == 7:
                # Status column: directly set value without opening editor
                status_options = ["", "New", "Optional", "Name Difference", "Exclude"]
                idx = key - Qt.Key.Key_1 + 1
                if idx < len(status_options) and self._is_cell_editable(row, col):
                    self._set_status_for_rows([row], status_options[idx])
                return True

            elif event.text() and event.text().isprintable() and not event.modifiers() & (
                    Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.AltModifier):
                # Printable key: start editing the current cell
                if self._is_cell_editable(row, col):
                    text = event.text()
                    self._m_all_table._suppress_popup = True
                    self._begin_cell_edit(row, col)
                    self._m_all_table._suppress_popup = False
                    # Defer key forwarding so editor is fully ready
                    from PyQt6.QtCore import QTimer
                    QTimer.singleShot(0, lambda t=text: self._forward_key_to_editor(t))
                    return True

        return super().eventFilter(obj, event)

    def _forward_key_to_editor(self, text):
        """Forward a printable character to the active editor widget."""
        editor = self._m_all_table.viewport().focusWidget()
        if not editor:
            return
        # For editable combo boxes, target the internal line edit
        if isinstance(editor, QComboBox) and editor.isEditable():
            line_edit = editor.lineEdit()
            if line_edit:
                line_edit.clear()
                line_edit.insert(text)
                return
        # For QComboBox (non-editable) or its line edit child
        if isinstance(editor, QLineEdit):
            editor.clear()
            editor.insert(text)
            return
        # Walk up to find a parent combo with a line edit
        p = editor.parent()
        while p:
            if isinstance(p, QComboBox) and p.isEditable():
                p.lineEdit().clear()
                p.lineEdit().insert(text)
                return
            p = p.parent()

    def _copy_cell(self):
        """Copy the text of the currently focused table cell to clipboard."""
        if self._tabs.currentWidget() != self._master_tab:
            return
        row = self._m_all_table.currentRow()
        col = self._m_all_table.currentColumn()
        if row < 0:
            return
        item = self._m_all_table.item(row, col)
        if item:
            QApplication.clipboard().setText(item.text())

    def _paste_cell(self):
        """Paste clipboard text into the currently focused editable table cell."""
        if self._tabs.currentWidget() != self._master_tab:
            return
        if self._editing_cell is not None:
            return  # already editing, let the editor handle paste
        row = self._m_all_table.currentRow()
        col = self._m_all_table.currentColumn()
        if row < 0:
            return
        if not self._is_cell_editable(row, col):
            return
        text = QApplication.clipboard().text()
        if not text:
            return
        self._edit_guard = True
        try:
            item = self._m_all_table.item(row, col)
            if not item:
                item = QTableWidgetItem("")
                self._m_all_table.setItem(row, col, item)
            item.setText(text)
            self._save_row_edit(row)
        finally:
            self._edit_guard = False

    def _show_float_tip(self, text, global_pos):
        """Show or update the floating tooltip label."""
        if not hasattr(self, '_float_tip'):
            self._float_tip = QLabel(self)
            self._float_tip.setWindowFlags(
                Qt.WindowType.ToolTip | Qt.WindowType.FramelessWindowHint)
            self._float_tip.setStyleSheet(
                "background-color: #313244; color: #cdd6f4; border: 1px solid #585b70;"
                " padding: 4px 8px; font-size: 12px;")
            self._float_tip.setWordWrap(True)
            self._float_tip.setMaximumWidth(400)
        self._float_tip.setText(text)
        self._float_tip.adjustSize()
        self._float_tip.move(global_pos)
        self._float_tip.show()

    def _hide_float_tip(self):
        """Hide the floating tooltip label."""
        if hasattr(self, '_float_tip') and self._float_tip.isVisible():
            self._float_tip.hide()

    # -- Table editing -------------------------------------------------------

    def _on_all_table_right_click(self, pos):
        """Context menu for the LEMSA comparison table."""
        idx = self._m_all_table.indexAt(pos)
        if not idx.isValid():
            return

        selected_rows = sorted(set(idx.row() for idx in self._m_all_table.selectedIndexes()))
        if not selected_rows:
            return

        # Filter to only rows whose status can be changed (not Qty Diff/Match)
        editable_rows = []
        for r in selected_rows:
            type_item = self._m_all_table.item(r, 0)
            if type_item and type_item.text().strip() in ("Qty Diff", "Match"):
                continue
            editable_rows.append(r)

        menu = QMenu(self)

        if len(selected_rows) == 1:
            row = selected_rows[0]
            name_item = self._m_all_table.item(row, 2)
            if not name_item:
                return
            name = name_item.text().strip()
            qty_item = self._m_all_table.item(row, 3)
            qty = 1
            if qty_item:
                try:
                    qty = int(qty_item.text().strip())
                except ValueError:
                    qty = 1
            agency_item = self._m_all_table.item(row, 1)
            agency_text = agency_item.text() if agency_item else ""
            agency_tip = agency_item.toolTip() if agency_item else ""
            menu.addAction(f"Split '{name}'…",
                lambda: self._split_table_item(row, name, qty, agency_text, agency_tip))
            menu.addSeparator()

        # Set Status submenu (only if there are editable rows)
        if editable_rows:
            count = len(editable_rows)
            label = f"Set Status ({count} items)" if count > 1 else "Set Status"
            status_menu = menu.addMenu(label)
            for status_val in ["", "New", "Optional", "Name Difference", "Exclude"]:
                display = status_val if status_val else "(clear)"
                status_menu.addAction(display,
                    lambda s=status_val, rows=list(editable_rows): self._set_status_for_rows(rows, s))

        if menu.isEmpty():
            return
        menu.exec(self._m_all_table.viewport().mapToGlobal(pos))

    def _set_status_for_rows(self, rows, status_value):
        """Set the status column for multiple rows and persist."""
        self._edit_guard = True
        self._m_all_table.setSortingEnabled(False)
        try:
            for r in rows:
                status_item = self._m_all_table.item(r, 7)
                if not status_item:
                    status_item = QTableWidgetItem("")
                    self._m_all_table.setItem(r, 7, status_item)

                old_status = status_item.text().strip()
                status_item.setText(status_value)

                # Lock/unlock for Exclude
                if status_value == "Exclude" and old_status != "Exclude":
                    self._lock_exclude_row(r)
                elif old_status == "Exclude" and status_value != "Exclude":
                    self._unlock_exclude_row(r)

                self._save_row_edit(r)
        finally:
            self._m_all_table.setSortingEnabled(True)
            self._edit_guard = False
        self._status.showMessage(f"Set status '{status_value or '(clear)'}' on {len(rows)} row(s)")

    def _split_table_item(self, row, name, qty, agency_text="", agency_tip=""):
        """Open split dialog and persist the result."""
        dlg = SplitDialog(name, qty, self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        new_items = dlg.get_items()
        if not new_items:
            return

        # Save to splits file (include agency)
        key = name.lower()
        splits = self._load_splits()
        splits[key] = {
            "original_name": name,
            "agency": agency_text,
            "agency_tooltip": agency_tip,
            "items": new_items,
        }
        self._save_splits(splits)

        # Remove original row
        self._m_all_table.removeRow(row)

        # Insert new rows at the same position
        for i, item_data in enumerate(new_items):
            insert_at = row + i
            self._m_all_table.insertRow(insert_at)
            type_item = QTableWidgetItem("No Match")
            type_item.setForeground(QBrush(QColor("#74b9ff")))
            agency_cell = QTableWidgetItem(agency_text)
            if agency_tip:
                agency_cell.setToolTip(agency_tip)
            cells = [
                type_item,
                agency_cell,                                       # Agency
                QTableWidgetItem(item_data["name"]),               # Item Name
                QTableWidgetItem(str(item_data["qty"])),           # LEMSA Qty
                QTableWidgetItem(""),                              # Master Name
                QTableWidgetItem(""),                              # Master Qty
                QTableWidgetItem(""),                              # Category
                QTableWidgetItem(""),                              # Status
            ]
            is_odd = insert_at % 2 == 1
            bg_ro_even = QBrush(QColor("#1e1e2e"))
            bg_ro_odd = QBrush(QColor("#1a1a28"))
            bg_ed_even = QBrush(QColor("#2a2a3c"))
            bg_ed_odd = QBrush(QColor("#252536"))
            for col, ci in enumerate(cells):
                if col in (3, 5):
                    ci.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
                if col in self._readonly_cols:
                    ci.setFlags(ci.flags() & ~Qt.ItemFlag.ItemIsEditable)
                    ci.setBackground(bg_ro_odd if is_odd else bg_ro_even)
                else:
                    ci.setBackground(bg_ed_odd if is_odd else bg_ed_even)
                self._m_all_table.setItem(insert_at, col, ci)

        self._status.showMessage(f"Split '{name}' into {len(new_items)} items")

    def _is_cell_editable(self, row, col):
        """Check if a cell can be edited (respects readonly cols, exclude rows, locked status)."""
        if col in self._readonly_cols:
            return False
        if self._m_all_table.isRowHidden(row):
            return False
        # Exclude rows: only Status col (7) is editable
        if col in (4, 5, 6):
            status_item = self._m_all_table.item(row, 7)
            if status_item and status_item.text().strip() == "Exclude":
                return False
        # Qty Diff/Match rows: Status col is locked to N/A
        if col == 7:
            type_item = self._m_all_table.item(row, 0)
            if type_item and type_item.text().strip() in ("Qty Diff", "Match"):
                return False
        return True

    def _begin_cell_edit(self, row, col):
        """Start editing a cell if it's editable. Used by double-click and keyboard."""
        if not self._is_cell_editable(row, col):
            return
        self._edit_guard = True
        self._editing_cell = (row, col)
        try:
            item = self._m_all_table.item(row, col)
            if not item:
                item = QTableWidgetItem("")
                self._m_all_table.setItem(row, col, item)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsEditable)
            self._m_all_table.setSortingEnabled(False)
            try:
                self._m_all_table.cellChanged.disconnect(self._on_all_table_cell_changed)
            except TypeError:
                pass
            self._m_all_table.cellChanged.connect(self._on_all_table_cell_changed)
            self._m_all_table.editItem(item)
        finally:
            self._edit_guard = False

    def _on_all_table_double_click(self, index):
        """Enable editing on double-click for editable columns."""
        self._begin_cell_edit(index.row(), index.column())

    def _on_editor_closed(self):
        """Called by ManagedTableWidget.closeEditor — editor is already gone.
        Cleans up state when editing ends without cellChanged firing (e.g. Escape).
        Also handles cleanup after auto-advanced edits."""
        if self._edit_guard:
            return  # cellChanged handler is managing the lifecycle
        # Editing ended without committing — clean up
        row = self._m_all_table.currentRow()
        col = self._m_all_table.currentColumn()
        self._editing_cell = None
        self._edit_guard = True
        try:
            # Remove editable flag from current cell
            item = self._m_all_table.item(row, col)
            if item:
                item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)
            # Re-enable sorting
            self._m_all_table.setSortingEnabled(True)
            # Disconnect cellChanged
            try:
                self._m_all_table.cellChanged.disconnect(self._on_all_table_cell_changed)
            except TypeError:
                pass
            # Restore focus to navigation mode
            self._m_all_table.setFocus()
            self._m_all_table.setCurrentCell(row, col)
        finally:
            self._edit_guard = False

    def _on_all_table_cell_changed(self, row, col):
        """After edit, auto-populate from master if Master Name changed, then advance."""
        if self._edit_guard:
            return
        self._edit_guard = True
        self._editing_cell = None

        try:
            item = self._m_all_table.item(row, col)
            if item:
                item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)

            # Sorting is disabled (done in _on_all_table_double_click),
            # so `row` from the signal is the correct index.

            # Auto-populate when Master Name (col 4) is selected
            if col == 4 and item:
                selected_name = item.text().strip()
                if selected_name:
                    filled = False
                    # Try master list first
                    if self.master_list:
                        cat_obj, master_item = self.master_list.find_item(selected_name)
                        if master_item and cat_obj:
                            qty_item = self._m_all_table.item(row, 5)
                            if not qty_item:
                                qty_item = QTableWidgetItem("")
                                self._m_all_table.setItem(row, 5, qty_item)
                            qty_item.setText(str(master_item.emsa_min))
                            cat_item = self._m_all_table.item(row, 6)
                            if not cat_item:
                                cat_item = QTableWidgetItem("")
                                self._m_all_table.setItem(row, 6, cat_item)
                            cat_item.setText(cat_obj.name)
                            filled = True
                    # Fallback: look for same Master Name in other table rows
                    if not filled:
                        name_lower = selected_name.lower()
                        for r in range(self._m_all_table.rowCount()):
                            if r == row:
                                continue
                            other_name = self._m_all_table.item(r, 4)
                            if other_name and other_name.text().strip().lower() == name_lower:
                                other_cat = self._m_all_table.item(r, 6)
                                if other_cat and other_cat.text().strip():
                                    cat_item = self._m_all_table.item(row, 6)
                                    if not cat_item:
                                        cat_item = QTableWidgetItem("")
                                        self._m_all_table.setItem(row, 6, cat_item)
                                    cat_item.setText(other_cat.text().strip())
                                    # Also copy qty if available
                                    other_qty = self._m_all_table.item(r, 5)
                                    if other_qty and other_qty.text().strip():
                                        qty_item = self._m_all_table.item(row, 5)
                                        if not qty_item:
                                            qty_item = QTableWidgetItem("")
                                            self._m_all_table.setItem(row, 5, qty_item)
                                        qty_item.setText(other_qty.text().strip())
                                    break

            # Persist editable columns (sorting is off, row is correct)
            self._save_row_edit(row)

            # Lock/unlock row if Status (col 7) changed to/from Exclude
            if col == 7 and item:
                if item.text().strip() == "Exclude":
                    self._lock_exclude_row(row)
                else:
                    self._unlock_exclude_row(row)

            # Re-enable sorting — the edited row may now move
            original_row = row
            self._m_all_table.setSortingEnabled(True)

            # Get post-sort row index
            if item:
                row = item.row()

            total_rows = self._m_all_table.rowCount()
            total_cols = self._m_all_table.columnCount()
            empty_only = self._edit_scope == "empty"

            def _is_candidate(r, c):
                if c in self._readonly_cols:
                    return False
                if self._m_all_table.isRowHidden(r):
                    return False
                # Skip cols 4-6 on Exclude rows
                if c in (4, 5, 6):
                    status_cell = self._m_all_table.item(r, 7)
                    if status_cell and status_cell.text().strip() == "Exclude":
                        return False
                # Skip col 7 on Qty Diff/Match rows (locked N/A)
                if c == 7:
                    type_cell = self._m_all_table.item(r, 0)
                    if type_cell and type_cell.text().strip() in ("Qty Diff", "Match"):
                        return False
                if not empty_only:
                    return True
                cell = self._m_all_table.item(r, c)
                return not cell or not cell.text().strip()

            def _row_is_complete(r):
                """Check if all editable cells in a row are filled."""
                for c in range(total_cols):
                    if c in self._readonly_cols:
                        continue
                    cell = self._m_all_table.item(r, c)
                    if not cell or not cell.text().strip():
                        return False
                return True

            # Determine if the edited row is complete
            status_cell = self._m_all_table.item(row, 7)
            status_text = status_cell.text().strip() if status_cell else ""
            skip_scroll = status_text in ("Exclude", "Optional", "N/A")
            edited_row_complete = skip_scroll or _row_is_complete(row)

            if edited_row_complete:
                # Row is done — focus the item now at the original position
                # (this is the row that slid into the sorted-away slot)
                advance_from_row = original_row
                if advance_from_row >= total_rows:
                    advance_from_row = total_rows - 1
                # Find first editable cell in that row or below
                target = None
                for nr in range(advance_from_row, total_rows):
                    for nc in range(total_cols):
                        if _is_candidate(nr, nc):
                            target = (nr, nc)
                            break
                    if target:
                        break
            else:
                # Row is incomplete — scroll to it and advance normally from edited cell
                self._m_all_table.scrollToItem(
                    item, QAbstractItemView.ScrollHint.PositionAtCenter)

                target = None
                if self._edit_dir == "across":
                    for nc in range(col + 1, total_cols):
                        if _is_candidate(row, nc):
                            target = (row, nc); break
                    if not target:
                        for nr in range(row + 1, total_rows):
                            for nc in range(total_cols):
                                if _is_candidate(nr, nc):
                                    target = (nr, nc); break
                            if target:
                                break
                else:  # down
                    for nr in range(row + 1, total_rows):
                        if _is_candidate(nr, col):
                            target = (nr, col); break
                    if not target:
                        for nc in range(col + 1, total_cols):
                            for nr in range(total_rows):
                                if _is_candidate(nr, nc):
                                    target = (nr, nc); break
                            if target:
                                break

            if target:
                r, c = target
                next_item = self._m_all_table.item(r, c)
                if not next_item:
                    next_item = QTableWidgetItem("")
                    self._m_all_table.setItem(r, c, next_item)
                next_item.setFlags(next_item.flags() | Qt.ItemFlag.ItemIsEditable)
                # Disable sorting before starting next edit
                self._m_all_table.setSortingEnabled(False)
                self._m_all_table.setCurrentCell(r, c)
                self._m_all_table.editItem(next_item)
            else:
                try:
                    self._m_all_table.cellChanged.disconnect(self._on_all_table_cell_changed)
                except TypeError:
                    pass
        finally:
            self._edit_guard = False

    # -- Simulate ------------------------------------------------------------

    def _simulate(self):
        if not self.current_file:
            self._status.showMessage("No file loaded to simulate.")
            return
        widget_path = os.path.join(self.repo_root, "widgets", "ems-inventory-checklist.html")
        if not os.path.isfile(widget_path):
            self._status.showMessage(f"Widget not found: {widget_path}")
            return
        try:
            with open(widget_path, "r", encoding="utf-8") as f:
                html = f.read()
            json_content = json.dumps(self.current_file.to_json_data())
            m = re.search(r"var\s+DEFAULT_INVENTORY\s*=\s*[\s\S]*?;", html)
            if m:
                replacement = f"var DEFAULT_INVENTORY = JSON.stringify({json_content});"
                html = html[:m.start()] + replacement + html[m.end():]
            html = re.sub(r'<script\s+[^>]*src=["\'][^"\']*jotfor[^"\']*["\'][^>]*>\s*</script>',
                          '', html, flags=re.IGNORECASE)
            tmp = tempfile.NamedTemporaryFile(suffix=".html", delete=False, mode="w", encoding="utf-8")
            tmp.write(html)
            tmp.close()
            webbrowser.open(f"file://{tmp.name}")
            self._status.showMessage(f"Simulating {self.current_file.filename}...")
        except Exception as e:
            self._status.showMessage(f"Simulate error: {e}")

    # -- Preview panel -------------------------------------------------------

    def _get_widget_html_template(self):
        """Load and cache the widget HTML with JotForm scripts stripped."""
        if self._preview_html_cache is not None:
            return self._preview_html_cache
        widget_path = os.path.join(self.repo_root, "widgets", "ems-inventory-checklist.html")
        if not os.path.isfile(widget_path):
            return None
        with open(widget_path, "r", encoding="utf-8") as f:
            html = f.read()
        # Strip JotForm script tags (widget won't be in an iframe)
        html = re.sub(r'<script\s+[^>]*src=["\'][^"\']*jotfor[^"\']*["\'][^>]*>\s*</script>',
                      '', html, flags=re.IGNORECASE)
        self._preview_html_cache = html
        return html

    def _schedule_preview_refresh(self):
        """Debounced preview refresh — restarts the 500ms timer."""
        if self._preview_web is not None:
            self._preview_timer.start()

    def _refresh_preview(self):
        """Inject current inventory data into widget HTML and load into preview."""
        if self._preview_web is None or not self.current_file:
            return
        html = self._get_widget_html_template()
        if not html:
            return
        try:
            json_content = json.dumps(self.current_file.to_json_data())
            m = re.search(r"var\s+DEFAULT_INVENTORY\s*=\s*[\s\S]*?;", html)
            if m:
                injected = html[:m.start()] + \
                    f"var DEFAULT_INVENTORY = JSON.stringify({json_content});" + \
                    html[m.end():]
            else:
                injected = html
            # Write to a temp file so QWebEngine can load it with proper file:// context
            tmp_path = os.path.join(tempfile.gettempdir(), "ems_editor_preview.html")
            with open(tmp_path, "w", encoding="utf-8") as f:
                f.write(injected)
            self._preview_web.setUrl(QUrl.fromLocalFile(tmp_path))
        except Exception as e:
            self._status.showMessage(f"Preview error: {e}")

    # -- Save ----------------------------------------------------------------

    def _update_save_state(self):
        enabled = self.dirty or self.dirty_master
        self._save_action.setEnabled(enabled)
        base = f"EMS Inventory Editor v{VERSION}"
        self.setWindowTitle(f"● {base}" if enabled else base)
        if self.dirty:
            self._schedule_preview_refresh()

    def _save_all(self):
        errors = []
        if self.dirty_master and self.master_list:
            try:
                self.master_list.save()
            except Exception as e:
                errors.append(f"Master: {e}")
        if self.dirty:
            for rf in self.rig_files:
                try:
                    rf.save()
                except Exception as e:
                    errors.append(f"{rf.filename}: {e}")
        if errors:
            self._status.showMessage(f"Save errors: {'; '.join(errors)}")
        else:
            parts = []
            if self.dirty_master:
                parts.append("master list")
            if self.dirty:
                parts.append(f"{len(self.rig_files)} rig file(s)")
            self._status.showMessage(f"Saved {', '.join(parts)}")
        self.dirty = False
        self.dirty_master = False
        self._update_save_state()

    def closeEvent(self, event):
        if self.dirty or self.dirty_master:
            if not ConfirmDialog.confirm(self, "Unsaved Changes",
                "Discard unsaved changes?"):
                event.ignore()
                return
        self._save_ui_state()
        event.accept()


def _generate_branch_images():
    """Generate tree branch connector and arrow images, return temp dir path."""
    d = os.path.join(tempfile.gettempdir(), "ems_editor_branch")
    os.makedirs(d, exist_ok=True)
    sz = 20  # image size matches tree indentation
    line_color = QColor("#585b70")
    arrow_color = QColor("#a6adc8")

    def _make_pixmap():
        px = QPixmap(sz, sz)
        px.fill(QColor(0, 0, 0, 0))
        return px

    def _dotted_pen():
        pen = QPen(line_color)
        pen.setStyle(Qt.PenStyle.DotLine)
        pen.setWidth(1)
        return pen

    # vline: vertical dotted line through center (has siblings, no item)
    px = _make_pixmap()
    p = QPainter(px)
    p.setPen(_dotted_pen())
    p.drawLine(sz // 2, 0, sz // 2, sz)
    p.end()
    px.save(os.path.join(d, "vline.png"))

    # branch-more: T-connector (vertical + horizontal to right)
    px = _make_pixmap()
    p = QPainter(px)
    p.setPen(_dotted_pen())
    p.drawLine(sz // 2, 0, sz // 2, sz)       # vertical through
    p.drawLine(sz // 2, sz // 2, sz, sz // 2)  # horizontal to right
    p.end()
    px.save(os.path.join(d, "branch-more.png"))

    # branch-end: L-connector (half vertical + horizontal to right)
    px = _make_pixmap()
    p = QPainter(px)
    p.setPen(_dotted_pen())
    p.drawLine(sz // 2, 0, sz // 2, sz // 2)   # vertical top to center
    p.drawLine(sz // 2, sz // 2, sz, sz // 2)   # horizontal to right
    p.end()
    px.save(os.path.join(d, "branch-end.png"))

    # arrow-closed: [+] box with dotted border
    px = _make_pixmap()
    p = QPainter(px)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
    box_pen = QPen(line_color)
    box_pen.setStyle(Qt.PenStyle.DotLine)
    box_pen.setWidth(1)
    p.setPen(box_pen)
    bx, by, bsz = 3, 4, 12
    p.drawRect(bx, by, bsz, bsz)
    # + sign
    plus_pen = QPen(arrow_color)
    plus_pen.setWidth(1)
    p.setPen(plus_pen)
    mid_x = bx + bsz // 2
    mid_y = by + bsz // 2
    p.drawLine(bx + 3, mid_y, bx + bsz - 3, mid_y)       # horizontal
    p.drawLine(mid_x, by + 3, mid_x, by + bsz - 3)         # vertical
    p.end()
    px.save(os.path.join(d, "arrow-closed.png"))

    # arrow-open: [-] box with dotted border
    px = _make_pixmap()
    p = QPainter(px)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
    p.setPen(box_pen)
    p.drawRect(bx, by, bsz, bsz)
    # - sign
    p.setPen(plus_pen)
    p.drawLine(bx + 3, mid_y, bx + bsz - 3, mid_y)       # horizontal only
    p.end()
    px.save(os.path.join(d, "arrow-open.png"))

    return d


if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    branch_dir = _generate_branch_images()
    _init_icons()
    # Paths for stylesheet (forward slashes for Qt CSS on all platforms)
    bp = branch_dir.replace("\\", "/")
    # Dark palette so Fusion draws widgets in dark colors
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#1e1e2e"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#cdd6f4"))
    palette.setColor(QPalette.ColorRole.Base, QColor("#1e1e2e"))
    palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#313244"))
    palette.setColor(QPalette.ColorRole.Text, QColor("#cdd6f4"))
    palette.setColor(QPalette.ColorRole.Button, QColor("#313244"))
    palette.setColor(QPalette.ColorRole.ButtonText, QColor("#cdd6f4"))
    palette.setColor(QPalette.ColorRole.Highlight, QColor("#3b5998"))
    palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#f0f0f0"))
    palette.setColor(QPalette.ColorRole.Mid, QColor("#585b70"))
    app.setPalette(palette)
    app.setStyleSheet("""
        /* === Catppuccin Mocha Base === */
        QMainWindow, QWidget {
            background-color: #1e1e2e;
            color: #cdd6f4;
        }
        QLabel {
            color: #cdd6f4;
        }
        QLabel a {
            color: #89b4fa;
        }

        /* === Inputs === */
        QLineEdit, QSpinBox, QComboBox {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
            border-radius: 4px;
            padding: 4px 6px;
            selection-background-color: #3b5998;
            selection-color: #f0f0f0;
        }
        QLineEdit:focus, QSpinBox:focus, QComboBox:focus {
            border-color: #89b4fa;
        }
        QLineEdit:disabled, QSpinBox:disabled, QComboBox:disabled {
            background-color: #181825;
            color: #6c7086;
        }

        /* === ComboBox dropdown list === */
        QComboBox QAbstractItemView {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
            selection-background-color: #3b5998;
            selection-color: #f0f0f0;
        }

        /* === Buttons === */
        QPushButton {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
            border-radius: 4px;
            padding: 5px 14px;
        }
        QPushButton:hover {
            background-color: #45475a;
            border-color: #585b70;
        }
        QPushButton:pressed {
            background-color: #585b70;
        }
        QPushButton:disabled {
            background-color: #181825;
            color: #6c7086;
            border-color: #313244;
        }
        /* Small icon buttons (clear, maximize, find) */
        QPushButton[flat="true"], QPushButton[iconBtn="true"] {
            padding: 2px;
        }

        /* === Checkbox === */
        QCheckBox {
            color: #cdd6f4;
            spacing: 6px;
        }
        QCheckBox::indicator {
            width: 16px;
            height: 16px;
            border: 1px solid #45475a;
            border-radius: 3px;
            background-color: #313244;
        }
        QCheckBox::indicator:checked {
            background-color: #89b4fa;
            border-color: #89b4fa;
        }
        QCheckBox::indicator:hover {
            border-color: #89b4fa;
        }

        /* === Menu Bar === */
        QMenuBar {
            background-color: #181825;
            color: #cdd6f4;
            border-bottom: 1px solid #45475a;
            padding: 2px;
        }
        QMenuBar::item {
            background-color: transparent;
            padding: 4px 10px;
            border-radius: 4px;
        }
        QMenuBar::item:selected {
            background-color: #313244;
        }
        QMenuBar::item:pressed {
            background-color: #45475a;
        }

        /* === Tabs === */
        QTabWidget::pane {
            border: 1px solid #45475a;
            background-color: #1e1e2e;
        }
        QTabBar::tab {
            background-color: #181825;
            color: #a6adc8;
            border: 1px solid #45475a;
            border-bottom: none;
            padding: 6px 16px;
            margin-right: 2px;
            border-top-left-radius: 4px;
            border-top-right-radius: 4px;
        }
        QTabBar::tab:selected {
            background-color: #1e1e2e;
            color: #cdd6f4;
            border-bottom: 2px solid #89b4fa;
        }
        QTabBar::tab:hover:!selected {
            background-color: #313244;
            color: #cdd6f4;
        }

        /* === Tree Widget === */
        QTreeWidget {
            background-color: #1e1e2e;
            alternate-background-color: #1a1a28;
            color: #cdd6f4;
            border: 1px solid #45475a;
            outline: none;
        }
        QTreeWidget::item {
            padding: 2px 0px;
            min-height: 22px;
        }
        QTreeWidget QLineEdit {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #89b4fa;
            border-radius: 2px;
            padding: 2px 4px;
            min-height: 18px;
            selection-background-color: #3b5998;
            selection-color: #f0f0f0;
        }
        QTreeWidget::item:selected {
            background-color: #3b5998;
            color: #f0f0f0;
        }
        QTreeWidget::item:hover:!selected {
            background-color: #313244;
        }
        QTreeWidget::branch {
            background-color: #1e1e2e;
        }
        QTreeWidget::branch:selected {
            background-color: #3b5998;
        }
        QTreeWidget::branch:hover:!selected {
            background-color: #313244;
        }
        QTreeWidget::branch:has-siblings:!adjoins-item {
            border-image: url(""" + bp + """/vline.png) 0;
        }
        QTreeWidget::branch:has-siblings:adjoins-item {
            border-image: url(""" + bp + """/branch-more.png) 0;
        }
        QTreeWidget::branch:!has-children:!has-siblings:adjoins-item {
            border-image: url(""" + bp + """/branch-end.png) 0;
        }
        QTreeWidget::branch:has-children:!has-siblings:closed,
        QTreeWidget::branch:closed:has-children:has-siblings {
            image: url(""" + bp + """/arrow-closed.png);
        }
        QTreeWidget::branch:open:has-children:!has-siblings,
        QTreeWidget::branch:open:has-children:has-siblings {
            image: url(""" + bp + """/arrow-open.png);
        }
        QTreeWidget {
            show-decoration-selected: 1;
        }
        QHeaderView::section {
            background-color: #181825;
            color: #bac2de;
            border: 1px solid #45475a;
            padding: 4px;
            font-weight: bold;
        }

        /* === Table Widget === */
        QTableWidget {
            background-color: #1e1e2e;
            alternate-background-color: #1a1a28;
            color: #cdd6f4;
            gridline-color: #45475a;
            border: 1px solid #45475a;
            outline: none;
        }
        QTableWidget::item:selected {
            background-color: #3b5998;
            color: #f0f0f0;
        }
        QTableWidget::item:focus {
            border: 2px solid #89b4fa;
        }

        /* === Scroll Area === */
        QScrollArea {
            background-color: #1e1e2e;
            border: 1px solid #45475a;
        }
        QScrollArea > QWidget > QWidget {
            background-color: #1e1e2e;
        }

        /* === Scrollbars === */
        QScrollBar:vertical {
            background-color: #181825;
            width: 12px;
            margin: 0;
        }
        QScrollBar::handle:vertical {
            background-color: #45475a;
            min-height: 24px;
            border-radius: 4px;
            margin: 2px;
        }
        QScrollBar::handle:vertical:hover {
            background-color: #585b70;
        }
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
            height: 0;
        }
        QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
            background: none;
        }
        QScrollBar:horizontal {
            background-color: #181825;
            height: 12px;
            margin: 0;
        }
        QScrollBar::handle:horizontal {
            background-color: #45475a;
            min-width: 24px;
            border-radius: 4px;
            margin: 2px;
        }
        QScrollBar::handle:horizontal:hover {
            background-color: #585b70;
        }
        QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {
            width: 0;
        }
        QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {
            background: none;
        }

        /* === Splitter === */
        QSplitter::handle {
            background-color: #45475a;
        }
        QSplitter::handle:horizontal {
            width: 3px;
        }
        QSplitter::handle:vertical {
            height: 3px;
        }
        QSplitter::handle:hover {
            background-color: #89b4fa;
        }

        /* === Status Bar === */
        QStatusBar {
            background-color: #181825;
            color: #a6adc8;
            border-top: 1px solid #45475a;
        }

        /* === Progress Bar === */
        QProgressBar {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
            border-radius: 4px;
            text-align: center;
        }
        QProgressBar::chunk {
            background-color: #89b4fa;
            border-radius: 3px;
        }

        /* === Menu === */
        QMenu {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
        }
        QMenu::item {
            padding: 5px 30px 5px 20px;
        }
        QMenu::item:selected {
            background-color: #3b5998;
            color: #f0f0f0;
        }
        QMenu::separator {
            height: 1px;
            background-color: #45475a;
            margin: 4px 8px;
        }
        QMenu::item:disabled {
            color: #6c7086;
        }

        /* === Group Box === */
        QGroupBox {
            color: #cdd6f4;
            border: 1px solid #45475a;
            border-radius: 4px;
            margin-top: 8px;
            padding-top: 8px;
        }
        QGroupBox::title {
            subcontrol-origin: margin;
            left: 10px;
            padding: 0 4px;
        }

        /* === Dialog === */
        QDialog {
            background-color: #1e1e2e;
            color: #cdd6f4;
        }
        QDialogButtonBox QPushButton {
            min-width: 70px;
        }

        /* === Message Box === */
        QMessageBox {
            background-color: #1e1e2e;
            color: #cdd6f4;
        }

        /* === Frame separator === */
        QFrame[frameShape="5"] {
            color: #45475a;
        }

        /* === Completer popup === */
        QListView {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #45475a;
            selection-background-color: #3b5998;
            selection-color: #f0f0f0;
        }

        /* === ToolTip === */
        QToolTip {
            background-color: #313244;
            color: #cdd6f4;
            border: 1px solid #585b70;
            padding: 4px 8px;
        }

        /* === Input Dialog === */
        QInputDialog {
            background-color: #1e1e2e;
            color: #cdd6f4;
        }
    """)
    window = App()
    window.show()
    window.raise_()
    window.activateWindow()
    sys.exit(app.exec())
