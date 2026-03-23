#!/usr/bin/env python3
"""
EMS Inventory Markdown Editor v2.0.0
A GUI tool for managing EMS inventory checklist markdown files
with a master list as the canonical item registry.

Place this file in the root of your GitHub Pages repo (parent of
data/checklists/{rig}/*.md) and run it. The master list should be at
data/checklists/master_list.md
"""

import os
import sys
import re
import shutil
import tempfile
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
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
from collections import defaultdict
from copy import deepcopy
import html as html_module

VERSION = "2.5.0"

# == LEMSA directory ==========================================================

LEMSA_DATA = [
    {"name": "Alameda County EMS", "counties": ["Alameda"], "url": "https://ems.acgov.org/"},
    {"name": "Central California EMS Agency", "counties": ["Fresno", "Kings", "Madera", "Tulare"], "url": "https://www.fresnocountyca.gov/Departments/Public-Health/Emergency-Services"},
    {"name": "Coastal Valleys EMS Agency", "counties": ["Mendocino", "Sonoma"], "url": "https://www.coastalvalleysems.org/"},
    {"name": "Contra Costa EMS Agency", "counties": ["Contra Costa"], "url": "https://www.cchealth.org/about-contra-costa-health/divisions/ems"},
    {"name": "El Dorado County EMS Agency", "counties": ["El Dorado"], "url": "https://www.eldoradocounty.ca.gov/Public-Safety-Justice/Emergency-Medical-Services"},
    {"name": "Imperial County EMS Agency", "counties": ["Imperial"], "url": "https://www.icphd.org/emergency-medical-services/"},
    {"name": "Inland Counties Emergency Medical Agency (ICEMA)", "counties": ["Inyo", "Mono", "San Bernardino"], "url": "https://icema.sbcounty.gov/"},
    {"name": "Kern County EMS Agency", "counties": ["Kern"], "url": "https://www.kernpublichealth.com/emergency-medical-services"},
    {"name": "Los Angeles County EMS Agency", "counties": ["Los Angeles"], "url": "https://dhs.lacounty.gov/emergency-medical-services-agency/"},
    {"name": "Marin County EMS Agency", "counties": ["Marin"], "url": "https://ems.marinhhs.org/"},
    {"name": "Merced County EMS Agency", "counties": ["Merced"], "url": "https://www.countyofmerced.com/2261/Emergency-Medical-Services"},
    {"name": "Monterey County EMS Agency", "counties": ["Monterey"], "url": "https://www.co.monterey.ca.us/government/departments-a-h/health/emergency-medical-services"},
    {"name": "Mountain Counties EMS Agency (MCEMSA)", "counties": ["Alpine", "Amador", "Calaveras", "Mariposa"], "url": "https://www.mvemsa.org/"},
    {"name": "Napa County EMS Agency", "counties": ["Napa"], "url": "https://www.napacounty.gov/756/Emergency-Medical-Services-EMS-Agency"},
    {"name": "North Coast EMS", "counties": ["Del Norte", "Humboldt", "Lake"], "url": "http://www.northcoastems.com/"},
    {"name": "Northern California EMS Inc.", "counties": ["Lassen", "Modoc", "Plumas", "Sierra", "Trinity"], "url": "https://norcalems.org/"},
    {"name": "Orange County EMS Agency", "counties": ["Orange"], "url": "https://www.ochealthinfo.com/providers-partners/emergency-medical-services"},
    {"name": "Riverside County EMS Agency", "counties": ["Riverside"], "url": "https://www.rivcoems.org/"},
    {"name": "Sacramento County EMS Agency", "counties": ["Sacramento"], "url": "https://dhs.saccounty.gov/PUB/EMS/Pages/EMS-Home.aspx"},
    {"name": "San Benito County EMS Agency", "counties": ["San Benito"], "url": "https://www.cosb.us/departments/office-of-emergency-services-oes-and-emergency-medical-services/emergency-medical-services-ems"},
    {"name": "San Diego County EMS Agency", "counties": ["San Diego"], "url": "https://www.sandiegocounty.gov/content/sdc/ems.html"},
    {"name": "San Francisco EMS Agency", "counties": ["San Francisco"], "url": "https://sf.gov/departments/department-emergency-management/emergency-medical-services-agency"},
    {"name": "San Joaquin EMS Agency", "counties": ["San Joaquin"], "url": "https://www.sjgov.org/department/ems"},
    {"name": "San Luis Obispo County EMS Agency", "counties": ["San Luis Obispo"], "url": "https://www.slocounty.ca.gov/Departments/Health-Agency/Public-Health/Emergency-Medical-Services/Emergency-Medical-Services-Agency.aspx"},
    {"name": "San Mateo County EMS Agency", "counties": ["San Mateo"], "url": "https://www.smchealth.org/ems"},
    {"name": "Santa Barbara County EMS Agency", "counties": ["Santa Barbara"], "url": "https://www.countyofsb.org/412/Emergency-Medical-Services"},
    {"name": "Santa Clara County EMS Agency", "counties": ["Santa Clara"], "url": "https://emsagency.sccgov.org/home"},
    {"name": "Santa Cruz County EMS Agency", "counties": ["Santa Cruz"], "url": "https://www.santacruzhealth.org/HSAHome/HSADivisions/PublicHealth/EmergencyMedicalServices.aspx"},
    {"name": "Sierra-Sacramento Valley EMS Agency", "counties": ["Butte", "Colusa", "Glenn", "Nevada", "Placer", "Shasta", "Siskiyou", "Sutter", "Tehama", "Yuba"], "url": "https://www.ssvems.com/"},
    {"name": "Solano County EMS Agency", "counties": ["Solano"], "url": "https://www.solanocounty.com/depts/ems/default.asp"},
    {"name": "Stanislaus County EMS Agency", "counties": ["Stanislaus"], "url": "https://stanems.com/"},
    {"name": "Tuolumne County EMS Agency", "counties": ["Tuolumne"], "url": "https://www.tuolumnecounty.ca.gov/302/Emergency-Medical-Services"},
    {"name": "Ventura County EMS Agency", "counties": ["Ventura"], "url": "https://vchca.org/ems"},
    {"name": "Yolo County EMS Agency", "counties": ["Yolo"], "url": "https://www.yolocounty.org/government/general-government-departments/health-human-services/providers-partners/yolo-emergency-medical-services-agency-yemsa"},
]

# == Data model ==============================================================

class Item:
    __slots__ = ("name", "qty")
    def __init__(self, name, qty):
        self.name = name
        self.qty = qty

class Category:
    __slots__ = ("name", "items", "is_subcat")
    def __init__(self, name, is_subcat=False):
        self.name = name
        self.items = []
        self.is_subcat = is_subcat

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
            inv.areas = cls._parse(f.read())
        return inv

    @staticmethod
    def _parse(text):
        lines = text.split("\n")
        areas = []
        current_area = None
        current_cat = None
        current_subcat = None

        for raw_line in lines:
            line = raw_line.strip()
            if not line:
                continue
            area_match = re.match(r"^>?\s*Area Name:\s*(.+)", line, re.IGNORECASE)
            if area_match:
                current_area = Area(area_match.group(1).strip())
                current_cat = None
                current_subcat = None
                areas.append(current_area)
                continue
            if line.lower().startswith("sealable:") and current_area and current_cat is None:
                current_area.sealable = line.split(":", 1)[1].strip().lower() in ("yes", "true", "1")
                continue
            if line.lower().startswith("childof:") and current_area and current_cat is None:
                current_area.child_of = line.split(":", 1)[1].strip()
                continue
            if line.startswith(">"):
                clean = line.lstrip(">").strip()
                if "|" in clean:
                    parts = clean.split("|", 1)
                    iname = parts[0].strip()
                    try: qty = int(parts[1].strip())
                    except: qty = 1
                    if current_area is None:
                        current_area = Area("Items"); areas.append(current_area)
                    target = current_subcat if current_subcat else current_cat
                    if target is None:
                        target = Category("General")
                        current_area.categories.append(target)
                        current_cat = target
                    target.items.append(Item(iname, qty))
                else:
                    if current_area is None:
                        current_area = Area("Items"); areas.append(current_area)
                    current_subcat = Category(clean, is_subcat=True)
                    current_area.categories.append(current_subcat)
                continue
            if "|" in line:
                current_subcat = None
                parts = line.split("|", 1)
                iname = parts[0].strip()
                try: qty = int(parts[1].strip())
                except: qty = 1
                if current_area is None:
                    current_area = Area("Items"); areas.append(current_area)
                if current_cat is None:
                    current_cat = Category("General")
                    current_area.categories.append(current_cat)
                current_cat.items.append(Item(iname, qty))
                continue
            current_subcat = None
            if current_area is None:
                current_area = Area("Items"); areas.append(current_area)
            current_cat = Category(line)
            current_area.categories.append(current_cat)
        return areas

    def to_markdown(self):
        blocks = []
        for area in self.areas:
            lines = [f"Area Name: {area.name}"]
            if area.sealable: lines.append("sealable: yes")
            if area.child_of: lines.append(f"childOf: {area.child_of}")
            for cat in area.categories:
                if cat.is_subcat:
                    lines.append(f">{cat.name}")
                    for item in cat.items:
                        lines.append(f">{item.name}|{item.qty}")
                else:
                    lines.append(cat.name)
                    for item in cat.items:
                        lines.append(f"{item.name}|{item.qty}")
            blocks.append("\n".join(lines))
        return "\n\n".join(blocks) + "\n"

    def save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            f.write(self.to_markdown())

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
    __slots__ = ("name", "emsa_min")
    def __init__(self, name, emsa_min):
        self.name = name
        self.emsa_min = emsa_min

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
            text = f.read()
        current_cat = None
        for line in text.split("\n"):
            s = line.strip()
            if not s or (s.startswith("#") and not s.startswith("##")):
                continue
            if s.startswith("## "):
                current_cat = MasterCategory(s[3:].strip())
                ml.categories.append(current_cat)
                continue
            if "|" in s:
                parts = s.split("|", 1)
                name = parts[0].strip()
                try: qty = int(parts[1].strip())
                except: qty = 1
                if current_cat is None:
                    current_cat = MasterCategory("Uncategorized")
                    ml.categories.append(current_cat)
                current_cat.items.append(MasterItem(name, qty))
        return ml

    def to_markdown(self):
        lines = ["# EMS Inventory Master List", "#",
                 "# Format: Item Name | EMSA Min Qty", "# Categories are ## headers", ""]
        for cat in self.categories:
            lines.append(f"## {cat.name}")
            for item in cat.items:
                lines.append(f"{item.name} | {item.emsa_min}")
            lines.append("")
        return "\n".join(lines)

    def save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            f.write(self.to_markdown())

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


# == Application ==============================================================

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"EMS Inventory Editor v{VERSION}")
        self.geometry("1150x750")
        self.minsize(900, 550)

        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.checklists_dir = os.path.join(self.base_dir, "data", "checklists")
        self.master_list_path = os.path.join(self.checklists_dir, "master_list.md")
        self.master_list = None
        self.current_rig = None
        self.current_file = None
        self.rig_files = []
        self.dirty = False
        self.dirty_master = False
        self.lemsa_config_path = os.path.join(self.base_dir, "data", "lemsa_config.json")
        self.lemsa_config = {}  # {lemsa_name: {tracked: bool, page_url (LEMSA document): str, last_hash: str, last_checked: str}}

        self._build_ui()
        self._load_lemsa_config()
        self._rebuild_lemsa_list()
        self._load_master()
        self._refresh_rigs()

    # -- UI ------------------------------------------------------------------

    def _build_ui(self):
        toolbar = ttk.Frame(self, padding=4)
        toolbar.pack(fill=tk.X)

        ttk.Label(toolbar, text="Dir:").pack(side=tk.LEFT)
        self._dir_var = tk.StringVar(value=self.checklists_dir)
        ttk.Entry(toolbar, textvariable=self._dir_var, width=40).pack(side=tk.LEFT, padx=(4, 2))
        ttk.Button(toolbar, text="Browse\u2026", command=self._browse_dir).pack(side=tk.LEFT)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, padx=8, fill=tk.Y)
        ttk.Label(toolbar, text="Rig:").pack(side=tk.LEFT)
        self._rig_var = tk.StringVar()
        self._rig_combo = ttk.Combobox(toolbar, textvariable=self._rig_var, state="readonly", width=8)
        self._rig_combo.pack(side=tk.LEFT, padx=(4, 2))
        self._rig_combo.bind("<<ComboboxSelected>>", lambda e: self._on_rig_selected())
        ttk.Button(toolbar, text="Duplicate Rig\u2026", command=self._duplicate_rig).pack(side=tk.LEFT, padx=2)

        self._save_all_btn = ttk.Button(toolbar, text="Save All", command=self._save_all, state=tk.DISABLED)
        self._save_all_btn.pack(side=tk.RIGHT, padx=4)

        self._notebook = ttk.Notebook(self)
        self._notebook.pack(fill=tk.BOTH, expand=True, padx=4, pady=(0, 4))

        self._lemsa_tab = ttk.Frame(self._notebook)
        self._notebook.add(self._lemsa_tab, text="LEMSA Equipment")
        self._build_lemsa_tab()

        self._master_tab = ttk.Frame(self._notebook)
        self._notebook.add(self._master_tab, text="Master List")
        self._build_master_tab()

        self._rig_tab = ttk.Frame(self._notebook)
        self._notebook.add(self._rig_tab, text="Rig Files")
        self._build_rig_tab()

        self._status_var = tk.StringVar(value="Ready")
        ttk.Label(self, textvariable=self._status_var, relief=tk.SUNKEN,
                  anchor=tk.W, padding=(4, 2)).pack(fill=tk.X, side=tk.BOTTOM)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _build_master_tab(self):
        paned = ttk.PanedWindow(self._master_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        left = ttk.Frame(paned); paned.add(left, weight=1)

        sf = ttk.Frame(left); sf.pack(fill=tk.X, pady=(4, 2))
        ttk.Label(sf, text="Search:").pack(side=tk.LEFT)
        self._m_search_var = tk.StringVar()
        self._m_search_var.trace_add("write", lambda *_: self._rebuild_master_tree())
        ttk.Entry(sf, textvariable=self._m_search_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        ttk.Button(sf, text="\u2715", width=3, command=lambda: self._m_search_var.set("")).pack(side=tk.LEFT)

        tf = ttk.Frame(left); tf.pack(fill=tk.BOTH, expand=True)
        self._m_tree = ttk.Treeview(tf, selectmode="browse", show="tree")
        vsb = ttk.Scrollbar(tf, orient=tk.VERTICAL, command=self._m_tree.yview)
        self._m_tree.configure(yscrollcommand=vsb.set)
        self._m_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self._m_tree.bind("<<TreeviewSelect>>", self._on_master_select)
        self._m_tree.bind("<Button-3>", self._on_master_right_click)
        self._m_tree.bind("<Button-2>", self._on_master_right_click)

        right = ttk.Frame(paned, padding=8); paned.add(right, weight=1)
        self._m_detail_title = ttk.Label(right, text="Select an item", font=("TkDefaultFont", 12, "bold"))
        self._m_detail_title.pack(anchor=tk.W, pady=(0, 8))
        self._m_editor = ttk.Frame(right); self._m_editor.pack(fill=tk.BOTH, expand=True)
        self._m_ctx = tk.Menu(self, tearoff=0)

    def _build_rig_tab(self):
        paned = ttk.PanedWindow(self._rig_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        left = ttk.Frame(paned); paned.add(left, weight=1)

        top = ttk.Frame(left); top.pack(fill=tk.X, pady=(4, 2))
        ttk.Label(top, text="File:").pack(side=tk.LEFT)
        self._file_var = tk.StringVar()
        self._file_combo = ttk.Combobox(top, textvariable=self._file_var, state="readonly", width=22)
        self._file_combo.pack(side=tk.LEFT, padx=(4, 8))
        self._file_combo.bind("<<ComboboxSelected>>", lambda e: self._on_file_selected())
        ttk.Button(top, text="Simulate", command=self._simulate).pack(side=tk.LEFT, padx=2)

        sf = ttk.Frame(left); sf.pack(fill=tk.X, pady=(0, 2))
        ttk.Label(sf, text="Search:").pack(side=tk.LEFT)
        self._r_search_var = tk.StringVar()
        self._r_search_var.trace_add("write", lambda *_: self._rebuild_rig_tree())
        ttk.Entry(sf, textvariable=self._r_search_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        ttk.Button(sf, text="\u2715", width=3, command=lambda: self._r_search_var.set("")).pack(side=tk.LEFT)

        tf = ttk.Frame(left); tf.pack(fill=tk.BOTH, expand=True)
        self._r_tree = ttk.Treeview(tf, selectmode="browse", show="tree")
        vsb = ttk.Scrollbar(tf, orient=tk.VERTICAL, command=self._r_tree.yview)
        self._r_tree.configure(yscrollcommand=vsb.set)
        self._r_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self._r_tree.bind("<<TreeviewSelect>>", self._on_rig_tree_select)
        self._r_tree.bind("<Button-3>", self._on_rig_right_click)
        self._r_tree.bind("<Button-2>", self._on_rig_right_click)
        self._r_tree.tag_configure("not_in_master", foreground="#cc4400")

        right = ttk.Frame(paned, padding=8); paned.add(right, weight=1)
        self._r_detail_title = ttk.Label(right, text="Select an item", font=("TkDefaultFont", 12, "bold"))
        self._r_detail_title.pack(anchor=tk.W, pady=(0, 8))
        self._r_editor = ttk.Frame(right); self._r_editor.pack(fill=tk.BOTH, expand=True)
        self._r_ctx = tk.Menu(self, tearoff=0)

    def _build_lemsa_tab(self):
        paned = ttk.PanedWindow(self._lemsa_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)

        # Left: search + list
        left = ttk.Frame(paned); paned.add(left, weight=1)

        sf = ttk.Frame(left); sf.pack(fill=tk.X, pady=(4, 2))
        ttk.Label(sf, text="Search:").pack(side=tk.LEFT)
        self._l_search_var = tk.StringVar()
        self._l_search_var.trace_add("write", lambda *_: self._rebuild_lemsa_list())
        ttk.Entry(sf, textvariable=self._l_search_var).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        ttk.Button(sf, text="\u2715", width=3,
                   command=lambda: self._l_search_var.set("")).pack(side=tk.LEFT)

        ff = ttk.Frame(left); ff.pack(fill=tk.X, pady=(0, 2), padx=4)
        self._l_show_tracked_only = tk.BooleanVar(value=False)
        ttk.Checkbutton(ff, text="Show tracked only", variable=self._l_show_tracked_only,
                         command=self._rebuild_lemsa_list).pack(side=tk.LEFT)
        ttk.Button(ff, text="Check Tracked for Updates",
                   command=self._check_lemsa_updates).pack(side=tk.LEFT, padx=(8, 0))

        df = ttk.Frame(left); df.pack(fill=tk.X, pady=(0, 2), padx=4)
        ttk.Label(df, text="Save PDFs to:").pack(side=tk.LEFT)
        self._l_dl_dir_var = tk.StringVar(value=self.lemsa_config.get("_download_dir", ""))
        ttk.Entry(df, textvariable=self._l_dl_dir_var, width=30).pack(side=tk.LEFT, padx=4)
        ttk.Button(df, text="Browse…", command=self._browse_lemsa_dl_dir).pack(side=tk.LEFT)

        tf = ttk.Frame(left); tf.pack(fill=tk.BOTH, expand=True)
        self._l_tree = ttk.Treeview(tf, selectmode="browse", show="tree")
        vsb = ttk.Scrollbar(tf, orient=tk.VERTICAL, command=self._l_tree.yview)
        self._l_tree.configure(yscrollcommand=vsb.set)
        self._l_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True); vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self._l_tree.bind("<<TreeviewSelect>>", self._on_lemsa_select)
        self._l_tree.tag_configure("tracked", foreground="#006600")

        pf = ttk.Frame(left); pf.pack(fill=tk.X, padx=4, pady=(2, 4))
        self._l_progress = ttk.Progressbar(pf, mode="determinate", length=200)
        self._l_progress.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._l_progress_label = ttk.Label(pf, text="")
        self._l_progress_label.pack(side=tk.LEFT, padx=(8, 0))
        self._l_checking = False  # guard against concurrent checks

        # Right: detail
        right = ttk.Frame(paned, padding=8); paned.add(right, weight=1)
        self._l_detail_title = ttk.Label(right, text="Select a LEMSA",
                                          font=("TkDefaultFont", 12, "bold"))
        self._l_detail_title.pack(anchor=tk.W, pady=(0, 8))
        self._l_editor = ttk.Frame(right); self._l_editor.pack(fill=tk.BOTH, expand=True)

    # -- LEMSA config persistence --------------------------------------------

    def _load_lemsa_config(self):
        if os.path.isfile(self.lemsa_config_path):
            try:
                with open(self.lemsa_config_path, "r", encoding="utf-8") as f:
                    self.lemsa_config = json.load(f)
            except Exception:
                self.lemsa_config = {}
        else:
            self.lemsa_config = {}
        # Populate download dir from saved config
        if hasattr(self, '_l_dl_dir_var'):
            self._l_dl_dir_var.set(self.lemsa_config.get("_download_dir", ""))

    def _save_lemsa_config(self):
        os.makedirs(os.path.dirname(self.lemsa_config_path), exist_ok=True)
        with open(self.lemsa_config_path, "w", encoding="utf-8") as f:
            json.dump(self.lemsa_config, f, indent=2)

    def _get_lemsa_conf(self, name):
        if name not in self.lemsa_config:
            self.lemsa_config[name] = {
                "tracked": False, "page_url": "", "link_text": "",
                "last_hash": "", "last_checked": "", "resolved_url": ""
            }
        conf = self.lemsa_config[name]
        # Migrate old config key
        if "equip_url" in conf and "page_url" not in conf:
            conf["page_url"] = conf.pop("equip_url")
        elif "equip_url" in conf:
            conf.pop("equip_url")
        return conf

    def _browse_lemsa_dl_dir(self):
        d = filedialog.askdirectory(initialdir=self._l_dl_dir_var.get() or self.base_dir)
        if d:
            self._l_dl_dir_var.set(d)
            self.lemsa_config["_download_dir"] = d
            self._save_lemsa_config()

    def _get_lemsa_dl_dir(self):
        """Return the download dir, or None if not set."""
        d = self._l_dl_dir_var.get().strip()
        return d if d and os.path.isdir(d) else None

    def _save_lemsa_pdf(self, name, doc_data):
        """Save PDF to the download directory. Returns the file path or None."""
        dl_dir = self._get_lemsa_dl_dir()
        if not dl_dir:
            return None
        # Sanitize LEMSA name for filename
        safe_name = re.sub(r'[^\w\s\-]', '', name).strip().replace(' ', '_')
        filepath = os.path.join(dl_dir, f"{safe_name}.pdf")
        with open(filepath, "wb") as f:
            f.write(doc_data)
        return filepath

    # -- LEMSA list ----------------------------------------------------------

    def _rebuild_lemsa_list(self):
        self._l_tree.delete(*self._l_tree.get_children())
        q = self._l_search_var.get().strip().lower()
        tracked_only = self._l_show_tracked_only.get()
        for i, lemsa in enumerate(LEMSA_DATA):
            name = lemsa["name"]
            counties = ", ".join(lemsa["counties"])
            searchable = f"{name} {counties}".lower()
            if q and q not in searchable:
                continue
            conf = self._get_lemsa_conf(name)
            tracked = conf.get("tracked", False)
            if tracked_only and not tracked:
                continue
            prefix = "\u2713 " if tracked else "  "
            status = ""
            if conf.get("last_checked"):
                status = f"  [{conf['last_checked']}]"
            if conf.get("last_hash"):
                status += "  \u2714"  # checkmark = has baseline
            tags = ("tracked",) if tracked else ()
            self._l_tree.insert("", tk.END, iid=f"lemsa_{i}",
                                 text=f"{prefix}{name}{status}", tags=tags)

    def _on_lemsa_select(self, event):
        sel = self._l_tree.selection()
        if not sel: return
        idx = int(sel[0].split("_")[1])
        lemsa = LEMSA_DATA[idx]
        self._show_lemsa_editor(lemsa)

    def _show_lemsa_editor(self, lemsa):
        for w in self._l_editor.winfo_children(): w.destroy()
        name = lemsa["name"]
        conf = self._get_lemsa_conf(name)
        self._l_detail_title.config(text=name)
        f = self._l_editor

        # Counties
        ttk.Label(f, text="Counties:").grid(row=0, column=0, sticky=tk.NW, pady=4)
        ttk.Label(f, text=", ".join(lemsa["counties"]), wraplength=350).grid(
            row=0, column=1, sticky=tk.W, padx=4, pady=4)

        # Website
        ttk.Label(f, text="Website:").grid(row=1, column=0, sticky=tk.W, pady=4)
        url_label = ttk.Label(f, text=lemsa["url"], foreground="blue", cursor="hand2", wraplength=350)
        url_label.grid(row=1, column=1, sticky=tk.W, padx=4, pady=4)
        url_label.bind("<Button-1>", lambda e: webbrowser.open(lemsa["url"]))

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=2, column=0, columnspan=2, sticky=tk.EW, pady=8)

        # Tracked toggle
        tracked_var = tk.BooleanVar(value=conf.get("tracked", False))
        ttk.Checkbutton(f, text="Track this LEMSA", variable=tracked_var).grid(
            row=3, column=0, columnspan=2, sticky=tk.W, pady=4)

        # Protocols page URL
        ttk.Label(f, text="Protocols Page URL:").grid(row=4, column=0, sticky=tk.W, pady=4)
        page_var = tk.StringVar(value=conf.get("page_url", ""))
        ttk.Entry(f, textvariable=page_var, width=50).grid(row=4, column=1, sticky=tk.W, padx=4, pady=4)

        # Link text to find on the page
        ttk.Label(f, text="Link Text:").grid(row=5, column=0, sticky=tk.W, pady=4)
        link_text_var = tk.StringVar(value=conf.get("link_text", ""))
        ttk.Entry(f, textvariable=link_text_var, width=50).grid(row=5, column=1, sticky=tk.W, padx=4, pady=4)
        ttk.Label(f, text="Text of the clickable link on the page (not the PDF title)",
                  foreground="gray", font=("TkDefaultFont", 9)).grid(
            row=6, column=1, sticky=tk.W, padx=4)

        # Status info
        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=7, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Status:", font=("TkDefaultFont", 10, "bold")).grid(
            row=8, column=0, columnspan=2, sticky=tk.W)

        last_checked = conf.get("last_checked", "Never")
        last_hash = conf.get("last_hash", "")
        doc_url = conf.get("resolved_url", "")
        status_text = f"Last checked: {last_checked}"
        if last_hash:
            status_text += f"\nDocument hash: {last_hash[:16]}..."
        if doc_url:
            status_text += f"\nResolved URL: {doc_url}"
        ttk.Label(f, text=status_text, wraplength=400).grid(
            row=9, column=0, columnspan=2, sticky=tk.W, pady=4)

        def save():
            conf["tracked"] = tracked_var.get()
            conf["page_url"] = page_var.get().strip()
            conf["link_text"] = link_text_var.get().strip()
            self._save_lemsa_config()
            self._rebuild_lemsa_list()
            self._status_var.set(f"LEMSA config updated: {name}")

        ttk.Button(f, text="Save Settings", command=save).grid(
            row=10, column=0, columnspan=2, pady=12, sticky=tk.W)

        # Check this one
        def check_one():
            url = page_var.get().strip()
            lt = link_text_var.get().strip()
            if not url or not lt:
                self._status_var.set("Enter both a protocols page URL and link text first.")
                return
            # Auto-save all settings before checking
            conf["tracked"] = tracked_var.get()
            conf["page_url"] = url
            conf["link_text"] = lt
            self._save_lemsa_config()
            self._check_single_lemsa(name, conf)

        ttk.Button(f, text="Check Now", command=check_one).grid(
            row=11, column=0, columnspan=2, sticky=tk.W)

    def _fetch_url(self, url):
        """Fetch URL content. Tries urllib first, falls back to curl."""
        headers = {
            "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/131.0.0.0 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,"
                      "application/pdf,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Referer": url,
        }

        # Attempt 1: urllib with cookies
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
                    pass  # fall through to curl
            elif not isinstance(e, urllib.error.HTTPError):
                pass  # fall through to curl for other URL errors
            # For HTTP errors (403 etc), also fall through to curl

        # Attempt 2: curl (available on macOS, handles SSL/cookies natively)
        try:
            result = subprocess.run(
                ["curl", "-sL", "--max-time", "15",
                 "-H", f"User-Agent: {headers['User-Agent']}",
                 "-H", f"Accept: {headers['Accept']}",
                 "-H", f"Referer: {url}",
                 url],
                capture_output=True, timeout=20)
            if result.returncode == 0 and result.stdout:
                # Check for HTML error pages in what should be a PDF
                snippet = result.stdout[:200].lower()
                if b"access denied" not in snippet and b"403" not in snippet:
                    return result.stdout
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass

        # Attempt 3: Puppeteer browser download (handles CDN/WAF blocks)
        try:
            return self._fetch_via_browser(url)
        except Exception:
            pass

        raise Exception(f"Could not fetch {url} (urllib, curl, and browser all failed)")

    def _fetch_via_browser(self, url):
        """Download a file via Puppeteer (real browser), returns raw bytes."""
        script = os.path.join(self.base_dir, "fetch_page.js")
        if not os.path.isfile(script):
            raise Exception("fetch_page.js not found")
        result = subprocess.run(
            ["node", script, "--download", url],
            capture_output=True, timeout=45)
        if result.returncode != 0 or not result.stdout:
            err = result.stderr.decode("utf-8", errors="ignore").strip()
            raise Exception(f"Browser download failed: {err[:200]}")
        return base64.b64decode(result.stdout)

    def _extract_links(self, html):
        """Extract (href, clean_text) pairs from HTML, decoding HTML entities."""
        pattern = r'<a\s[^>]*href=["\']([^"\']+)["\'][^>]*>([\s\S]*?)</a>'
        matches = re.findall(pattern, html, re.IGNORECASE)
        candidates = []
        for href, inner in matches:
            href = html_module.unescape(href)
            clean_inner = re.sub(r"<[^>]+>", "", inner).strip()
            clean_inner = re.sub(r"\s+", " ", clean_inner)
            clean_inner = html_module.unescape(clean_inner)
            if clean_inner:
                candidates.append((href, clean_inner))
        return candidates

    def _fetch_rendered_html(self, url):
        """Use fetch_page.js (Node + Puppeteer) to get fully rendered DOM."""
        script = os.path.join(self.base_dir, "fetch_page.js")
        if not os.path.isfile(script):
            raise Exception(
                f"fetch_page.js not found at {script}\n"
                "Place it next to ems_inventory_editor.py")

        try:
            result = subprocess.run(
                ["node", script, url],
                capture_output=True, timeout=45)
        except FileNotFoundError:
            raise Exception(
                "Node.js not found. Install it from https://nodejs.org")
        except subprocess.TimeoutExpired:
            raise Exception("Page render timed out (45s)")

        if result.returncode != 0:
            err = result.stderr.decode("utf-8", errors="ignore").strip()
            if "Cannot find module" in err and "puppeteer" in err.lower():
                raise Exception(
                    "Puppeteer not installed. Run:\n"
                    "  npm install puppeteer")
            raise Exception(f"fetch_page.js failed: {err[:200]}")

        return result.stdout.decode("utf-8", errors="ignore")

    def _resolve_doc_url(self, page_url, link_text):
        """Fetch a page, find the <a> whose text contains link_text, return its absolute href."""
        target = link_text.strip().lower()

        def _make_absolute(href):
            if href.startswith("http"):
                return href
            elif href.startswith("/"):
                parsed = urlparse(page_url)
                return f"{parsed.scheme}://{parsed.netloc}{href}"
            else:
                base = page_url.rsplit("/", 1)[0]
                return f"{base}/{href}"

        def _find_match(candidates):
            # Exact match first
            for href, text in candidates:
                if text.lower() == target:
                    return _make_absolute(href)
            # Substring match
            for href, text in candidates:
                if target in text.lower():
                    return _make_absolute(href)
            return None

        # Attempt 1: regular fetch
        html_bytes = self._fetch_url(page_url)
        html = html_bytes.decode("utf-8", errors="ignore")
        candidates = self._extract_links(html)

        result = _find_match(candidates)
        if result:
            return result

        # No match from regular fetch — try rendered DOM (page may be JS-rendered)
        try:
            self._status_var.set("Link not found, trying rendered page...")
            self.update_idletasks()
            rendered_html = self._fetch_rendered_html(page_url)
            candidates = self._extract_links(rendered_html)

            result = _find_match(candidates)
            if result:
                return result
        except Exception as render_err:
            # If rendering fails, report with whatever we have
            pass

        # No match — show available links
        doc_links = [text for _, text in candidates
                     if any(kw in text.lower() for kw in
                            ("inventory", "equipment", "supply", "protocol",
                             "policy", "list", "manual", "field", "ambulance"))]
        if not doc_links:
            doc_links = [text for _, text in candidates if len(text) > 3]

        hint = "\n".join(f"  • {t}" for t in doc_links[:20])
        if not hint:
            hint = "(no links found)"
        raise Exception(
            f"Could not find link containing '{link_text}' on the page.\n\n"
            f"Links found on page:\n{hint}")

    def _check_single_lemsa(self, name, conf):
        if self._l_checking:
            return
        self._l_checking = True
        self._l_progress["maximum"] = 3
        self._l_progress["value"] = 0
        self._l_progress_label.config(text=name)
        self._status_var.set(f"Checking {name}...")

        def _worker():
            now = datetime.now().strftime("%Y-%m-%d %H:%M")
            conf["last_checked"] = now
            try:
                page_url = conf.get("page_url", "")
                link_text = conf.get("link_text", "")
                if not page_url or not link_text:
                    raise Exception("Missing page URL or link text")

                self.after(0, lambda: self._l_progress_label.config(text=f"{name}: resolving link..."))
                doc_url = self._resolve_doc_url(page_url, link_text)
                conf["resolved_url"] = doc_url
                self.after(0, lambda: [self._l_progress.configure(value=1),
                                        self._l_progress_label.config(text=f"{name}: downloading...")])

                doc_data = self._fetch_url(doc_url)
                self.after(0, lambda: [self._l_progress.configure(value=2),
                                        self._l_progress_label.config(text=f"{name}: comparing...")])

                new_hash = hashlib.sha256(doc_data).hexdigest()
                old_hash = conf.get("last_hash", "")

                if not old_hash:
                    conf["last_hash"] = new_hash
                    saved = self._save_lemsa_pdf(name, doc_data)
                    self._save_lemsa_config()
                    msg = f"{name}: baseline captured ({len(doc_data)} bytes)"
                    if saved:
                        msg += f" — saved to {os.path.basename(saved)}"
                elif new_hash != old_hash:
                    conf["last_hash"] = new_hash
                    saved = self._save_lemsa_pdf(name, doc_data)
                    self._save_lemsa_config()
                    msg = f"{name}: DOCUMENT CHANGED — review for updated requirements"
                    if saved:
                        msg += f" — saved to {os.path.basename(saved)}"
                else:
                    self._save_lemsa_config()
                    msg = f"{name}: no changes detected"

                def _finish():
                    self._l_progress["value"] = 3
                    self._l_progress_label.config(text="Done")
                    self._status_var.set(msg)
                    self._rebuild_lemsa_list()
                    for lemsa in LEMSA_DATA:
                        if lemsa["name"] == name:
                            self._show_lemsa_editor(lemsa)
                            break
                    self._l_checking = False
                self.after(0, _finish)

            except Exception as e:
                self._save_lemsa_config()
                def _err():
                    self._l_progress_label.config(text="Error")
                    self._status_var.set(f"{name}: error — {e}")
                    self._rebuild_lemsa_list()
                    self._l_checking = False
                self.after(0, _err)

        threading.Thread(target=_worker, daemon=True).start()

    def _check_lemsa_updates(self):
        if self._l_checking:
            return
        tracked = [(l, self._get_lemsa_conf(l["name"]))
                    for l in LEMSA_DATA if self._get_lemsa_conf(l["name"]).get("tracked")]
        if not tracked:
            self._status_var.set("No tracked LEMSAs. Select LEMSAs to track in the detail panel first.")
            return

        ready = [(l, c) for l, c in tracked if c.get("page_url") and c.get("link_text")]
        not_ready = [(l, c) for l, c in tracked
                     if not c.get("page_url") or not c.get("link_text")]

        if not_ready:
            names = ", ".join(l["name"] for l, c in not_ready)
            self._status_var.set(f"Skipping incomplete: {names}")

        if not ready:
            return

        self._l_checking = True
        total = len(ready)
        self._l_progress["maximum"] = total
        self._l_progress["value"] = 0
        self._l_progress_label.config(text=f"0/{total}")

        def _worker():
            results = {"changed": [], "baselined": [], "unchanged": [], "errors": []}
            for i, (lemsa, conf) in enumerate(ready):
                name = lemsa["name"]
                self.after(0, lambda n=name, idx=i: [
                    self._l_progress.configure(value=idx),
                    self._l_progress_label.config(text=f"{idx}/{total}: {n}"),
                    self._status_var.set(f"Checking {idx+1}/{total}: {n}...")])
                conf["last_checked"] = datetime.now().strftime("%Y-%m-%d %H:%M")
                try:
                    doc_url = self._resolve_doc_url(conf["page_url"], conf["link_text"])
                    conf["resolved_url"] = doc_url
                    doc_data = self._fetch_url(doc_url)
                    new_hash = hashlib.sha256(doc_data).hexdigest()
                    old_hash = conf.get("last_hash", "")

                    if not old_hash:
                        conf["last_hash"] = new_hash
                        self._save_lemsa_pdf(name, doc_data)
                        results["baselined"].append(name)
                    elif new_hash != old_hash:
                        conf["last_hash"] = new_hash
                        self._save_lemsa_pdf(name, doc_data)
                        results["changed"].append(name)
                    else:
                        results["unchanged"].append(name)
                except Exception as e:
                    results["errors"].append(f"{name}: {e}")

            def _finish():
                self._save_lemsa_config()
                self._rebuild_lemsa_list()
                self._l_progress["value"] = total
                parts = []
                if results["changed"]:
                    parts.append(f"CHANGED: {', '.join(results['changed'])}")
                if results["baselined"]:
                    parts.append(f"Baselined: {', '.join(results['baselined'])}")
                if results["unchanged"]:
                    parts.append(f"Unchanged: {', '.join(results['unchanged'])}")
                if results["errors"]:
                    parts.append(f"Errors: {', '.join(results['errors'])}")
                self._status_var.set(" | ".join(parts))
                self._l_progress_label.config(text="Done")
                self._l_checking = False
            self.after(0, _finish)

        threading.Thread(target=_worker, daemon=True).start()

    # -- Dir / rig / file management -----------------------------------------

    def _browse_dir(self):
        d = filedialog.askdirectory(initialdir=self._dir_var.get())
        if d:
            self._dir_var.set(d)
            self.checklists_dir = d
            self.master_list_path = os.path.join(d, "master_list.md")
            self._load_master()
            self._refresh_rigs()

    def _load_master(self):
        if os.path.isfile(self.master_list_path):
            try:
                self.master_list = MasterList.from_file(self.master_list_path)
                self._rebuild_master_tree()
                n = sum(len(c.items) for c in self.master_list.categories)
                self._status_var.set(f"Master list loaded: {n} items in {len(self.master_list.categories)} categories")
            except Exception as e:
                self._status_var.set(f"Master list error: {e}")
                self.master_list = None
        else:
            self.master_list = None
            self._status_var.set("No master_list.md found in checklists directory")

    def _refresh_rigs(self):
        d = self.checklists_dir
        if not os.path.isdir(d):
            self._rig_combo["values"] = []; return
        rigs = sorted([n for n in os.listdir(d) if os.path.isdir(os.path.join(d, n))], key=str.lower)
        self._rig_combo["values"] = rigs
        if rigs:
            self._rig_var.set(rigs[0]); self._on_rig_selected()

    def _on_rig_selected(self):
        if (self.dirty or self.dirty_master) and not self._confirm_discard(): return
        self.current_rig = self._rig_var.get()
        rig_dir = os.path.join(self.checklists_dir, self.current_rig)
        md_files = sorted([f for f in os.listdir(rig_dir) if f.endswith(".md")], key=str.lower)
        self._file_combo["values"] = md_files
        self.rig_files = []
        for fn in md_files:
            try: self.rig_files.append(InventoryFile.from_file(os.path.join(rig_dir, fn)))
            except: pass
        if md_files:
            self._file_var.set(md_files[0]); self._on_file_selected()
        else:
            self.current_file = None; self._rebuild_rig_tree()
        self.dirty = False; self.dirty_master = False; self._update_save_state()

    def _on_file_selected(self):
        fname = self._file_var.get()
        if not fname: return
        path = os.path.join(self.checklists_dir, self.current_rig, fname)
        try: self.current_file = InventoryFile.from_file(path)
        except Exception as e:
            self._status_var.set(f"Parse error: {e}"); self.current_file = None
        self._rebuild_rig_tree(); self._clear_rig_editor()
        if self.current_file:
            total = sum(len(c.items) for a in self.current_file.areas for c in a.categories)
            flag = ""
            if self.master_list:
                mn = self.master_list.all_item_names()
                nim = sum(1 for a in self.current_file.areas for c in a.categories
                          for i in c.items if i.name not in mn)
                if nim: flag = f", {nim} not in master"
            self._status_var.set(f"{fname} \u2014 {total} items{flag}")

    def _duplicate_rig(self):
        if not self.current_rig: return
        new = simpledialog.askstring("Duplicate Rig", f"Duplicating '{self.current_rig}'.\nNew rig number:", parent=self)
        if not new: return
        new = new.strip()
        src = os.path.join(self.checklists_dir, self.current_rig)
        dst = os.path.join(self.checklists_dir, new)
        if os.path.exists(dst):
            self._status_var.set(f"Rig '{new}' already exists."); return
        try: shutil.copytree(src, dst)
        except Exception as e: self._status_var.set(f"Duplicate error: {e}"); return
        self._refresh_rigs(); self._rig_var.set(new); self._on_rig_selected()
        self._status_var.set(f"Duplicated {self.current_rig} \u2192 {new}")

    # -- Tree state persistence -----------------------------------------------

    def _save_tree_state(self, tree):
        """Capture which nodes are open and which is selected."""
        open_nodes = set()
        def _walk(parent=""):
            for node in tree.get_children(parent):
                if tree.item(node, "open"):
                    open_nodes.add(node)
                _walk(node)
        _walk()
        sel = tree.selection()
        return {"open": open_nodes, "selected": sel[0] if sel else None}

    def _restore_tree_state(self, tree, state):
        """Restore open/collapsed and selection state after a rebuild."""
        for node in state["open"]:
            if tree.exists(node):
                tree.item(node, open=True)
        if state["selected"] and tree.exists(state["selected"]):
            tree.selection_set(state["selected"])
            tree.see(state["selected"])

    # -- Master tree ---------------------------------------------------------

    def _rebuild_master_tree(self):
        state = self._save_tree_state(self._m_tree)
        self._m_tree.delete(*self._m_tree.get_children())
        if not self.master_list: return
        q = self._m_search_var.get().strip().lower()
        for ci, cat in enumerate(self.master_list.categories):
            matches = [(ii, it) for ii, it in enumerate(cat.items) if not q or q in it.name.lower()]
            if not matches and q: continue
            cid = f"mc_{ci}"
            show = matches if q else list(enumerate(cat.items))

            # Group items by comma-prefix: "BP Cuffs, 7" → prefix "BP Cuffs", suffix "7"
            groups = {}   # prefix -> [(item_index, item, suffix)]
            ungrouped = []  # (item_index, item)
            for ii, it in show:
                if ", " in it.name:
                    prefix, suffix = it.name.split(", ", 1)
                    groups.setdefault(prefix, []).append((ii, it, suffix))
                else:
                    ungrouped.append((ii, it))

            # Only use grouping for prefixes with 2+ items; otherwise treat as ungrouped
            real_groups = {}
            for prefix, members in groups.items():
                if len(members) >= 2:
                    real_groups[prefix] = members
                else:
                    for ii, it, suffix in members:
                        ungrouped.append((ii, it))

            total_visible = len(ungrouped) + sum(len(m) for m in real_groups.values())
            self._m_tree.insert("", tk.END, iid=cid,
                text=f"\U0001F4C2 {cat.name} ({total_visible})", open=bool(q))

            # Insert groups first (sorted by prefix)
            for gi, prefix in enumerate(sorted(real_groups.keys(), key=str.lower)):
                members = real_groups[prefix]
                gid = f"mc_{ci}_g_{gi}"
                self._m_tree.insert(cid, tk.END, iid=gid,
                    text=f"{prefix} ({len(members)})", open=bool(q))
                for ii, it, suffix in members:
                    self._m_tree.insert(gid, tk.END, iid=f"mc_{ci}_i_{ii}",
                        text=f"{suffix}  (min {it.emsa_min})")

            # Insert ungrouped items (sorted by name)
            for ii, it in sorted(ungrouped, key=lambda x: x[1].name.lower()):
                self._m_tree.insert(cid, tk.END, iid=f"mc_{ci}_i_{ii}",
                    text=f"{it.name}  (min {it.emsa_min})")

        self._restore_tree_state(self._m_tree, state)

    def _on_master_select(self, event):
        sel = self._m_tree.selection()
        if not sel: return
        node = sel[0]
        parts = node.split("_")
        ci = int(parts[1]); cat = self.master_list.categories[ci]
        if "_i_" in node:
            ii = int(node.split("_i_")[1])
            self._show_master_item_editor(cat, cat.items[ii])
        elif "_g_" in node:
            # Group node — find the prefix from the first matching item
            gi = int(node.split("_g_")[1])
            # Reconstruct which prefix this group index corresponds to
            groups = {}
            for it in cat.items:
                if ", " in it.name:
                    prefix = it.name.split(", ", 1)[0]
                    groups.setdefault(prefix, []).append(it)
            real_groups = {p: m for p, m in groups.items() if len(m) >= 2}
            sorted_prefixes = sorted(real_groups.keys(), key=str.lower)
            if gi < len(sorted_prefixes):
                prefix = sorted_prefixes[gi]
                self._show_master_group_editor(cat, prefix, real_groups[prefix])
        else:
            self._show_master_cat_editor(cat)

    def _show_master_group_editor(self, cat, prefix, members):
        for w in self._m_editor.winfo_children(): w.destroy()
        self._m_detail_title.config(text=f"Edit Group — {cat.name}")
        f = self._m_editor

        ttk.Label(f, text="Group Name:").grid(row=0, column=0, sticky=tk.W, pady=4)
        name_var = tk.StringVar(value=prefix)
        ttk.Entry(f, textvariable=name_var, width=40).grid(row=0, column=1, sticky=tk.W, padx=4, pady=4)

        ttk.Label(f, text=f"{len(members)} items in this group").grid(
            row=1, column=0, columnspan=2, sticky=tk.W, pady=4)

        old_prefix = prefix

        def apply():
            new_prefix = name_var.get().strip()
            if not new_prefix:
                self._status_var.set("Group name cannot be empty.")
                return
            if new_prefix == old_prefix:
                return

            # Rename prefix on all member items and propagate to rig files
            total_rig_renames = 0
            for it in members:
                old_full = it.name
                suffix = old_full.split(", ", 1)[1]
                new_full = f"{new_prefix}, {suffix}"
                it.name = new_full
                total_rig_renames += sum(
                    rf.rename_item_everywhere(old_full, new_full) for rf in self.rig_files)

            self.dirty_master = True
            self.dirty = bool(total_rig_renames) or self.dirty
            self._update_save_state()
            self._rebuild_master_tree()
            self._rebuild_rig_tree()
            self._status_var.set(
                f"Renamed group '{old_prefix}' → '{new_prefix}' "
                f"({len(members)} items, {total_rig_renames} rig location(s))")

        ttk.Button(f, text="Apply", command=apply).grid(
            row=2, column=0, columnspan=2, pady=12, sticky=tk.W)

        def delete_group():
            for it in list(members):
                cat.items.remove(it)
            self.dirty_master = True
            self._update_save_state()
            self._rebuild_master_tree()
            self._clear_master_editor()
            self._status_var.set(f"Deleted group '{prefix}' ({len(members)} items)")

        ttk.Button(f, text="Delete Group", command=delete_group).grid(
            row=3, column=0, columnspan=2, sticky=tk.W)

    def _show_master_item_editor(self, cat, item):
        for w in self._m_editor.winfo_children(): w.destroy()
        f = self._m_editor

        # Detect if this item belongs to a group (has comma prefix)
        has_prefix = ", " in item.name
        if has_prefix:
            prefix, suffix = item.name.split(", ", 1)
            display_name = suffix
            self._m_detail_title.config(text=f"Edit Master Item — {cat.name} › {prefix}")
        else:
            prefix = None
            display_name = item.name
            self._m_detail_title.config(text=f"Edit Master Item — {cat.name}")

        ttk.Label(f, text="Item Name:").grid(row=0, column=0, sticky=tk.W, pady=4)
        name_var = tk.StringVar(value=display_name)
        ttk.Entry(f, textvariable=name_var, width=45).grid(row=0, column=1, sticky=tk.W, padx=4, pady=4)

        ttk.Label(f, text="EMSA Min Qty:").grid(row=1, column=0, sticky=tk.W, pady=4)
        qty_var = tk.IntVar(value=item.emsa_min)
        ttk.Spinbox(f, from_=0, to=9999, textvariable=qty_var, width=8).grid(row=1, column=1, sticky=tk.W, padx=4, pady=4)

        ttk.Label(f, text="Category:").grid(row=2, column=0, sticky=tk.W, pady=4)
        cat_names = [c.name for c in self.master_list.categories]
        cat_var = tk.StringVar(value=cat.name)
        ttk.Combobox(f, textvariable=cat_var, values=cat_names, state="readonly", width=30).grid(
            row=2, column=1, sticky=tk.W, padx=4, pady=4)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=3, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Rig Locations:", font=("TkDefaultFont", 10, "bold")).grid(
            row=4, column=0, columnspan=2, sticky=tk.W)

        loc_frame = ttk.Frame(f)
        loc_frame.grid(row=5, column=0, columnspan=2, sticky=tk.NSEW, pady=4)
        loc_widgets = []; row = 0
        for rf in self.rig_files:
            for loc in rf.item_locations(item.name):
                label = f"{rf.filename} \u203A {loc['area']} \u203A {loc['category']}"
                ttk.Label(loc_frame, text=label, wraplength=350).grid(row=row, column=0, sticky=tk.W, pady=1)
                lqv = tk.IntVar(value=loc["qty"])
                ttk.Spinbox(loc_frame, from_=0, to=9999, textvariable=lqv, width=6).grid(
                    row=row, column=1, sticky=tk.W, padx=4, pady=1)
                loc_widgets.append((lqv, loc["item_ref"])); row += 1
        if row == 0:
            ttk.Label(loc_frame, text="(not placed on current rig)", foreground="gray").grid(row=0, column=0)

        old_name = item.name

        def apply():
            new_suffix = name_var.get().strip()
            if not new_suffix: self._status_var.set("Item name cannot be empty."); return
            try: new_qty = int(qty_var.get())
            except: self._status_var.set("Quantity must be a number."); return

            # Reconstruct full name with prefix if item belongs to a group
            new_name = f"{prefix}, {new_suffix}" if prefix else new_suffix

            if new_name != old_name:
                item.name = new_name
                total_r = sum(rf.rename_item_everywhere(old_name, new_name) for rf in self.rig_files)
                if total_r:
                    self._status_var.set(f"Renamed '{old_name}' \u2192 '{new_name}' in {total_r} location(s)")
                self.dirty = True

            item.emsa_min = new_qty
            new_cat = cat_var.get()
            if new_cat != cat.name:
                cat.items.remove(item)
                for c in self.master_list.categories:
                    if c.name == new_cat: c.items.append(item); break

            for lqv, iref in loc_widgets:
                try: iref.qty = int(lqv.get())
                except: pass

            self.dirty_master = True; self.dirty = True
            self._update_save_state(); self._rebuild_master_tree(); self._rebuild_rig_tree()

        ttk.Button(f, text="Apply Changes", command=apply).grid(row=6, column=0, columnspan=2, pady=12, sticky=tk.W)

        def delete():
            cat.items.remove(item)
            self.dirty_master = True; self._update_save_state()
            self._rebuild_master_tree(); self._clear_master_editor()
            self._status_var.set(f"Deleted '{item.name}' from master list")

        ttk.Button(f, text="Delete from Master", command=delete).grid(row=7, column=0, columnspan=2, sticky=tk.W)

    def _show_master_cat_editor(self, cat):
        for w in self._m_editor.winfo_children(): w.destroy()
        self._m_detail_title.config(text="Edit Category")
        f = self._m_editor

        ttk.Label(f, text="Name:").grid(row=0, column=0, sticky=tk.W, pady=4)
        name_var = tk.StringVar(value=cat.name)
        ttk.Entry(f, textvariable=name_var, width=40).grid(row=0, column=1, sticky=tk.W, padx=4, pady=4)
        ttk.Label(f, text=f"{len(cat.items)} items").grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=4)

        def apply():
            n = name_var.get().strip()
            if n: cat.name = n; self.dirty_master = True; self._update_save_state(); self._rebuild_master_tree()
        ttk.Button(f, text="Apply", command=apply).grid(row=2, column=0, columnspan=2, pady=8, sticky=tk.W)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=3, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Add Item:", font=("TkDefaultFont", 10, "bold")).grid(row=4, column=0, columnspan=2, sticky=tk.W)
        ttk.Label(f, text="Name:").grid(row=5, column=0, sticky=tk.W, pady=2)
        nv = tk.StringVar(); ttk.Entry(f, textvariable=nv, width=40).grid(row=5, column=1, sticky=tk.W, padx=4, pady=2)
        ttk.Label(f, text="EMSA Min:").grid(row=6, column=0, sticky=tk.W, pady=2)
        nq = tk.IntVar(value=1); ttk.Spinbox(f, from_=0, to=9999, textvariable=nq, width=8).grid(row=6, column=1, sticky=tk.W, padx=4, pady=2)

        def add():
            n = nv.get().strip()
            if n: cat.items.append(MasterItem(n, int(nq.get()))); nv.set("")
            self.dirty_master = True; self._update_save_state(); self._rebuild_master_tree()
        ttk.Button(f, text="Add Item", command=add).grid(row=7, column=0, columnspan=2, pady=8, sticky=tk.W)

    def _clear_master_editor(self):
        for w in self._m_editor.winfo_children(): w.destroy()
        self._m_detail_title.config(text="Select an item")

    def _on_master_right_click(self, event):
        node = self._m_tree.identify_row(event.y)
        self._m_ctx.delete(0, tk.END)
        if not node:
            self._m_ctx.add_command(label="Add Category\u2026", command=self._add_master_cat)
        else:
            self._m_tree.selection_set(node)
            parts = node.split("_"); ci = int(parts[1]); cat = self.master_list.categories[ci]
            if "_i_" in node:
                ii = int(node.split("_i_")[1]); it = cat.items[ii]
                self._m_ctx.add_command(label=f"Delete '{it.name}'",
                    command=lambda: self._del_master_item(cat, it))
            elif "_g_" in node:
                # Group node — offer to add item to this category
                self._m_ctx.add_command(label="Add Item\u2026", command=lambda: self._qadd_master_item(cat))
            else:
                self._m_ctx.add_command(label="Add Item\u2026", command=lambda: self._qadd_master_item(cat))
                self._m_ctx.add_separator()
                self._m_ctx.add_command(label="Add Category\u2026", command=self._add_master_cat)
                self._m_ctx.add_separator()
                self._m_ctx.add_command(label=f"Delete '{cat.name}'", command=lambda: self._del_master_cat(cat))
        self._m_ctx.tk_popup(event.x_root, event.y_root)

    def _add_master_cat(self):
        if not self.master_list: return
        n = simpledialog.askstring("Add Category", "Category name:", parent=self)
        if n: self.master_list.categories.append(MasterCategory(n.strip())); self.dirty_master = True
        self._update_save_state(); self._rebuild_master_tree()

    def _qadd_master_item(self, cat):
        n = simpledialog.askstring("Add Item", "Item name:", parent=self)
        if not n: return
        q = simpledialog.askinteger("EMSA Min", "EMSA minimum qty:", initialvalue=1, minvalue=0, parent=self)
        if q is None: return
        cat.items.append(MasterItem(n.strip(), q)); self.dirty_master = True
        self._update_save_state(); self._rebuild_master_tree()

    def _del_master_item(self, cat, item):
        cat.items.remove(item); self.dirty_master = True
        self._update_save_state(); self._rebuild_master_tree(); self._clear_master_editor()

    def _del_master_cat(self, cat):
        self.master_list.categories.remove(cat); self.dirty_master = True
        self._update_save_state(); self._rebuild_master_tree(); self._clear_master_editor()

    # -- Rig tree ------------------------------------------------------------

    def _rebuild_rig_tree(self):
        state = self._save_tree_state(self._r_tree)
        self._r_tree.delete(*self._r_tree.get_children())
        if not self.current_file: return
        q = self._r_search_var.get().strip().lower()
        mn = self.master_list.all_item_names() if self.master_list else set()

        for ai, area in enumerate(self.current_file.areas):
            aid = f"ra_{ai}"; area_added = False
            for ci, cat in enumerate(area.categories):
                matches = [(ii, it) for ii, it in enumerate(cat.items) if not q or q in it.name.lower()]
                if not matches: continue
                if not area_added:
                    seal = " [sealable]" if area.sealable else ""
                    child = f" (child of {area.child_of})" if area.child_of else ""
                    self._r_tree.insert("", tk.END, iid=aid,
                        text=f"\U0001F4E6 {area.name}{seal}{child}", open=bool(q))
                    area_added = True
                cid = f"ra_{ai}_c_{ci}"
                self._r_tree.insert(aid, tk.END, iid=cid,
                    text=f"\U0001F4C2 {cat.name} ({len(matches)})", open=bool(q))
                for ii, it in matches:
                    iid = f"ra_{ai}_c_{ci}_i_{ii}"
                    ok = it.name in mn
                    flag = "" if ok else " \u26A0"
                    tags = ("ritem",) if ok else ("ritem", "not_in_master")
                    self._r_tree.insert(cid, tk.END, iid=iid, text=f"{it.name}  \u00D7{it.qty}{flag}", tags=tags)

        self._restore_tree_state(self._r_tree, state)

    def _on_rig_tree_select(self, event):
        sel = self._r_tree.selection()
        if not sel: return
        parts = sel[0].split("_")
        ai = int(parts[1]); area = self.current_file.areas[ai]
        if len(parts) <= 2: self._show_rig_area_editor(area)
        elif len(parts) <= 4:
            ci = int(parts[3]); self._show_rig_cat_editor(area, area.categories[ci])
        else:
            ci = int(parts[3]); ii = int(parts[5])
            self._show_rig_item_editor(area, area.categories[ci], area.categories[ci].items[ii])

    def _clear_rig_editor(self):
        for w in self._r_editor.winfo_children(): w.destroy()
        self._r_detail_title.config(text="Select an item")

    def _show_rig_item_editor(self, area, cat, item):
        for w in self._r_editor.winfo_children(): w.destroy()
        self._r_detail_title.config(text=f"Edit Item \u2014 {area.name} \u203A {cat.name}")
        f = self._r_editor
        mn = self.master_list.all_item_names() if self.master_list else set()
        r = 0
        if item.name not in mn:
            ttk.Label(f, text="\u26A0 Not in master list", foreground="#cc4400",
                font=("TkDefaultFont", 10, "bold")).grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 8))
            r = 1

        ttk.Label(f, text="Name:").grid(row=r, column=0, sticky=tk.W, pady=4)
        nv = tk.StringVar(value=item.name)
        ttk.Entry(f, textvariable=nv, width=40).grid(row=r, column=1, sticky=tk.W, padx=4, pady=4)
        ttk.Label(f, text="Qty:").grid(row=r+1, column=0, sticky=tk.W, pady=4)
        qv = tk.IntVar(value=item.qty)
        ttk.Spinbox(f, from_=0, to=9999, textvariable=qv, width=8).grid(row=r+1, column=1, sticky=tk.W, padx=4, pady=4)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=r+2, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Move to:").grid(row=r+3, column=0, sticky=tk.W, pady=4)
        dests = {}; dlabels = []
        for a in self.current_file.areas:
            for c in a.categories:
                lb = f"{a.name} \u203A {c.name}"; dlabels.append(lb); dests[lb] = (a, c)
        cur = f"{area.name} \u203A {cat.name}"
        mv = tk.StringVar(value=cur)
        ttk.Combobox(f, textvariable=mv, values=dlabels, state="readonly", width=38).grid(
            row=r+3, column=1, sticky=tk.W, padx=4, pady=4)

        def apply():
            nn = nv.get().strip()
            if not nn: return
            try: nq = int(qv.get())
            except: return
            item.name = nn; item.qty = nq
            dl = mv.get()
            if dl != cur and dl in dests:
                cat.items.remove(item); dests[dl][1].items.append(item)
            self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()
        ttk.Button(f, text="Apply", command=apply).grid(row=r+4, column=0, columnspan=2, pady=12, sticky=tk.W)

        def delete():
            cat.items.remove(item); self.dirty = True; self._update_save_state()
            self._rebuild_rig_tree(); self._clear_rig_editor()
        ttk.Button(f, text="Delete", command=delete).grid(row=r+5, column=0, columnspan=2, sticky=tk.W)

    def _show_rig_area_editor(self, area):
        for w in self._r_editor.winfo_children(): w.destroy()
        self._r_detail_title.config(text="Edit Area")
        f = self._r_editor
        ttk.Label(f, text="Name:").grid(row=0, column=0, sticky=tk.W, pady=4)
        nv = tk.StringVar(value=area.name)
        ttk.Entry(f, textvariable=nv, width=40).grid(row=0, column=1, sticky=tk.W, padx=4, pady=4)
        sv = tk.BooleanVar(value=area.sealable)
        ttk.Checkbutton(f, text="Sealable", variable=sv).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=4)
        ttk.Label(f, text="Child of:").grid(row=2, column=0, sticky=tk.W, pady=4)
        parents = ["(none)"] + [a.name for a in self.current_file.areas if a is not area]
        pv = tk.StringVar(value=area.child_of or "(none)")
        ttk.Combobox(f, textvariable=pv, values=parents, state="readonly", width=30).grid(
            row=2, column=1, sticky=tk.W, padx=4, pady=4)

        def apply():
            n = nv.get().strip()
            if n: area.name = n; area.sealable = sv.get()
            area.child_of = pv.get() if pv.get() != "(none)" else None
            self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()
        ttk.Button(f, text="Apply", command=apply).grid(row=3, column=0, columnspan=2, pady=12, sticky=tk.W)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=4, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Add Category:", font=("TkDefaultFont", 10, "bold")).grid(row=5, column=0, columnspan=2, sticky=tk.W)
        cv = tk.StringVar(); ttk.Entry(f, textvariable=cv, width=40).grid(row=6, column=0, columnspan=2, sticky=tk.W, padx=4)
        def add_cat():
            n = cv.get().strip()
            if n: area.categories.append(Category(n)); cv.set(""); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()
        ttk.Button(f, text="Add Category", command=add_cat).grid(row=7, column=0, columnspan=2, pady=8, sticky=tk.W)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=8, column=0, columnspan=2, sticky=tk.EW, pady=8)
        def delete():
            self.current_file.areas.remove(area); self.dirty = True; self._update_save_state()
            self._rebuild_rig_tree(); self._clear_rig_editor()
            self._status_var.set(f"Deleted area '{area.name}'")
        ttk.Button(f, text="Delete Area", command=delete).grid(row=9, column=0, columnspan=2, sticky=tk.W)

    def _show_rig_cat_editor(self, area, cat):
        for w in self._r_editor.winfo_children(): w.destroy()
        self._r_detail_title.config(text=f"Edit Category \u2014 {area.name}")
        f = self._r_editor
        ttk.Label(f, text="Name:").grid(row=0, column=0, sticky=tk.W, pady=4)
        nv = tk.StringVar(value=cat.name)
        ttk.Entry(f, textvariable=nv, width=40).grid(row=0, column=1, sticky=tk.W, padx=4, pady=4)
        def apply():
            n = nv.get().strip()
            if n: cat.name = n; self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()
        ttk.Button(f, text="Apply", command=apply).grid(row=1, column=0, columnspan=2, pady=8, sticky=tk.W)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=2, column=0, columnspan=2, sticky=tk.EW, pady=8)
        ttk.Label(f, text="Add Item:", font=("TkDefaultFont", 10, "bold")).grid(row=3, column=0, columnspan=2, sticky=tk.W)
        ttk.Label(f, text="Name:").grid(row=4, column=0, sticky=tk.W, pady=2)
        inv = tk.StringVar(); ttk.Entry(f, textvariable=inv, width=40).grid(row=4, column=1, sticky=tk.W, padx=4, pady=2)
        ttk.Label(f, text="Qty:").grid(row=5, column=0, sticky=tk.W, pady=2)
        iqv = tk.IntVar(value=1); ttk.Spinbox(f, from_=0, to=9999, textvariable=iqv, width=8).grid(row=5, column=1, sticky=tk.W, padx=4, pady=2)
        def add():
            n = inv.get().strip()
            if n: cat.items.append(Item(n, int(iqv.get()))); inv.set(""); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()
        ttk.Button(f, text="Add Item", command=add).grid(row=6, column=0, columnspan=2, pady=8, sticky=tk.W)

        ttk.Separator(f, orient=tk.HORIZONTAL).grid(row=7, column=0, columnspan=2, sticky=tk.EW, pady=8)
        def delete():
            area.categories.remove(cat); self.dirty = True; self._update_save_state()
            self._rebuild_rig_tree(); self._clear_rig_editor()
            self._status_var.set(f"Deleted category '{cat.name}'")
        ttk.Button(f, text="Delete Category", command=delete).grid(row=8, column=0, columnspan=2, sticky=tk.W)

    def _on_rig_right_click(self, event):
        node = self._r_tree.identify_row(event.y)
        self._r_ctx.delete(0, tk.END)
        if not node:
            self._r_ctx.add_command(label="Add Area\u2026", command=self._add_rig_area)
            self._r_ctx.tk_popup(event.x_root, event.y_root); return
        self._r_tree.selection_set(node)
        parts = node.split("_"); ai = int(parts[1]); area = self.current_file.areas[ai]
        if len(parts) > 4:
            ci = int(parts[3]); ii = int(parts[5])
            cat = area.categories[ci]; it = cat.items[ii]
            self._r_ctx.add_command(label=f"Delete '{it.name}'", command=lambda: self._rdel_item(cat, it))
        elif len(parts) > 2:
            ci = int(parts[3]); cat = area.categories[ci]
            self._r_ctx.add_command(label="Add Item\u2026", command=lambda: self._radd_item(cat))
            self._r_ctx.add_separator()
            self._r_ctx.add_command(label=f"Delete '{cat.name}'", command=lambda: self._rdel_cat(area, cat))
        else:
            self._r_ctx.add_command(label="Add Category\u2026", command=lambda: self._radd_cat(area))
            self._r_ctx.add_separator()
            self._r_ctx.add_command(label="Add Area\u2026", command=self._add_rig_area)
            self._r_ctx.add_separator()
            self._r_ctx.add_command(label=f"Delete '{area.name}'", command=lambda: self._rdel_area(area))
        self._r_ctx.tk_popup(event.x_root, event.y_root)

    def _add_rig_area(self):
        if not self.current_file: return
        n = simpledialog.askstring("Add Area", "Area name:", parent=self)
        if n: self.current_file.areas.append(Area(n.strip())); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()

    def _radd_item(self, cat):
        n = simpledialog.askstring("Add Item", "Item name:", parent=self)
        if not n: return
        q = simpledialog.askinteger("Qty", "Quantity:", initialvalue=1, minvalue=0, parent=self)
        if q is None: return
        cat.items.append(Item(n.strip(), q)); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()

    def _radd_cat(self, area):
        n = simpledialog.askstring("Add Category", "Category name:", parent=self)
        if n: area.categories.append(Category(n.strip())); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree()

    def _rdel_item(self, cat, item):
        cat.items.remove(item); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree(); self._clear_rig_editor()

    def _rdel_cat(self, area, cat):
        area.categories.remove(cat); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree(); self._clear_rig_editor()

    def _rdel_area(self, area):
        self.current_file.areas.remove(area); self.dirty = True; self._update_save_state(); self._rebuild_rig_tree(); self._clear_rig_editor()

    # -- Simulate ------------------------------------------------------------

    def _simulate(self):
        if not self.current_file:
            self._status_var.set("No file selected to simulate.")
            return

        # Locate the widget HTML
        widget_path = os.path.join(self.base_dir, "widgets", "ems-inventory-checklist.html")
        if not os.path.isfile(widget_path):
            self._status_var.set(f"Widget not found at {widget_path}")
            return

        # Get current in-memory markdown (includes unsaved edits)
        md_content = self.current_file.to_markdown()

        # Read the widget HTML
        with open(widget_path, "r", encoding="utf-8") as f:
            html = f.read()

        # Build the JS replacement
        js_str = json.dumps(md_content)
        replacement = f"var DEFAULT_INVENTORY = {js_str};"

        # Find the DEFAULT_INVENTORY assignment using regex search,
        # then replace via string slicing (avoids regex replacement parsing issues)
        pattern = r"var\s+DEFAULT_INVENTORY\s*=\s*[\s\S]*?;"
        match = re.search(pattern, html)

        if not match:
            self._status_var.set("Could not find DEFAULT_INVENTORY in widget HTML.")
            return

        new_html = html[:match.start()] + replacement + html[match.end():]

        # Force standalone mode: remove JotForm CDN script tags so
        # JFCustomWidget is undefined and the widget uses standalone init.
        # Without this, the CDN scripts load and define JFCustomWidget,
        # but the 'ready' event never fires since there's no parent form.
        new_html = re.sub(
            r'<script[^>]*src="[^"]*jotfor[^"]*"[^>]*>\s*</script>\s*',
            '', new_html)

        # Write to a temp file and open in browser
        tmp = tempfile.NamedTemporaryFile(suffix=".html", prefix="ems_sim_",
                                           delete=False, mode="w", encoding="utf-8")
        tmp.write(new_html)
        tmp.close()

        webbrowser.open(f"file://{tmp.name}")
        self._status_var.set(f"Simulating {self.current_file.filename} — temp file: {tmp.name}")

    # -- Save ----------------------------------------------------------------

    def _update_save_state(self):
        state = tk.NORMAL if (self.dirty or self.dirty_master) else tk.DISABLED
        self._save_all_btn.config(state=state)
        base = f"EMS Inventory Editor v{VERSION}"
        self.title(f"\u25CF {base}" if (self.dirty or self.dirty_master) else base)

    def _save_all(self):
        errors = []
        if self.dirty_master and self.master_list:
            try: self.master_list.save()
            except Exception as e: errors.append(f"Master: {e}")
        if self.dirty:
            for rf in self.rig_files:
                try: rf.save()
                except Exception as e: errors.append(f"{rf.filename}: {e}")
        if errors: self._status_var.set(f"Save errors: {'; '.join(errors)}")
        else:
            parts = []
            if self.dirty_master: parts.append("master list")
            if self.dirty: parts.append(f"{len(self.rig_files)} rig file(s)")
            self._status_var.set(f"Saved {', '.join(parts)}")
        self.dirty = False; self.dirty_master = False; self._update_save_state()

    def _confirm_discard(self):
        return messagebox.askyesno("Unsaved Changes", "Discard unsaved changes?")

    def _on_close(self):
        if (self.dirty or self.dirty_master) and not self._confirm_discard(): return
        self.destroy()


if __name__ == "__main__":
    app = App()
    app.lift()
    app.attributes("-topmost", True)
    app.after(100, lambda: app.attributes("-topmost", False))
    app.focus_force()
    app.mainloop()
