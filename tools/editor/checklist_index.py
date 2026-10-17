"""Builds data/checklists/index.json, the rig and checklist index the widget's
in-widget picker reads.

Every sub-folder of the checklists directory is a rig. Every .json file in a
rig folder is a checklist, named by its _meta.name (or the file stem). A file
whose _meta has "hidden": true is left out, which is how reference files
such as unplaced_reference.json stay off the picker. Checklists are listed
by _meta.order (lowest first), then by name. A rig folder containing a file
named ".hidden" is left out entirely.

No Qt dependency so it can run on its own:

    python tools/editor/checklist_index.py data/checklists
"""
import json
import os
import sys
from datetime import date


def build_index(checklists_dir):
    rigs = []
    for rig_name in sorted(os.listdir(checklists_dir), key=str.lower):
        rig_dir = os.path.join(checklists_dir, rig_name)
        if not os.path.isdir(rig_dir):
            continue
        if os.path.exists(os.path.join(rig_dir, ".hidden")):
            continue
        checklists = []
        for fn in sorted(os.listdir(rig_dir), key=str.lower):
            if not fn.endswith(".json"):
                continue
            stem = fn[:-5]
            try:
                with open(os.path.join(rig_dir, fn), "r", encoding="utf-8") as f:
                    data = json.load(f)
            except (OSError, ValueError):
                continue
            meta = data.get("_meta", {}) if isinstance(data, dict) else {}
            if meta.get("hidden"):
                continue
            order = meta.get("order")
            try:
                order = float(order)
            except (TypeError, ValueError):
                order = float("inf")
            checklists.append({"id": stem, "name": meta.get("name") or stem, "_order": order})
        checklists.sort(key=lambda c: (c["_order"], c["name"].lower()))
        for c in checklists:
            del c["_order"]
        if checklists:
            rigs.append({"id": rig_name, "name": rig_name, "checklists": checklists})
    return {"generated": date.today().isoformat(), "rigs": rigs}


def write_index(checklists_dir):
    """Write index.json into checklists_dir and return its path."""
    index = build_index(checklists_dir)
    path = os.path.join(checklists_dir, "index.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(index, f, indent=2, ensure_ascii=False)
        f.write("\n")
    return path


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else os.path.join("data", "checklists")
    print(write_index(target))
