# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Custom JotForm widgets for EMS (Emergency Medical Services) operational management. Each widget is a self-contained HTML file with inline JavaScript and CSS, deployed directly to JotForm's custom widget platform — no build process, no package manager, no transpilation.

## Repository Structure

```
widgets/
  ems-inventory-checklist.html   # Multi-area inventory management (~4300 lines)
  oxygen-supply-check.html       # Oxygen cylinder status tracking (~700 lines)
  news-bulletin.html             # Announcements & review schedule (~530 lines)
data/
  announcements.json             # Remote announcements data for news-bulletin
```

## Architecture

**Single-file widgets**: Each `.html` file is entirely self-contained — HTML structure, CSS styles, and all JavaScript are inline. The only external dependency is the JotForm Custom Widget SDK (`JFCustomWidget`).

**State management layers** (ems-inventory-checklist):
1. In-memory globals (`itemStates`, `restockStatus`, `taggedAreas`, `brokenSeals`)
2. localStorage with 8-hour expiry (device-level persistence)
3. JotForm widget value (in-form persistence via `JFCustomWidget.sendSubmit`)
4. JotForm Submissions API (cross-device sync for sealed state)

**Inventory data format**: Parsed from a custom text format configured in JotForm widget settings:
```
Area Name: Driver Compartment
Sealable: yes
Safety Equipment
Fire Extinguisher|1

Area Name: Patient Compartment
>Monitoring
  >Cardiac
  Cardiac Monitor|1
```
- `Area Name:` declares areas; `>` prefix creates subcategory hierarchy; `Item|quantity` defines items.

**Key naming convention**: State keys use `areaName::categoryName::itemName` format throughout.

## Development Notes

- **No build/test/lint commands** — widgets are plain HTML files edited directly.
- **Deployment**: Upload HTML file to JotForm's custom widget platform or reference by URL.
- **JotForm API**: The inventory widget optionally uses the Submissions API for cross-device sealed state sync. The API key is configured by the form admin in widget settings.
- **HTML entity encoding**: JotForm's Submissions API HTML-entity-encodes stored values. The inventory widget includes custom decode logic to match area names against stored state.
- **ES5 JavaScript**: No modern module syntax. All code uses vanilla JS with direct DOM manipulation.

## Branch Naming Convention

Feature branches: `claude/[description]-[random-code]` (e.g., `claude/fix-restock-subcategories-XNW8e`)

## Versioning

The inventory widget maintains an internal version and changelog displayed via an in-app dialog. When making changes to `ems-inventory-checklist.html`, update the version number and add a changelog entry in the `changelogEntries` array.
