#!/usr/bin/env python3
"""Keep the README's latest-news card in sync with docs/news.json."""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import textwrap
import xml.etree.ElementTree as ET


SVG = "http://www.w3.org/2000/svg"
START = "<!-- proofloom:latest-news:start -->"
END = "<!-- proofloom:latest-news:end -->"
BOARD = "https://trace231.github.io/ProofLoom/news.html"
ET.register_namespace("", SVG)


def latest_entry(entries):
    valid = []
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("title"), str):
            continue
        try:
            date = datetime.date.fromisoformat(entry["date"])
        except (KeyError, TypeError, ValueError):
            continue
        if entry["title"].strip():
            valid.append((date, entry))
    # Keep the board's order when multiple announcements share the newest date.
    return max(valid, key=lambda item: item[0])[1] if valid else None


def render_card(template, latest):
    root = ET.fromstring(template)
    if latest is None:
        return template
    title = " ".join(latest["title"].split())
    lines = textwrap.wrap(title, width=62)
    height = max(144, 92 + 38 * (len(lines) - 1) + 26)
    root.set("height", str(height))
    root.set("viewBox", f"0 0 1200 {height}")
    root.find(f"{{{SVG}}}title").text = f"News — {latest['date']}: {title}"
    for rect in root.findall(f".//{{{SVG}}}rect"):
        if rect.get("width") == "1200":
            rect.set("height", str(height))
    group = root.find(f"{{{SVG}}}g")
    for node in group:
        if node.tag == f"{{{SVG}}}text" and node.text == "NEWS":
            node.set("y", "39")
            node.set("font-size", "14")
            node.set("letter-spacing", "3.5")
        if node.get("d") == "M55 56v12m-6-6h12":
            node.set("transform", "translate(0,-28)")
    date = ET.SubElement(group, f"{{{SVG}}}text", {
        "x": "1070", "y": "38", "fill": "#c5af8b",
        "font-family": "monospace", "font-size": "13", "text-anchor": "end",
    })
    date.text = latest["date"]
    for index, line in enumerate(lines):
        text = ET.SubElement(group, f"{{{SVG}}}text", {
            "x": "55", "y": str(92 + index * 38), "fill": "#f4f1e9",
            "font-family": "Arial,Helvetica,sans-serif", "font-size": "30",
        })
        text.text = line
    return ET.tostring(root, encoding="unicode") + "\n"


def sync(root, check=False):
    entries = json.loads((root / "docs/news.json").read_text())
    if not isinstance(entries, list):
        raise ValueError("docs/news.json must be an array")
    latest = latest_entry(entries)
    template = (root / "docs/assets/news-board.svg").read_text()
    card = render_card(template, latest)
    revision = hashlib.sha256(card.encode()).hexdigest()[:12]
    alt = "News" if latest is None else f"News — {latest['date']}: {latest['title']}"
    alt = " ".join(alt.split()).replace("[", r"\[").replace("]", r"\]")
    block = f"{START}\n[![{alt}](docs/assets/news-latest.svg?v={revision})]({BOARD})\n{END}"
    readme = (root / "README.md").read_text()
    if START in readme and END in readme:
        updated = re.sub(re.escape(START) + r".*?" + re.escape(END),
                         lambda _: block, readme, count=1, flags=re.S)
    elif START in readme or END in readme:
        raise ValueError("README latest-news markers are incomplete")
    else:
        first, newline, rest = readme.partition("\n")
        if not re.fullmatch(r"\[!\[.*\]\(docs/assets/news-(?:board|latest)\.svg[^)]*\)\]\([^)]+\)", first):
            raise ValueError("Cannot locate the README news card")
        updated = block + newline + rest
    outputs = {root / "docs/assets/news-latest.svg": card,
               root / "README.md": updated}
    changed = []
    for path, content in outputs.items():
        if not path.exists() or path.read_text() != content:
            changed.append(str(path.relative_to(root)))
            if not check:
                path.write_text(content)
    if check and changed:
        print("Out of date: " + ", ".join(changed))
        return 1
    print("Latest news card is current" if not changed else "Updated: " + ", ".join(changed))
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raise SystemExit(sync(Path(__file__).resolve().parents[1], args.check))
