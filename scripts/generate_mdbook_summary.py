#!/usr/bin/env python3
"""Generate mdBook navigation from all.lagda.md and chapter import order."""

import argparse
from pathlib import Path
from book_sources import book_structure, module_name, title


def entry(path, indent=""):
    label = title(path).replace("[", r"\[").replace("]", r"\]")
    return f"{indent}- [{label}]({module_name(path)}.md)"


def summary():
    structure, appendices = book_structure()
    lines = ["# Summary", "", "<!-- Generated from the chapter imports. Do not edit. -->", "",
             "[Home](HOME.md)", "", "# Introduction to Homotopy Type Theory", ""]
    for chapter, children in structure:
        lines.append(entry(chapter))
        lines.extend(entry(child, "  ") for child in children)
    lines += ["", "# Reference", "", "- [All Rosetta modules](all.md)"]
    lines.extend(entry(path) for path in appendices)
    lines += ["- [Formalization benchmark](BENCHMARK.md)",
              "- [About and contributors](ABOUT.md)",
              "- [Building and publishing](WEBSITE.md)",
              "- [Website credits](CREDITS.md)",
              "  - [Reused website code license](LICENSE-agda-unimath.md)", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(summary(), encoding="utf-8")
