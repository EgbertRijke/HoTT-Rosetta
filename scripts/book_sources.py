#!/usr/bin/env python3
"""Read the book's existing module structure; fail on missing/orphaned pages."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "rosetta-book"
SUFFIX = ".lagda.md"


def module_name(path):
    return path.name.removesuffix(SUFFIX)


def agda_code(text):
    return "\n".join(re.findall(r"^```agda\s*\n(.*?)^```\s*$", text, re.M | re.S))


def imports(path):
    return re.findall(r"^\s*(?:open\s+)?import\s+([^\s;]+)",
                      agda_code(path.read_text(encoding="utf-8")), re.M)


def title(path):
    match = re.search(r"^#\s+(.+?)\s*$", path.read_text(encoding="utf-8"), re.M)
    if not match:
        raise ValueError(f"Missing title: {path.relative_to(ROOT)}")
    return match[1]


def book_structure(source=SOURCE):
    pages = {module_name(path): path for path in source.glob("*" + SUFFIX)}
    if "all" not in pages:
        raise ValueError("Missing rosetta-book/all.lagda.md")
    for name, path in pages.items():
        declaration = re.search(r"^module\s+(\S+)\s+where\s*$",
                                agda_code(path.read_text(encoding="utf-8")), re.M)
        if not declaration or declaration[1] != name:
            raise ValueError(f"Module declaration does not match filename: {path.name}")
        title(path)
        for dependency in imports(path):
            if dependency not in pages and not dependency.startswith("Agda."):
                raise ValueError(f"{name}: missing imported module {dependency}")

    chapters = imports(pages["all"])
    expected_chapters = {name for name in pages if name.startswith("chapter-")}
    if len(chapters) != len(set(chapters)) or set(chapters) != expected_chapters:
        raise ValueError("all.lagda.md must import every chapter exactly once")
    listed = {"all", *chapters}
    structure = []
    for chapter in chapters:
        children = imports(pages[chapter])
        for child in children:
            if child in listed:
                raise ValueError(f"Duplicate sidebar entry: {child}")
            listed.add(child)
        structure.append((pages[chapter], [pages[child] for child in children]))
    orphans = {name for name in pages if name.startswith(("section-", "exercise-"))} - listed
    if orphans:
        raise ValueError(f"Sections/exercises missing from chapter imports: {sorted(orphans)}")
    # Support modules are included only when reachable through the compilation root.
    reachable = set()

    def visit(name):
        if name in reachable or name not in pages:
            return
        reachable.add(name)
        for dependency in imports(pages[name]):
            visit(dependency)

    visit("all")
    if reachable != set(pages):
        raise ValueError(f"Modules not imported by all: {sorted(set(pages) - reachable)}")
    appendices = [pages[name] for name in sorted(set(pages) - listed)]
    return structure, appendices


if __name__ == "__main__":
    structure, appendices = book_structure()
    count = 1 + len(appendices) + sum(1 + len(children) for _, children in structure)
    print(f"Validated {count} modules in {len(structure)} chapters.")
