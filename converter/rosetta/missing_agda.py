"""Discover generated mathematical items without curated Agda."""

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional

from .audit import extract_existing_agda_blocks
from .agda_manifest import load_manifest
from .latex import inventory, numbered_items, subsection_body
from .layout import rosetta_directory
from .file_registry import registered_filename


NUMBERED_MARKDOWN_HEADING_RE = re.compile(
    r"^#{2,6}\s+(?:Theorem|Corollary|Lemma|Proposition|Definition|"
    r"Quasi-definition|Remark|Example|Axiom|Postulate)\s+(\d+\.\d+\.\d+)\b.*$",
    re.MULTILINE | re.IGNORECASE,
)


@dataclass(frozen=True)
class MissingAgdaItem:
    item_id: str
    kind: str
    number: str
    destination: str
    statement: str


def load_agda_coverage(root: Path) -> set[str]:
    """Load files explicitly confirmed to have complete required Agda coverage."""

    path = root / "data" / "agda-coverage.json"
    raw = json.loads(path.read_text())
    files = raw.get("complete_files")
    if raw.get("format_version") != 1 or not isinstance(files, list):
        raise ValueError("Agda coverage data must have format_version 1 and complete_files")
    if len(files) != len(set(files)):
        raise ValueError("Agda coverage data contains duplicate filenames")
    for name in files:
        if not isinstance(name, str) or Path(name).name != name or not name.endswith(".lagda.md"):
            raise ValueError(f"Invalid complete Agda coverage filename: {name!r}")
        if not (rosetta_directory(root) / name).is_file():
            raise ValueError(f"Complete Agda coverage file does not exist: {name}")
    return set(files)


def load_explicit_agda_gaps(root: Path) -> List[MissingAgdaItem]:
    """Load reviewed gaps that automatic numbered-item discovery cannot express."""

    path = root / "data" / "agda-gaps.json"
    if not path.exists():
        return []
    raw = json.loads(path.read_text())
    items = raw.get("items")
    if raw.get("format_version") != 1 or not isinstance(items, list):
        raise ValueError("Agda gap data must have format_version 1 and items")
    result = []
    seen = set()
    for item in items:
        if not isinstance(item, dict):
            raise ValueError("Each Agda gap must be an object")
        required = ("item_id", "kind", "number", "destination", "statement")
        if any(not isinstance(item.get(key), str) or not item[key].strip() for key in required):
            raise ValueError("Each Agda gap must have nonempty string fields")
        destination = item["destination"]
        if Path(destination).name != destination or not destination.endswith(".lagda.md"):
            raise ValueError(f"Invalid Agda gap destination: {destination!r}")
        if not (rosetta_directory(root) / destination).is_file():
            raise ValueError(f"Agda gap destination does not exist: {destination}")
        key = (destination, item["item_id"])
        if key in seen:
            raise ValueError(f"Duplicate Agda gap: {destination} {item['item_id']}")
        seen.add(key)
        result.append(MissingAgdaItem(**{key: item[key] for key in required}))
    return result


def _generated_section(root: Path, chapter: int, subsection: int) -> Optional[Path]:
    path = rosetta_directory(root) / registered_filename(
        root, "section", chapter, subsection
    )
    return path if path.is_file() else None


def _generated_statement(markdown: str, number: str) -> str:
    headings = list(NUMBERED_MARKDOWN_HEADING_RE.finditer(markdown))
    for index, heading in enumerate(headings):
        if heading.group(1) != number:
            continue
        end = headings[index + 1].start() if index + 1 < len(headings) else len(markdown)
        return markdown[heading.start() : end].strip()
    return ""


def discover_missing_agda(root: Path) -> List[MissingAgdaItem]:
    """List generated numbered items with no curated Agda block."""

    result = load_explicit_agda_gaps(root)
    complete_files = load_agda_coverage(root)
    curated = {
        (block.destination, block.item_id)
        for block in load_manifest(root / "data" / "agda-blocks.json")
        if block.conversion_status in {"ready", "exercise"}
    }
    for chapter in inventory(root / "book"):
        for subsection in range(1, len(chapter.subsections) + 1):
            destination = _generated_section(root, chapter.number, subsection)
            if destination is None:
                continue
            if destination.name in complete_files:
                continue
            _, source = subsection_body(chapter.path, subsection)
            existing_ids = {
                block.item_id
                for block in extract_existing_agda_blocks(destination)
                if block.item_id
            }
            markdown = destination.read_text()
            for item in numbered_items(source, chapter.number, subsection):
                if (
                    item.stable_id in existing_ids
                    or (destination.name, item.stable_id) in curated
                ):
                    continue
                statement = _generated_statement(markdown, item.number)
                # A source item absent from the generated document is a prose
                # coverage issue, not an item whose Agda is missing.
                if not statement:
                    continue
                result.append(
                    MissingAgdaItem(
                        item_id=item.stable_id,
                        kind=item.kind,
                        number=item.number,
                        destination=destination.name,
                        statement=statement,
                    )
                )
    return result
