"""Load and validate curated Agda blocks and their exact provenance."""

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import List


@dataclass(frozen=True)
class AgdaBlock:
    block_id: str
    provenance_kind: str
    item_id: str
    destination: str
    source_file: str
    source_commit: str
    source_start_line: int
    source_end_line: int
    source_sha256: str
    code: str
    order: int
    imports: List[str]
    source_note: str = ""
    conversion_status: str = "ready"
    conversion_note: str = ""
    after_text: str = ""
    display_heading: str = ""

    @classmethod
    def from_dict(cls, value):
        required = {
            "block_id",
            "provenance_kind",
            "item_id",
            "destination",
            "source_file",
            "source_commit",
            "source_start_line",
            "source_end_line",
            "source_sha256",
            "code",
            "order",
            "imports",
        }
        missing = sorted(required - value.keys())
        if missing:
            raise ValueError(f"Agda block is missing fields: {', '.join(missing)}")
        fields = {name: value[name] for name in required}
        fields["source_note"] = value.get("source_note", "")
        fields["conversion_status"] = value.get("conversion_status", "ready")
        fields["conversion_note"] = value.get("conversion_note", "")
        fields["after_text"] = value.get("after_text", "")
        fields["display_heading"] = value.get("display_heading", "")
        block = cls(**fields)
        if block.provenance_kind not in {"exact", "adapted", "handwritten"}:
            raise ValueError(f"Invalid provenance kind for {block.block_id}")
        if block.provenance_kind == "handwritten":
            if any((block.source_file, block.source_commit, block.source_sha256)):
                raise ValueError(f"Handwritten block has an upstream source: {block.block_id}")
            if block.source_start_line != 0 or block.source_end_line != 0:
                raise ValueError(f"Handwritten block has an upstream range: {block.block_id}")
            if not block.source_note.strip():
                raise ValueError(f"Handwritten block needs a source note: {block.block_id}")
        elif block.source_start_line < 1 or block.source_end_line < block.source_start_line:
            raise ValueError(f"Invalid source range for {block.item_id}")
        if not isinstance(block.imports, list) or not all(
            isinstance(module, str) and module for module in block.imports
        ):
            raise ValueError(f"Invalid imports for {block.block_id}")
        if block.conversion_status not in {"ready", "blocked"}:
            raise ValueError(f"Invalid conversion status for {block.block_id}")
        if block.conversion_status == "blocked" and not block.conversion_note.strip():
            raise ValueError(f"Blocked block needs a conversion note: {block.block_id}")
        return block


def load_manifest(path: Path, _seen=None) -> List[AgdaBlock]:
    raw = json.loads(path.read_text())
    if raw.get("format_version") != 1 or not isinstance(raw.get("blocks"), list):
        raise ValueError("Agda manifest must have format_version 1 and a blocks list")
    seen = set() if _seen is None else _seen
    resolved = path.resolve()
    if resolved in seen:
        raise ValueError(f"Agda manifest include cycle: {path}")
    seen.add(resolved)
    blocks = [AgdaBlock.from_dict(value) for value in raw["blocks"]]
    includes = raw.get("includes", [])
    if not isinstance(includes, list) or not all(
        isinstance(name, str) and Path(name).name == name and name.endswith(".json")
        for name in includes
    ):
        raise ValueError("Agda manifest includes must be local JSON filenames")
    for name in includes:
        blocks.extend(load_manifest(path.parent / name, seen))
    seen.remove(resolved)
    identifiers = [block.block_id for block in blocks]
    if len(identifiers) != len(set(identifiers)):
        raise ValueError("Agda manifest contains duplicate block_id values")
    return blocks


def source_digest(lines: List[str], start: int, end: int) -> str:
    """Hash an inclusive, one-based upstream source range."""

    text = "".join(lines[start - 1 : end])
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def verify_block_source(block: AgdaBlock, upstream_root: Path) -> List[str]:
    """Return human-readable errors for one pinned upstream source range."""

    if block.provenance_kind == "handwritten":
        return []
    source = upstream_root / block.source_file
    if not source.is_file():
        return [f"{block.block_id}: source file does not exist: {block.source_file}"]
    lines = source.read_text().splitlines(keepends=True)
    if block.source_end_line > len(lines):
        return [f"{block.block_id}: source range ends beyond the file"]
    errors = []
    digest = source_digest(lines, block.source_start_line, block.source_end_line)
    if digest != block.source_sha256:
        errors.append(f"{block.block_id}: upstream source hash has changed")
    source_code = "".join(
        lines[block.source_start_line - 1 : block.source_end_line]
    ).rstrip("\n")
    code_is_exact = source_code == block.code.rstrip("\n")
    if block.provenance_kind == "exact" and not code_is_exact:
        errors.append(f"{block.block_id}: stored code is not verbatim upstream source")
    if block.provenance_kind == "adapted" and code_is_exact:
        errors.append(f"{block.block_id}: exact code is incorrectly marked adapted")
    return errors


def inject_agda_blocks(document: str, destination: str, blocks: List[AgdaBlock]) -> str:
    """Insert destination blocks at their curated narrative locations."""

    selected = sorted(
        (
            block for block in blocks
            if block.destination == destination and block.conversion_status == "ready"
        ),
        key=lambda block: (block.item_id, block.order, block.block_id),
    )
    result = document
    for block in selected:
        anchor = f"<!-- rosetta-item: {block.item_id}"
        anchor_position = result.find(anchor)
        if anchor_position < 0:
            raise ValueError(f"No item anchor for Agda block {block.block_id}: {block.item_id}")
        if block.after_text:
            text_position = result.find(block.after_text, anchor_position)
            if text_position < 0:
                raise ValueError(
                    f"No narrative anchor for Agda block {block.block_id}: "
                    f"{block.after_text}"
                )
            insertion = text_position + len(block.after_text)
        else:
            end_marker = f"<!-- rosetta-item-end: {block.item_id} -->"
            insertion = result.find(end_marker, anchor_position)
            if insertion < 0:
                next_item = result.find("\n## ", anchor_position)
                insertion = len(result) if next_item < 0 else next_item
        marker = f"<!-- rosetta-agda-block: {block.block_id} -->"
        if marker in result:
            raise ValueError(f"Agda block already inserted: {block.block_id}")
        heading = f"\n\n### {block.display_heading}" if block.display_heading else ""
        fenced = f"{heading}\n\n{marker}\n\n```agda\n{block.code.rstrip()}\n```\n"
        result = result[:insertion].rstrip() + fenced + result[insertion:]
    return result
