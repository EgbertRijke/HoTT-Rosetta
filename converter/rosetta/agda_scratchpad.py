"""Temporary, typecheckable Agda drafts for curated review blocks."""

import hashlib
import json
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Optional

from .agda_edit import _find_block
from .agda_manifest import load_manifest
from .agda_typecheck import candidate_for_destination
from .editing import apply_edit, preview_edit
from .generate import typecheck_candidate


@dataclass(frozen=True)
class AgdaScratchpad:
    block_id: str
    code: str
    adaptation_note: str
    base_manifest_digest: str
    status: str = "not-checked"
    message: str = ""
    checked_sha256: str = ""


def _path(root: Path) -> Path:
    return root / "_build" / "rosetta-review" / "agda-scratchpads.json"


def _ensure_store(root: Path) -> Path:
    path = _path(root)
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('{\n  "version": 1,\n  "drafts": {}\n}\n')
    return path


def _load(root: Path) -> dict:
    path = _ensure_store(root)
    value = json.loads(path.read_text())
    if value.get("version") != 1 or not isinstance(value.get("drafts"), dict):
        raise ValueError(f"Invalid Agda scratchpad data: {path}")
    return value


def load_scratchpad(root: Path, block_id: str) -> Optional[AgdaScratchpad]:
    value = _load(root)["drafts"].get(block_id)
    return AgdaScratchpad(**value) if value else None


def _code_digest(code: str) -> str:
    return hashlib.sha256(code.encode()).hexdigest()


def _save(root: Path, draft: Optional[AgdaScratchpad], block_id: str) -> Path:
    path = _ensure_store(root)
    store = _load(root)
    if draft is None:
        store["drafts"].pop(block_id, None)
    else:
        store["drafts"][block_id] = asdict(draft)
    text = json.dumps(store, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    return apply_edit(preview_edit(path, text), root)


def save_scratchpad(
    root: Path, block_id: str, code: str, adaptation_note: str = ""
) -> AgdaScratchpad:
    cleaned = code.rstrip("\n")
    if not cleaned.strip():
        raise ValueError("Scratchpad Agda code cannot be empty")
    manifest_path, _, _ = _find_block(root, block_id)
    base_digest = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
    draft = AgdaScratchpad(
        block_id=block_id,
        code=cleaned,
        adaptation_note=adaptation_note.strip(),
        base_manifest_digest=base_digest,
    )
    _save(root, draft, block_id)
    return draft


def discard_scratchpad(root: Path, block_id: str) -> None:
    _find_block(root, block_id)
    _save(root, None, block_id)


def run_scratchpad_typecheck(root: Path, block_id: str) -> AgdaScratchpad:
    draft = load_scratchpad(root, block_id)
    if draft is None:
        raise ValueError("No scratchpad draft has been saved")
    blocks = load_manifest(root / "data" / "agda-blocks.json")
    matches = [block for block in blocks if block.block_id == block_id]
    if len(matches) != 1:
        raise ValueError(f"Agda block not found: {block_id}")
    block = matches[0]
    # A blocked source excerpt is omitted by the renderer. Check the supplied
    # draft as active code, or a passing result would say nothing about it.
    replacement = replace(
        block,
        code=draft.code,
        conversion_status=(
            "ready" if block.conversion_status == "blocked" else block.conversion_status
        ),
    )
    overlaid = [replacement if block.block_id == block_id else block for block in blocks]
    filename, document = candidate_for_destination(
        root, replacement.destination, blocks=overlaid
    )
    returncode, output, _ = typecheck_candidate(root, filename, document)
    checked = replace(
        draft,
        status="passed" if returncode == 0 else "failed",
        message=output.strip(),
        checked_sha256=_code_digest(draft.code),
    )
    _save(root, checked, block_id)
    return checked


def promotion_scratchpad(root: Path, block_id: str) -> AgdaScratchpad:
    draft = load_scratchpad(root, block_id)
    if draft is None:
        raise ValueError("No scratchpad draft has been saved")
    if draft.status != "passed" or draft.checked_sha256 != _code_digest(draft.code):
        raise ValueError("The current scratchpad draft must pass Agda before promotion")
    manifest_path, _, _ = _find_block(root, block_id)
    current = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
    if current != draft.base_manifest_digest:
        raise ValueError("The curated manifest changed after this draft was started")
    return draft
