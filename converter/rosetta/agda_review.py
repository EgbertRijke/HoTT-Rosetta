"""Side-by-side review records for curated Agda blocks."""

import hashlib
import json
import re
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import List, Optional

from .agda_manifest import AgdaBlock, load_manifest
from .editing import apply_edit, preview_edit
from .generate import candidate_exercise, candidate_section
from .latex import inventory
from .agda_typecheck import typecheck_result
from .missing_agda import discover_missing_agda
from .layout import rosetta_directory


AGDA_REVIEW_STATES = (
    "pending",
    "needs-further-review",
    "approved",
    "rejected",
)


@dataclass(frozen=True)
class AgdaReviewRecord:
    block_id: str
    item_id: str
    destination: str
    provenance_kind: str
    statement: str
    project_code: str
    source_code: str
    source_location: str
    source_commit: str
    exact_match: bool
    document_sha256: str
    conversion_status: str
    conversion_note: str
    state: str
    comments: List["ReviewComment"]
    typecheck_status: str = "not-checked"
    typecheck_message: str = ""
    typecheck_candidate: str = ""

    def to_dict(self):
        return asdict(self)


@dataclass(frozen=True)
class ReviewComment:
    author: str
    text: str


def missing_agda_block_id(destination: str, item_id: str) -> str:
    """Return the stable review identifier for an item without Agda."""

    return f"missing-agda-{destination.removesuffix('.lagda.md')}-{item_id}"


def _source_code(root: Path, block: AgdaBlock) -> str:
    if block.provenance_kind == "handwritten":
        return ""
    lines = (root / "external" / "agda-unimath" / block.source_file).read_text().splitlines(
        keepends=True
    )
    return "".join(lines[block.source_start_line - 1 : block.source_end_line]).rstrip(
        "\n"
    )


def _statement(document: str, block: AgdaBlock) -> str:
    anchor = f"<!-- rosetta-item: {block.item_id}"
    start = document.find(anchor)
    if start < 0:
        raise ValueError(f"Missing item marker for {block.block_id}")
    heading_start = document.rfind("\n## ", 0, start)
    start = heading_start + 1 if heading_start >= 0 else start
    end = document.find("\n## ", start + 1)
    if end < 0:
        end = len(document)
    value = document[start:end]
    agda_marker = value.find("<!-- rosetta-agda-block:")
    if agda_marker >= 0:
        value = value[:agda_marker]
    value = re.sub(r"<!--.*?-->\s*", "", value, flags=re.DOTALL)
    return value.strip()


def _generated_block_code(document: str, block: AgdaBlock) -> str:
    marker = f"<!-- rosetta-agda-block: {block.block_id} -->"
    position = document.find(marker)
    if position < 0:
        return block.code.rstrip("\n")
    match = re.match(r"\s*```agda\s*\n(.*?)^```", document[position + len(marker) :], re.DOTALL | re.MULTILINE)
    if not match:
        raise ValueError(f"Malformed generated Agda block: {block.block_id}")
    return match.group(1).rstrip("\n")


def _exercise_statement(document: str, before: Optional[int] = None) -> str:
    """Return the exercise prompt nearest to the associated Agda block."""

    limit = len(document) if before is None else before
    headings = list(
        re.finditer(r"^##\s+Problem statement\s*$", document[:limit], re.MULTILINE)
    )
    if not headings:
        return ""
    start = headings[-1].start()
    following = re.search(r"^##\s+", document[headings[-1].end() :], re.MULTILINE)
    end = (
        headings[-1].end() + following.start()
        if following
        else len(document)
    )
    return document[start:end].strip()


def _review_digest(record: AgdaReviewRecord) -> str:
    value = "\0".join(
        (
            record.statement,
            record.project_code,
            record.source_code,
            record.source_location,
            record.source_commit,
            record.provenance_kind,
            record.document_sha256,
            record.conversion_status,
            record.conversion_note,
        )
    )
    return hashlib.sha256(value.encode()).hexdigest()


def _empty_store() -> dict:
    return {"version": 1, "blocks": {}}


def load_agda_review_store(path: Path) -> dict:
    if not path.exists():
        return _empty_store()
    store = json.loads(path.read_text())
    if store.get("version") != 1 or not isinstance(store.get("blocks"), dict):
        raise ValueError(f"Invalid Agda review data: {path}")
    return store


def _with_stored_review(record: AgdaReviewRecord, store: dict) -> AgdaReviewRecord:
    saved = store["blocks"].get(record.block_id)
    if not saved:
        return record
    raw_comments = saved.get("comments", [])
    if not isinstance(raw_comments, list):
        raise ValueError(f"Invalid comments for Agda block {record.block_id}")
    comments = []
    for item in raw_comments:
        if isinstance(item, str):
            comments.append(ReviewComment(author="", text=item))
        elif (
            isinstance(item, dict)
            and isinstance(item.get("author"), str)
            and isinstance(item.get("text"), str)
            and item["text"].strip()
        ):
            comments.append(ReviewComment(author=item["author"], text=item["text"]))
        else:
            raise ValueError(f"Invalid comments for Agda block {record.block_id}")
    state = saved.get("state", "pending")
    if state not in AGDA_REVIEW_STATES:
        raise ValueError(f"Invalid review state for Agda block {record.block_id}")
    if saved.get("review_sha256") and saved.get("review_sha256") != _review_digest(record):
        state = "stale"
    return replace(record, state=state, comments=comments)


def discover_agda_reviews(root: Path) -> List[AgdaReviewRecord]:
    """Build records from generated files, manifest data, and pinned sources."""

    blocks = load_manifest(root / "data" / "agda-blocks.json")
    sections = inventory(root / "book")
    store = load_agda_review_store(root / "data" / "agda-reviews.json")
    documents = {}
    generated = {}
    typechecks = {}
    records = []
    for block in blocks:
        match = re.match(r"section-(\d+)-(\d+)-", block.destination)
        fallback_statement = ""
        if match:
            chapter, subsection = map(int, match.groups())
            key = (chapter, subsection)
            if key not in documents:
                _, documents[key] = candidate_section(
                    sections[chapter - 1], subsection, blocks
                )
            fallback_statement = _statement(documents[key], block)
        else:
            exercise_match = re.match(r"exercise-(\d+)-(\d+)-", block.destination)
            if exercise_match:
                chapter, exercise = map(int, exercise_match.groups())
                key = (chapter, "exercise", exercise)
                if key not in documents:
                    _, documents[key] = candidate_exercise(
                        root, sections[chapter - 1], exercise, blocks
                    )
                fallback_statement = _exercise_statement(documents[key])
                if not fallback_statement:
                    fallback_statement = _statement(documents[key], block)
            else:
                raise ValueError(
                    f"Unsupported Agda review destination: {block.destination}"
                )
        generated_path = rosetta_directory(root) / block.destination
        if block.destination not in generated:
            generated[block.destination] = generated_path.read_text()
        generated_text = generated[block.destination]
        project_code = _generated_block_code(generated_text, block)
        statement = (
            _exercise_statement(generated_text)
            if block.item_id.startswith("exercise-")
            else _statement(generated_text, block)
        ) or fallback_statement
        upstream = _source_code(root, block)
        if block.destination not in typechecks:
            typechecks[block.destination] = typecheck_result(root, block.destination)
        checked = typechecks[block.destination]
        record = AgdaReviewRecord(
            block_id=block.block_id,
            item_id=block.item_id,
            destination=block.destination,
            provenance_kind=block.provenance_kind,
            statement=statement,
            project_code=project_code,
            source_code=upstream,
            source_location=(
                f"{block.source_file}:{block.source_start_line}-{block.source_end_line}"
                if block.source_file else block.source_note
            ),
            source_commit=block.source_commit,
            exact_match=project_code == upstream,
            document_sha256=hashlib.sha256(generated_text.encode()).hexdigest(),
            conversion_status=block.conversion_status,
            conversion_note=block.conversion_note,
            state="pending",
            comments=[],
            typecheck_status=checked.get("status", "not-checked"),
            typecheck_message=checked.get("message", ""),
            typecheck_candidate=checked.get("candidate", ""),
        )
        records.append(_with_stored_review(record, store))
    for item in discover_missing_agda(root):
        generated_text = (rosetta_directory(root) / item.destination).read_text()
        record = AgdaReviewRecord(
            block_id=missing_agda_block_id(item.destination, item.item_id),
            item_id=item.item_id,
            destination=item.destination,
            provenance_kind="missing",
            statement=item.statement,
            project_code="",
            source_code="",
            source_location="No applicable agda-unimath source recorded.",
            source_commit="",
            exact_match=False,
            document_sha256=hashlib.sha256(generated_text.encode()).hexdigest(),
            conversion_status="missing",
            conversion_note="No candidate Agda block has been curated for this item.",
            state="pending",
            comments=[],
            typecheck_status="not-applicable",
        )
        records.append(_with_stored_review(record, store))
    return records


def update_agda_review(
    root: Path,
    block_id: str,
    *,
    state: Optional[str] = None,
    comment: Optional[str] = None,
    comment_author: str = "Reviewer",
    current_record: Optional[AgdaReviewRecord] = None,
) -> Path:
    if current_record is None:
        records = discover_agda_reviews(root)
        matches = [record for record in records if record.block_id == block_id]
        if not matches:
            raise ValueError(f"Agda block not found: {block_id}")
        current = matches[0]
    else:
        if current_record.block_id != block_id:
            raise ValueError(f"Agda block not found: {block_id}")
        current = current_record
    if state is not None and state not in AGDA_REVIEW_STATES:
        raise ValueError(f"Unsupported Agda review state: {state}")
    if current.provenance_kind == "missing" and state not in {None, "pending"}:
        raise ValueError(
            "An item with no Agda code cannot be approved, rejected, or marked "
            "as needing further review"
        )
    path = root / "data" / "agda-reviews.json"
    if not path.exists():
        path.write_text(json.dumps(_empty_store(), indent=2) + "\n")
    store = load_agda_review_store(path)
    saved = store["blocks"].setdefault(block_id, {})
    saved["review_sha256"] = _review_digest(current)
    if state is not None:
        saved["state"] = state
    else:
        saved.setdefault("state", current.state if current.state != "stale" else "pending")
    comments = saved.setdefault("comments", [])
    if comment is not None:
        cleaned = comment.strip()
        if not cleaned:
            raise ValueError("Review comments cannot be empty")
        comments.append({"author": comment_author.strip() or "Reviewer", "text": cleaned})
    new_text = json.dumps(store, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    apply_edit(preview_edit(path, new_text), root)
    return path
