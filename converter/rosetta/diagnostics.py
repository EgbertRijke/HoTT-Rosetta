"""Preflight checks that fail visibly instead of losing source material."""

import re
import shutil
import json
from dataclasses import dataclass
from pathlib import Path
from typing import List

from .latex import inventory
from .review import discover_diagram_reviews
from .agda_review import discover_agda_reviews
from .active_files import active_files
from .file_registry import load_file_registry
from .layout import rosetta_directory


@dataclass(frozen=True)
class Diagnostic:
    level: str
    message: str


def repository_checks(root: Path) -> List[Diagnostic]:
    findings: List[Diagnostic] = []
    try:
        active_directory = rosetta_directory(root)
        active_directory.relative_to(root)
        findings.append(
            Diagnostic("ok", f"Active Rosetta directory: {active_directory.relative_to(root)}.")
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        return [Diagnostic("error", f"Invalid project layout: {error}")]

    legacy_name = "archive" + "/legacy-rosetta"
    forbidden = re.compile(
        r"(?:root|ROOT)\s*/\s*[\"']src[\"']|include:\s*src(?:\s|$)"
        r"|archive\s*/\s*[\"']legacy-rosetta[\"']"
        r"|" + re.escape(legacy_name)
    )
    runtime_paths = [root / "rosetta.py", root / "converter" / "rosetta.py"]
    runtime_paths += sorted((root / "converter" / "rosetta").glob("*.py"))
    violations = [path.relative_to(root) for path in runtime_paths if forbidden.search(path.read_text())]
    if violations:
        findings.append(Diagnostic("error", "Active tools reference the backup document tree: " + ", ".join(map(str, violations))))
    else:
        findings.append(Diagnostic("ok", "Active tools do not reference the backup document tree."))
    try:
        sections = inventory(root / "book")
    except (OSError, ValueError) as error:
        return [Diagnostic("error", str(error))]

    if len(sections) != 22:
        findings.append(
            Diagnostic("error", f"Expected 22 book sections, found {len(sections)}.")
        )
    else:
        findings.append(Diagnostic("ok", "Found all 22 book sections in source order."))

    if shutil.which("pandoc") is None:
        findings.append(Diagnostic("error", "Pandoc is not installed or not on PATH."))
    else:
        findings.append(Diagnostic("ok", "Pandoc is available."))

    upstream = root / "external" / "agda-unimath"
    if not upstream.exists() or not any(upstream.iterdir()):
        findings.append(
            Diagnostic(
                "warning",
                "external/agda-unimath is not initialized; provenance checks "
                "will be unavailable. Run: git submodule update --init",
            )
        )
    else:
        findings.append(Diagnostic("ok", "The agda-unimath submodule is initialized."))

    files = active_files(root)
    registered = set(load_file_registry(root).values())
    support = {
        path.name for path in (root / "data" / "support-files").iterdir()
        if path.is_file()
    }
    actual = {path.name for path in active_directory.iterdir() if path.is_file()}
    missing_product = sorted((registered | support) - actual)
    unregistered_product = sorted(actual - registered - support)
    if missing_product or unregistered_product:
        details = []
        if missing_product:
            details.append("missing: " + ", ".join(missing_product))
        if unregistered_product:
            details.append("unregistered: " + ", ".join(unregistered_product))
        findings.append(Diagnostic("error", "Generated product inventory mismatch (" + "; ".join(details) + ")."))
    else:
        findings.append(Diagnostic("ok", f"Generated product inventory is exact ({len(actual)} files)."))
    source_files = {path.name for path in files}
    broken_imports = []
    import_re = re.compile(r"^open import ([^\s]+)", re.MULTILINE)
    for path in files:
        for module in import_re.findall(path.read_text()):
            if module.startswith("Agda."):
                continue
            if f"{module}.lagda.md" not in source_files:
                broken_imports.append(f"{path.name}: {module}")
    if broken_imports:
        findings.append(
            Diagnostic(
                "error",
                "Missing repository-local imports:\n  " + "\n  ".join(broken_imports),
            )
        )
    else:
        findings.append(Diagnostic("ok", "All repository-local imports resolve."))

    try:
        reviews = discover_diagram_reviews(root)
        pending = sum(record.item.state == "pending" for record in reviews)
        stale = sum(record.item.state == "stale" for record in reviews)
        findings.append(
            Diagnostic(
                "ok",
                f"Diagram review data is valid ({len(reviews)} drafts, "
                f"{pending} pending, {stale} stale; review is optional).",
            )
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        findings.append(Diagnostic("error", f"Invalid diagram review data: {error}"))
    try:
        agda_reviews = discover_agda_reviews(root)
        pending = sum(record.state == "pending" for record in agda_reviews)
        needs_review = sum(
            record.state == "needs-further-review" for record in agda_reviews
        )
        stale = sum(record.state == "stale" for record in agda_reviews)
        missing = sum(record.provenance_kind == "missing" for record in agda_reviews)
        code_blocks = len(agda_reviews) - missing
        findings.append(
            Diagnostic(
                "ok",
                f"Agda review data is valid ({code_blocks} code blocks, "
                f"{missing} missing-code items, "
                f"{pending} pending, {needs_review} need further review, "
                f"{stale} stale; review is optional).",
            )
        )
    except (OSError, ValueError, json.JSONDecodeError, RuntimeError) as error:
        findings.append(Diagnostic("error", f"Invalid Agda review data: {error}"))
    return findings
