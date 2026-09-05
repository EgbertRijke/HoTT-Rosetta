"""Safe candidate-file generation and deterministic naming."""

import re
import unicodedata
import shutil
import subprocess
from pathlib import Path

from .latex import SectionSource, exercise_bodies, section_introduction
from .render import render_fragment, render_section
from .agda_manifest import AgdaBlock, inject_agda_blocks
from .file_registry import registered_filename
from .layout import rosetta_directory


def agda_typecheck_options(agda: str) -> list[str]:
    """Return portable Agda options, suppressing interfaces when supported."""

    help_process = subprocess.run(
        [agda, "--help"],
        text=True,
        capture_output=True,
        check=False,
    )
    options = ["--no-libraries"]
    if "--no-write-interfaces" in help_process.stdout + help_process.stderr:
        options.append("--no-write-interfaces")
    return options


def slugify(title: str) -> str:
    value = title.replace("Martin-L\\\"of", "Martin-Lof")
    value = value.replace("'", "").replace("’", "")
    value = re.sub(
        r"\\texorpdfstring\{\$\\N\$\}\{[^{}]+\}", "natural numbers", value
    )
    value = value.replace(r"\N", "N")
    value = value.replace("\\texorpdfstring", "")
    value = re.sub(r"\$([^$]+)\$", r"\1", value)
    value = re.sub(r"\\[A-Za-z@]+", " ", value)
    value = unicodedata.normalize("NFKD", value)
    value = value.encode("ascii", "ignore").decode("ascii").lower()
    value = re.sub(r"[^a-z0-9]+", "-", value).strip("-")
    if not value:
        raise ValueError(f"Cannot make a filename slug from title: {title!r}")
    return value


def section_module_name(chapter: int, subsection: int, title: str) -> str:
    return f"section-{chapter}-{subsection}-{slugify(title)}"


def candidate_section(
    section: SectionSource, subsection: int, blocks=None
) -> tuple[str, str]:
    if subsection < 1 or subsection > len(section.subsections):
        raise IndexError(f"Chapter {section.number} has no section {subsection}")
    title = section.subsections[subsection - 1]
    prefix = f"section-{section.number}-{subsection}-"
    curated_destinations = {
        block.destination
        for block in (blocks or [])
        if block.destination.startswith(prefix)
    }
    if len(curated_destinations) > 1:
        raise ValueError(
            f"Multiple curated destinations match {prefix}: "
            + ", ".join(sorted(curated_destinations))
        )
    root = section.path.parent.parent
    filename = registered_filename(root, "section", section.number, subsection)
    if curated_destinations and curated_destinations != {filename}:
        raise ValueError(
            f"Curated destination does not match registered filename: {filename}"
        )
    module = filename.removesuffix(".lagda.md")
    rendered = render_section(section.path, section.number, subsection)
    destination_blocks = [
        block for block in (blocks or [])
        if block.destination == module + ".lagda.md"
        and block.conversion_status in {"ready", "exercise"}
    ]
    imports = []
    for block in destination_blocks:
        if block.conversion_status != "ready":
            continue
        for imported_module in block.imports:
            if imported_module not in imports:
                imports.append(imported_module)
    import_text = (
        "\n" + "\n".join(f"open import {name}" for name in imports) + "\n"
        if imports
        else ""
    )
    heading_end = rendered.find("\n")
    document = (
        rendered[: heading_end + 1]
        + "\n```agda\n"
        + f"module {module} where\n"
        + import_text
        + "```\n"
        + rendered[heading_end + 1 :]
    )
    if destination_blocks:
        document = inject_agda_blocks(document, filename, destination_blocks)
    return filename, document


def candidate_exercise(
    root: Path, section: SectionSource, number: int, blocks=None
) -> tuple[str, str]:
    bodies = exercise_bodies(section.path)
    if number < 1 or number > len(bodies):
        raise IndexError(f"Chapter {section.number} has no exercise {number}")
    filename = registered_filename(root, "exercise", section.number, number)
    module = filename.removesuffix(".lagda.md")
    selected = [
        block for block in (blocks or [])
        if block.destination == filename
        and block.conversion_status in {"ready", "exercise"}
    ]
    imports = []
    for block in selected:
        if block.conversion_status != "ready":
            continue
        for imported in block.imports:
            if imported not in imports:
                imports.append(imported)
    import_text = "".join(f"open import {name}\n" for name in imports)
    prose = render_fragment(section.path, bodies[number - 1])
    document = (
        f"# Exercise {section.number}.{number}\n\n"
        f"```agda\nmodule {module} where\n\n{import_text}```\n\n"
        f"## Problem statement\n\n{prose}\n## Solution\n\n"
        f"<!-- rosetta-item: exercise-{section.number}-{number} -->\n"
        + ("\nNo formalization has been curated yet.\n" if not selected else "")
    )
    document = clean_document(document)
    if selected:
        document = inject_agda_blocks(document, filename, selected)
    return filename, document


def candidate_chapter(root: Path, section: SectionSource) -> tuple[str, str]:
    filename = registered_filename(root, "chapter", section.number)
    module = filename.removesuffix(".lagda.md")
    imports = []
    for subsection, _ in enumerate(section.subsections, 1):
        imports.append(
            registered_filename(root, "section", section.number, subsection)
            .removesuffix(".lagda.md")
        )
    for number in range(1, section.exercise_count + 1):
        imports.append(
            registered_filename(root, "exercise", section.number, number)
            .removesuffix(".lagda.md")
        )
    intro = render_fragment(section.path, section_introduction(section.path))
    document = (
        f"# Chapter {section.number} {slug_title(section.title)}\n\n"
        f"```agda\nmodule {module} where\n\n"
        + "\n".join(f"open import {name}" for name in imports)
        + f"\n```\n\n{intro}"
    )
    return filename, clean_document(document)


def slug_title(title: str) -> str:
    """Conservative readable title for aggregate headings."""
    from .math_text import normalize_heading_title
    return normalize_heading_title(title)


def clean_document(document: str) -> str:
    from .markdown import clean_markdown
    return clean_markdown(document)


def write_candidate(root: Path, filename: str, document: str) -> Path:
    destination = rosetta_directory(root) / filename
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(document)
    return destination


def write_support_files(root: Path) -> list[Path]:
    """Copy versioned support modules into the active Rosetta directory."""

    destination = rosetta_directory(root)
    destination.mkdir(parents=True, exist_ok=True)
    written = []
    for source in sorted((root / "data" / "support-files").iterdir()):
        if not source.is_file():
            continue
        target = destination / source.name
        target.write_text(source.read_text())
        written.append(target)
    return written


def typecheck_candidate(root: Path, filename: str, document: str):
    """Typecheck candidate content under a temporary non-conflicting module."""

    agda = shutil.which("agda")
    if agda is None:
        raise RuntimeError("Agda is not installed or not on PATH")
    original_module = filename.removesuffix(".lagda.md")
    candidate_module = "candidate-" + original_module
    staged = root / "_build" / "rosetta-typecheck" / (
        candidate_module + ".lagda.md"
    )
    staged.parent.mkdir(parents=True, exist_ok=True)
    staged.write_text(
        document.replace(
            f"module {original_module} where",
            f"module {candidate_module} where",
            1,
        )
    )
    process = subprocess.run(
        [
            agda,
            *agda_typecheck_options(agda),
            "-i",
            str(staged.parent),
            "-i",
            str(rosetta_directory(root)),
            str(staged),
        ],
        cwd=root,
        text=True,
        capture_output=True,
        check=False,
    )
    return process.returncode, process.stdout + process.stderr, staged
