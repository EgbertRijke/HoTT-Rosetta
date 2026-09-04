"""Turn Pandoc's conservative Markdown into Rosetta section structure."""

import re
from pathlib import Path
from typing import Dict, List

from .latex import ITEM_NAMES, numbered_items, subsection_body
from .pandoc import latex_to_gfm
from .math_text import normalize_heading_title, normalize_markdown_math
from .references import build_reference_index, resolve_markdown_references
from .markdown import clean_markdown
from .tables import normalize_html_tables


DIV_OPEN_RE = re.compile(r'^<div class="([^"]+)">\s*$')
DIV_CLOSE_RE = re.compile(r"^</div>\s*$")


def _heading_anchor_slug(title: str) -> str:
    """Return a readable, deterministic identifier for an unnumbered heading."""

    value = title.replace("`ℕ`", "natural numbers").replace("ℕ", "natural numbers")
    value = re.sub(r"[`*_]", "", value).lower()
    return re.sub(r"[^a-z0-9]+", "-", value).strip("-")


def _anchor_unnumbered_headings(
    markdown: str, section: int, subsection: int
) -> str:
    """Give level-three section headings stable Agda insertion anchors."""

    output: List[str] = []
    occurrences: Dict[str, int] = {}
    for line in markdown.splitlines():
        output.append(line)
        if not line.startswith("### "):
            continue
        slug = _heading_anchor_slug(line.removeprefix("### "))
        occurrences[slug] = occurrences.get(slug, 0) + 1
        suffix = "" if occurrences[slug] == 1 else f"-{occurrences[slug]}"
        output.extend(
            [
                "",
                f"<!-- rosetta-item: subheading-{section}.{subsection}-{slug}{suffix} -->",
            ]
        )
    return "\n".join(output).strip() + "\n"


def _structure_theorem_divs(markdown: str, expected_items) -> str:
    """Replace Pandoc HTML theorem divs with numbered Markdown headings."""

    item_index = 0
    stack: List[tuple[str, str]] = []
    output: List[str] = []
    pending_item_end = ""
    theorem_classes = set(ITEM_NAMES)
    for line in markdown.splitlines():
        opening = DIV_OPEN_RE.match(line)
        if pending_item_end and not (
            opening and opening.group(1) in {"proof", "constr"}
        ) and line.strip():
            output.extend(
                ["", f"<!-- rosetta-item-end: {pending_item_end} -->", ""]
            )
            pending_item_end = ""
        if opening:
            class_name = opening.group(1)
            if class_name in theorem_classes:
                if item_index >= len(expected_items):
                    raise ValueError(
                        f"Pandoc found an unexpected {class_name} environment"
                    )
                item = expected_items[item_index]
                item_index += 1
                marker = f"<!-- rosetta-item: {item.stable_id}"
                if item.label:
                    marker += f"; latex-label: {item.label}"
                marker += " -->"
                output.extend([f"## {item.kind} {item.number}", "", marker, ""])
                stack.append((class_name, item.stable_id))
            elif class_name == "proof":
                stack.append((class_name, pending_item_end))
                pending_item_end = ""
                output.extend(["### Proof", ""])
            elif class_name == "constr":
                stack.append((class_name, pending_item_end))
                pending_item_end = ""
                output.extend(["### Construction", ""])
            else:
                stack.append((class_name, ""))
                # Unknown divs remain explicit diagnostics in the preview.
                output.extend([f"<!-- unsupported LaTeX environment: {class_name} -->", ""])
            continue
        if DIV_CLOSE_RE.match(line) and stack:
            class_name, stable_id = stack.pop()
            if class_name in theorem_classes:
                pending_item_end = stable_id
            elif class_name in {"proof", "constr"} and stable_id:
                output.extend(["", f"<!-- rosetta-item-end: {stable_id} -->", ""])
            continue
        output.append(line)
    if pending_item_end:
        output.extend(["", f"<!-- rosetta-item-end: {pending_item_end} -->", ""])
    if item_index != len(expected_items):
        missing = ", ".join(item.number for item in expected_items[item_index:])
        raise ValueError(f"Pandoc did not preserve numbered items: {missing}")
    return "\n".join(output).strip() + "\n"


def render_section(source_path: Path, section: int, subsection: int) -> str:
    title, body = subsection_body(source_path, subsection)
    expected = numbered_items(body, section, subsection)
    markdown = normalize_markdown_math(latex_to_gfm(body))
    markdown = resolve_markdown_references(
        markdown, build_reference_index(source_path.parent)
    )
    markdown = normalize_html_tables(markdown)
    structured = _structure_theorem_divs(markdown, expected)
    structured = _anchor_unnumbered_headings(structured, section, subsection)
    return clean_markdown(
        f"# Section {section}.{subsection} {normalize_heading_title(title)}\n\n"
        f"<!-- rosetta-item: section-{section}.{subsection} -->\n\n{structured}"
    )


def render_fragment(source_path: Path, source: str) -> str:
    """Render unnumbered chapter/exercise prose through the same safe pipeline."""

    markdown = normalize_markdown_math(latex_to_gfm(source))
    markdown = resolve_markdown_references(
        markdown, build_reference_index(source_path.parent)
    )
    return clean_markdown(normalize_html_tables(markdown))
