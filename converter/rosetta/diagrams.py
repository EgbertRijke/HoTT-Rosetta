"""Readable, reviewable ASCII drafts for tikz-cd diagrams."""

import hashlib
import re
from dataclasses import dataclass
from typing import Callable, List, Optional, Tuple


TIKZCD_RE = re.compile(
    r"\\begin\{tikzcd\}(?:\[[^\]]*\])?(.*?)\\end\{tikzcd\}", re.DOTALL
)
ARROW_START_RE = re.compile(r"\\arrow\[")
QUOTED_RE = re.compile(r'"([^\"]*)"')
SPACING_OPTION_RE = re.compile(
    r"^\s*\[\s*[+-]?(?:\d+(?:\.\d*)?|\.\d+)\s*"
    r"(?:em|ex|pt|pc|in|bp|cm|mm|dd|cc|sp)\s*\]"
)


@dataclass(frozen=True)
class Arrow:
    source: Tuple[int, int]
    target: Optional[Tuple[int, int]]
    direction: str
    label: str


@dataclass(frozen=True)
class DiagramDraft:
    stable_id: str
    description: str
    art: str
    arrows: List[Arrow]


def diagram_stable_id(source: str) -> str:
    """Hash diagram content independent of indentation and layout options."""

    match = TIKZCD_RE.search(source)
    if not match:
        raise ValueError("Expected one tikzcd environment")
    canonical = re.sub(r"\s+", " ", match.group(1)).strip()
    return hashlib.sha256(canonical.encode()).hexdigest()[:12]


def _split_top_level(value: str, separator: str) -> List[str]:
    parts: List[str] = []
    start = 0
    depth = 0
    position = 0
    while position < len(value):
        character = value[position]
        if character == "{":
            depth += 1
        elif character == "}":
            depth = max(0, depth - 1)
        if depth == 0 and value.startswith(separator, position):
            parts.append(value[start:position])
            position += len(separator)
            start = position
            continue
        position += 1
    parts.append(value[start:])
    return parts


def _arrow_end(cell: str, start: int) -> int:
    depth = 0
    for position in range(start + len(r"\arrow["), len(cell)):
        if cell[position] == "[":
            depth += 1
        elif cell[position] == "]":
            if depth == 0:
                return position + 1
            depth -= 1
    return len(cell)


def _direction(options: str) -> str:
    first = options.split(",", 1)[0].strip()
    if re.fullmatch(r"[lrud]+", first):
        return first
    return "custom"


def _target(row: int, column: int, direction: str) -> Optional[Tuple[int, int]]:
    if direction == "custom":
        return None
    return (
        row + direction.count("d") - direction.count("u"),
        column + direction.count("r") - direction.count("l"),
    )


def _parse_cell(cell: str, row: int, column: int) -> Tuple[str, List[Arrow]]:
    arrows: List[Arrow] = []
    output: List[str] = []
    position = 0
    for match in ARROW_START_RE.finditer(cell):
        if match.start() < position:
            continue
        output.append(cell[position : match.start()])
        end = _arrow_end(cell, match.start())
        options = cell[match.end() : end - 1]
        direction = _direction(options)
        labels = [label for label in QUOTED_RE.findall(options) if label]
        label = next(
            (item for item in labels if "name=" not in item and item not in {""}),
            "",
        )
        arrows.append(
            Arrow((row, column), _target(row, column, direction), direction, label)
        )
        position = end
    output.append(cell[position:])
    node = "".join(output).strip()
    if node.startswith(r"\phantom"):
        node = ""
    node = re.sub(r"^\{(.*)\}([.,]?)$", r"\1\2", node, flags=re.DOTALL)
    node = node.rstrip(".,")
    return node, arrows


def _description(rows: int, columns: int, occupied: int) -> str:
    if rows == 1:
        return "linear diagram"
    if columns == 1:
        return "vertical diagram"
    if rows == 2 and columns == 2 and occupied == 4:
        return "square-shaped diagram"
    if rows == 2 and columns == 3 and occupied >= 5:
        return "diagram of two squares pasted horizontally"
    if rows == 3 and columns == 2 and occupied >= 5:
        return "diagram of two squares pasted vertically"
    if rows == 2 and columns in {2, 3} and occupied == 3:
        return "triangle-shaped diagram"
    return f"{rows}-by-{columns} diagram"


def _matrix_art(nodes: List[List[str]], arrows: List[Arrow]) -> str:
    columns = max(len(row) for row in nodes)
    widths = [
        max(3, max((len(row[column]) for row in nodes if column < len(row)), default=0))
        for column in range(columns)
    ]
    lines = []
    for row_number, row in enumerate(nodes):
        line = ""
        for column, width in enumerate(widths):
            value = row[column] if column < len(row) else ""
            line += (f"[{value}]" if value else "").center(width + 2)
            if column + 1 < columns:
                forward = any(
                    arrow.source == (row_number, column)
                    and arrow.target == (row_number, column + 1)
                    for arrow in arrows
                )
                backward = any(
                    arrow.source == (row_number, column + 1)
                    and arrow.target == (row_number, column)
                    for arrow in arrows
                )
                line += "<--->" if forward and backward else (
                    "---->" if forward else ("<----" if backward else "     ")
                )
        lines.append(line.rstrip())
        if row_number + 1 < len(nodes):
            vertical = []
            for column, width in enumerate(widths):
                connected = any(
                    {arrow.source, arrow.target}
                    == {(row_number, column), (row_number + 1, column)}
                    for arrow in arrows
                    if arrow.target is not None
                )
                vertical.append(("|" if connected else "").center(width + 2))
            lines.append("     ".join(vertical).rstrip())
    return "\n".join(lines)


def render_tikzcd(source: str, normalize: Callable[[str], str]) -> DiagramDraft:
    """Parse one tikz-cd environment into a readable review draft."""

    match = TIKZCD_RE.search(source)
    if not match:
        raise ValueError("Expected one tikzcd environment")
    raw_rows = _split_top_level(match.group(1).strip(), r"\\")
    nodes: List[List[str]] = []
    arrows: List[Arrow] = []
    for row_number, raw_row in enumerate(raw_rows):
        if row_number:
            raw_row = SPACING_OPTION_RE.sub("", raw_row, count=1)
        row: List[str] = []
        for column, raw_cell in enumerate(_split_top_level(raw_row, "&")):
            if column:
                raw_cell = SPACING_OPTION_RE.sub("", raw_cell, count=1)
            node, cell_arrows = _parse_cell(raw_cell, row_number, column)
            row.append(normalize(node) if node else "")
            arrows.extend(cell_arrows)
        nodes.append(row)
    columns = max(len(row) for row in nodes)
    occupied = sum(bool(node) for row in nodes for node in row)
    arrow_lines = []
    for arrow in arrows:
        source_name = nodes[arrow.source[0]][arrow.source[1]] or str(arrow.source)
        if arrow.target is not None:
            target_row, target_column = arrow.target
            if (
                0 <= target_row < len(nodes)
                and 0 <= target_column < len(nodes[target_row])
            ):
                target_name = nodes[target_row][target_column] or str(arrow.target)
            else:
                target_name = str(arrow.target)
        else:
            target_name = "custom target"
        label = normalize(arrow.label) if arrow.label else "unlabeled"
        arrow_lines.append(f"- {source_name} --{label}--> {target_name}")
    art = _matrix_art(nodes, arrows)
    if arrow_lines:
        art += "\n\nArrows:\n" + "\n".join(arrow_lines)
    stable_id = diagram_stable_id(source)
    return DiagramDraft(
        stable_id,
        _description(len(nodes), columns, occupied),
        art,
        arrows,
    )
