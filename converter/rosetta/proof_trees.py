"""Faithful plain-text rendering for the subset of bussproofs used by the book."""

import hashlib
import re
from dataclasses import dataclass
from typing import List


COMMAND_RE = re.compile(
    r"\\(AxiomC|UnaryInfC|BinaryInfC|TrinaryInfC|RightLabel|noLine)"
    r"(?![A-Za-z@])",
)


@dataclass(frozen=True)
class ProofTreeDraft:
    stable_id: str
    art: str


@dataclass
class _Tree:
    lines: List[str]

    @property
    def width(self) -> int:
        return max((len(line) for line in self.lines), default=0)


def proof_tree_stable_id(source: str) -> str:
    canonical = re.sub(r"\s+", " ", source).strip()
    return hashlib.sha256(canonical.encode()).hexdigest()[:12]


def _text(value: str) -> str:
    # Import lazily to avoid coupling the notation table to the renderer.
    from .math_text import normalize_math

    # The book sometimes puts sentence punctuation outside the math delimiters.
    value = value.strip().removesuffix(".").rstrip()
    if value.startswith("$") and value.endswith("$"):
        value = value[1:-1]
    return normalize_math(value.rstrip(".").strip())


def _commands(body: str):
    """Read full braced arguments; a depth-limited regex can lose conclusions."""

    cursor = 0
    while match := COMMAND_RE.search(body, cursor):
        command = match.group(1)
        cursor = match.end()
        if command == "noLine":
            yield command, ""
            continue
        while cursor < len(body) and body[cursor].isspace():
            cursor += 1
        if cursor >= len(body) or body[cursor] != "{":
            raise ValueError(f"{command} needs a braced argument")
        start = cursor + 1
        depth = 1
        cursor = start
        while cursor < len(body) and depth:
            if body[cursor] == "\\":
                # Escaped braces are literal symbols, not argument delimiters.
                cursor += 2
                continue
            if body[cursor] == "{":
                depth += 1
            elif body[cursor] == "}":
                depth -= 1
            cursor += 1
        if depth:
            raise ValueError(f"Unclosed {command} argument")
        yield command, body[start : cursor - 1]


def _combine(premises: List[_Tree], conclusion: str, label: str, line: bool) -> _Tree:
    gap = "   "
    height = max((len(tree.lines) for tree in premises), default=0)
    premise_lines = []
    for row in range(height):
        pieces = []
        for tree in premises:
            offset = height - len(tree.lines)
            value = tree.lines[row - offset] if row >= offset else ""
            pieces.append(value.center(tree.width))
        premise_lines.append(gap.join(pieces).rstrip())
    premise_width = max((len(value) for value in premise_lines), default=0)
    width = max(premise_width, len(conclusion), 3)
    rule = ("─" * width if line else " " * width) + (f" {label}" if label else "")
    return _Tree(
        [value.center(width).rstrip() for value in premise_lines]
        + [rule.rstrip(), conclusion.center(width).rstrip()]
    )


def render_proof_tree(body: str) -> ProofTreeDraft:
    """Render axioms and unary/binary/trinary inference rules without data loss."""

    center = re.search(r"\\def\\fCenter\{([^{}]*)\}", body)
    if center:
        body = body.replace(r"\fCenter", center.group(1))
    body = re.sub(
        r"\\(Axiom|UnaryInf|BinaryInf|TrinaryInf)\$(.*?)\$",
        lambda match: "\\" + match.group(1) + "C{" + match.group(2) + "}",
        body,
        flags=re.DOTALL,
    )
    stack: List[_Tree] = []
    label = ""
    draw_line = True
    arities = {"UnaryInfC": 1, "BinaryInfC": 2, "TrinaryInfC": 3}
    for command, argument in _commands(body):
        if command == "AxiomC":
            stack.append(_Tree([_text(argument)]))
        elif command == "RightLabel":
            label = _text(argument)
        elif command == "noLine":
            draw_line = False
        else:
            arity = arities[command]
            if len(stack) < arity:
                raise ValueError(f"{command} needs {arity} premises")
            premises = stack[-arity:]
            del stack[-arity:]
            stack.append(_combine(premises, _text(argument), label, draw_line))
            label = ""
            draw_line = True
    if len(stack) != 1:
        raise ValueError("Proof tree did not reduce to one conclusion")
    return ProofTreeDraft(proof_tree_stable_id(body), "\n".join(stack[0].lines))


def render_proof_tree_markdown(body: str) -> str:
    draft = render_proof_tree(body)
    return (
        f"<!-- rosetta-proof-tree: {draft.stable_id}; review: pending -->\n\n"
        "*Proof tree (automatic faithful draft).*\n\n"
        f"```text\n{draft.art}\n```"
    )
