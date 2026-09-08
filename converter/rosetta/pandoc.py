"""A deliberately small Pandoc prototype boundary."""

import shutil
import subprocess
import re
import uuid
from typing import List

from .proof_trees import render_proof_tree_markdown


class PandocUnavailable(RuntimeError):
    pass


def _split_align_intertext(source: str) -> str:
    """Move align intertext into prose without dropping either side."""

    align_re = re.compile(
        r"\\begin\{(align\*?)\}(.*?)\\end\{\1\}", re.DOTALL
    )

    def split_block(match):
        environment, body = match.group(1), match.group(2)
        pieces = []
        start = 0
        while True:
            marker = body.find(r"\intertext", start)
            if marker < 0:
                break
            argument_start = marker + len(r"\intertext")
            if argument_start >= len(body) or body[argument_start] != "{":
                break
            depth = 0
            argument_end = None
            for position in range(argument_start, len(body)):
                if body[position] == "{":
                    depth += 1
                elif body[position] == "}":
                    depth -= 1
                    if depth == 0:
                        argument_end = position
                        break
            if argument_end is None:
                break
            pieces.append((body[start:marker], body[argument_start + 1 : argument_end]))
            start = argument_end + 1
        if not pieces:
            return match.group(0)
        output = []
        for math, prose in pieces:
            if math.strip():
                output.append(
                    f"\\begin{{{environment}}}{math}\\end{{{environment}}}"
                )
            output.append(prose)
        tail = body[start:]
        if tail.strip():
            output.append(
                f"\\begin{{{environment}}}{tail}\\end{{{environment}}}"
            )
        return "\n\n".join(output)

    return align_re.sub(split_block, source)


def prepare_latex(source: str) -> str:
    """Rewrite book macros whose contents Pandoc would otherwise discard.

    This list stays intentionally explicit. New macros require a fixture and a
    documented rule instead of a broad substitution that might change math.
    """

    source = _split_align_intertext(source)
    # GFM has no citation extension, and its writer drops LaTeX citation keys.
    # Keep the book's simple citation groups as visible, explicitly unresolved
    # references. Do not invent bibliography numbering or execute BibTeX.
    source = re.sub(
        r"\\cite\s*\{([A-Za-z0-9_.:+/-]+(?:\s*,\s*[A-Za-z0-9_.:+/-]+)*)\}",
        lambda match: "[citation: " + ", ".join(
            r"\texttt{" + key.strip().replace("_", r"\_") + "}"
            for key in match.group(1).split(",")
        ) + "]",
        source,
    )
    # Pandoc drops this text symbol in prose, although it keeps it in math.
    # Use the same literal asterisk for equation tags and their text references.
    source = re.sub(r"\\textasteriskcentered(?![A-Za-z@])(?:\{\})?", "*", source)
    # ``samepage`` controls page breaking only; it has no Markdown meaning.
    source = re.sub(r"\\(?:begin|end)\{samepage\}%?", "", source)
    source = re.sub(r"\\define\{([^{}]*)\}", r"\\textbf{\1}", source)
    source = re.sub(
        r"\\texorpdfstring\{(\$[^$]*\$)\}\{[^{}]+\}", r"\1", source
    )
    return source


def latex_to_gfm(source: str) -> str:
    """Convert a LaTeX fragment to GitHub-flavored Markdown.

    Unknown book-specific commands remain visible in the output at this stage;
    later filters will handle them explicitly rather than silently dropping them.
    """

    executable = shutil.which("pandoc")
    if executable is None:
        raise PandocUnavailable(
            "Pandoc is required for conversion but was not found. "
            "Install it from https://pandoc.org/installing.html."
        )
    proof_trees = []

    def proof_placeholder(match):
        proof_trees.append(render_proof_tree_markdown(match.group(1)))
        return f"\n\nROSETTAPROOFTREE{len(proof_trees) - 1}TOKEN\n\n"

    source = re.sub(
        r"\\begin\{prooftree\}(.*?)\\end\{prooftree\}",
        proof_placeholder,
        source,
        flags=re.DOTALL,
    )
    process = subprocess.run(
        [executable, "--from=latex", "--to=gfm", "--wrap=none"],
        input=prepare_latex(source),
        text=True,
        capture_output=True,
        check=False,
    )
    if process.returncode:
        raise RuntimeError(process.stderr.strip() or "Pandoc conversion failed")
    output = process.stdout
    for index, rendered in enumerate(proof_trees):
        output = output.replace(f"ROSETTAPROOFTREE{index}TOKEN", rendered)
    return output


def markdown_to_safe_html(source: str) -> str:
    """Render Markdown for local preview without executing embedded HTML."""

    executable = shutil.which("pandoc")
    if executable is None:
        raise PandocUnavailable(
            "Pandoc is required for Markdown preview but was not found. "
            "Install it from https://pandoc.org/installing.html."
        )
    process = subprocess.run(
        [executable, "--from=markdown-raw_html", "--to=html", "--wrap=none"],
        input=source,
        text=True,
        capture_output=True,
        check=False,
    )
    if process.returncode:
        raise RuntimeError(process.stderr.strip() or "Markdown preview failed")
    return process.stdout


def markdown_fragments_to_safe_html(sources: List[str]) -> List[str]:
    """Render several independent previews with one Pandoc process."""

    if not sources:
        return []
    token = "ROSETTAPREVIEWBOUNDARY" + uuid.uuid4().hex
    combined = "".join(
        f"\n\n{token}{index}\n\n{source}\n"
        for index, source in enumerate(sources)
    )
    rendered = markdown_to_safe_html(combined)
    fragments = []
    for index in range(len(sources)):
        marker = f"<p>{token}{index}</p>"
        start = rendered.find(marker)
        if start < 0:
            raise RuntimeError("Markdown preview boundary was lost")
        start += len(marker)
        if index + 1 < len(sources):
            next_marker = f"<p>{token}{index + 1}</p>"
            end = rendered.find(next_marker, start)
            if end < 0:
                raise RuntimeError("Markdown preview boundary was lost")
        else:
            end = len(rendered)
        fragments.append(rendered[start:end].strip())
    return fragments
