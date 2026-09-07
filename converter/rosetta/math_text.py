"""Explicit LaTeX-to-Rosetta notation used in Markdown mathematics.

This is intentionally a readable table plus a few small structural rules. It
is not a general TeX evaluator. Each addition should be supported by an
existing translation fixture.
"""

import re
from pathlib import Path

from .diagrams import TIKZCD_RE, render_tikzcd


# Longer command names must be replaced before their prefixes.
SIMPLE_COMMANDS = {
    r"\ischoiceofrepresentatives": "is-choice-of-reps",
    r"\hasassociativemul": "has-associative-mul",
    r"\universalcovercircle": "E_(S^1)",
    r"\loophtpyidcircle": "β",
    r"\basehtpyidcircle": "α",
    r"\collectBinTree": "bin-tree",
    r"\isconstantW": "is-constant_W",
    r"\loopspacesym": "Ω",
    r"\loopmulcircle": "loop-mul_(S^1)",
    r"\basemulcircle": "base-mul_(S^1)",
    r"\segmenthelix": "segment-helix",
    r"\planarBinTree": "T_2",
    r"\reflEqW": "refl-Eq_W",
    r"\ispartition": "is-partition",
    r"\apbinary": "ap-binary",
    r"\isoeq": "iso-eq",
    r"\isunital": "is-unital",
    r"\semigroup": "Semigroup",
    r"\partition": "Partition",
    r"\htpyidcircle": "H",
    r"\mulcircle": "mul_(S^1)",
    r"\symbolW": "symbol",
    r"\prearity": "symbol",
    r"\indbool": "ind-bool",
    r"\indW": "ind_W",
    r"\BinTree": "Bin-Tree",
    r"\component": "component",
    r"\cohunit": "coh-unit",
    r"\isgroup": "is-group",
    r"\isiso": "is-iso",
    r"\isconn": "is-conn",
    r"\monoid": "Monoid",
    r"\semigroup": "Semigroup",
    r"\group": "Group",
    r"\Group": "Group",
    r"\Grp": "Group",
    r"\collect": "tree",
    r"\arity": "arity",
    r"\EqW": "Eq_W",
    r"\node": "node",
    r"\dgen": "dgen",
    r"\gen": "gen",
    r"\base": "base",
    r"\lloop": "loop",
    r"\hom": "hom",
    r"\eqvsym": "≃",
    r"\inneg": "in-neg",
    r"\inpos": "in-pos",
    r"\Omega": "Ω",
    r"\omega": "ω",
    r"\W": "W",
    r"\Q": "ℚ",
    r"\addsuccN": "add-S",
    r"\addzeroN": "add-0",
    r"\succN": "succ-ℕ",
    r"\addN": "add-ℕ",
    r"\indN": "ind-ℕ",
    r"\leftsuccessorlawaddN": "left-successor-law-add-ℕ",
    r"\rightsuccessorlawaddN": "right-successor-law-add-ℕ",
    r"\leftunitlawaddN": "left-unit-law-add-ℕ",
    r"\rightunitlawaddN": "right-unit-law-add-ℕ",
    r"\associativeaddN": "associative-add-ℕ",
    r"\commutativeaddN": "commutative-add-ℕ",
    r"\homslice": "hom-slice",
    r"\pathind": "path-ind",
    r"\succFin": "succ-Fin",
    r"\natFin": "nat-Fin",
    r"\distN": "dist-ℕ",
    r"\succZ": "succ-ℤ",
    r"\apfunc": "ap",
    r"\iscontr": "is-contr",
    r"\isemb": "is-emb",
    r"\isprime": "is-prime",
    r"\strongindN": "strong-ind-ℕ",
    r"\skipzeroFin": "skip-zero-Fin",
    r"\hasinverse": "has-inverse",
    r"\rightunit": "right-unit",
    r"\leftunit": "left-unit",
    r"\rightinv": "right-inv",
    r"\leftinv": "left-inv",
    r"\istrunc": "is-trunc",
    r"\isequiv": "is-equiv",
    r"\isempty": "is-empty",
    r"\Eqfib": "Eq-fib",
    r"\zeroFin": "zero-Fin",
    r"\predFin": "pred-Fin",
    r"\zeroZ": "0-ℤ",
    r"\cnt": "count",
    r"\idtypevar": "Id",
    r"\classicalFin": "classical-Fin",
    r"\ismultipleofgcd": "M",
    r"\islowerbound": "is-lower-bound",
    r"\iscohinvertible": "is-coh-invertible",
    r"\decidableProp": "decidable-Prop",
    r"\eqpairpairr": "eq-pair",
    r"\concathtpy": "concat-htpy",
    r"\assochtpy": "assoc-htpy",
    r"\Eqcoprodeq": "Eq-coproduct-eq",
    r"\Eqcoprod": "Eq-coproduct",
    r"\EqSigma": "Eq-Σ",
    r"\EqFin": "Eq-Fin",
    r"\eqequiv": "eq-equiv",
    r"\eqhtpy": "eq-htpy",
    r"\iffeq": "iff-eq",
    r"\eqpair": "eq-pair",
    r"\evpair": "ev-pair",
    r"\evrefl": "ev-refl",
    r"\evpt": "ev-pt",
    r"\apconcat": "ap-concat",
    r"\apcomp": "ap-comp",
    r"\aprefl": "ap-refl",
    r"\apinv": "ap-inv",
    r"\apid": "ap-id",
    r"\addFin": "add-Fin",
    r"\isfinite": "is-finite",
    r"\collatz": "collatz",
    r"\isdec": "is-decidable",
    r"\gcd": "gcd",
    r"\btrue": "true",
    r"\bfalse": "false",
    r"\concat": "concat",
    r"\assoc": "assoc",
    r"\choice": "choice",
    r"\booleanreflection": "boolean-reflection",
    r"\booleanization": "booleanization",
    r"\isdecidableisprime": "is-decidable-is-prime",
    r"\isprimethirtyseven": "is-prime-thirty-seven",
    r"\reflexiveEqSigma": "reflexive-Eq-Σ",
    r"\indcoprod": "ind-coproduct",
    r"\indSigma": "ind-Σ",
    r"\indunit": "ind-unit",
    r"\indsing": "ind-sing",
    r"\singind": "ind-sing",
    r"\singcomp": "comp-sing",
    r"\equiveq": "equiv-eq",
    r"\invfunc": "inv",
    r"\invhtpy": "inv-htpy",
    r"\negnegbool": "neg-neg-bool",
    r"\paireq": "pair-eq",
    r"\negtwoT": "-2",
    r"\reflhtpy": "refl-htpy",
    r"\reflleqN": "refl-≤-ℕ",
    r"\htpyeq": "htpy-eq",
    r"\top": "⊤",
    r"\Ty": "Ty",
    r"\sqcupW": "⊔ 𝕎",
    r"\sqcup": "⊔",
    r"\succT": "succT",
    r"\T": "𝕋",
    r"\im": "im",
    r"\emb": "↪",
    r"\demb": "↪ᵈ",
    r"\Aut": "Aut",
    r"\B": "B",
    r"\bot": "empty",
    r"\Leftrightarrow": "↔",
    r"\reflEqN": "refl-Eq-ℕ",
    r"\isdecidable": "is-decidable",
    r"\hookrightarrow": "↪",
    r"\exfalso": "ex-falso",
    r"\idfunc": "id",
    r"\negFin": "neg-Fin",
    r"\negbool": "neg-bool",
    r"\EqN": "Eq-ℕ",
    r"\zeroN": "0",
    r"\oneN": "1",
    r"\emptyt": "empty",
    r"\isprop": "is-prop",
    r"\isequivalenceclass": "is-equivalence-class",
    r"\islocallysmall": "is-locally-small",
    r"\issmall": "is-small",
    r"\eqrel": "Eq-Rel",
    r"\prop": "Prop",
    r"\const": "const",
    r"\simeq": "≃",
    r"\equiv": "≡",
    r"\htpy": "~",
    r"\circ": "∘",
    r"\refl": "refl",
    r"\leq": "≤",
    r"\geq": "≥",
    r"\neq": "≠",
    r"\neg": "¬",
    r"\ttt": "⋆",
    r"\blank": "_",
    r"\bool": "bool",
    r"\varphi": "φ",
    r"\square": "□",
    r"\textasteriskcentered": "*",
    r"\twoheadrightarrow": "↠",
    r"\Downarrow": "⇓",
    r"\cong": "≅",
    r"\Rightarrow": "⇒",
    r"\varepsilon": "ε",
    r"\notin": "∉",
    r"\nmid": "∤",
    r"\nless": "≮",
    r"\land": "∧",
    r"\vee": "∨",
    r"\sim": "~",
    r"\Set": "Set",
    r"\psi": "ψ",
    r"\pt": "pt",
    r"\tr": "tr",
    r"\left": "",
    r"\right": "",
    r"\star": "⋆",
    r"\ast": "⋆",
    r"\mod": "mod",
    r"\BS": "BS",
    r"\prd": "Π",
    r"\sm": "Σ",
    r"\big": "",
    r"\Big": "",
    r"\Fin": "Fin",
    r"\F": "𝔽",
    r"\UU": "𝒰",
    r"\VV": "𝒱",
    r"\rho": "ρ",
    r"\sigma": "σ",
    r"\tau": "τ",
    r"\eta": "η",
    r"\mu": "μ",
    r"\pi": "π",
    r"\pm": "±",
    r"\usc": "-",
    r"\in": "∈",
    r"\exists": "∃",
    r"\forall": "∀",
    r"\inl": "inl",
    r"\inr": "inr",
    r"\pair": "pair",
    r"\proj": "pr",
    r"\unit": "unit",
    r"\mid": "|",
    r"\cdot": "·",
    r"\lor": "∨",
    r"\alpha": "α",
    r"\beta": "β",
    r"\gamma": "γ",
    r"\jdeq": "≐",
    r"\defeq": "≔",
    r"\coloneqq": "≔",
    r"\vdash": "⊢",
    r"\mapsto": "↦",
    r"\longmapsto": "⟼",
    r"\leftrightarrow": "↔",
    r"\rightarrow": "→",
    r"\to": "→",
    r"\times": "×",
    r"\cdots": "⋯",
    r"\ldots": "…",
    r"\lambda": "λ",
    r"\Gamma": "Γ",
    r"\Sigma": "Σ",
    r"\Pi": "Π",
    r"\N": "ℕ",
    r"\Z": "ℤ",
    r"\ev": "ev",
}


def _word_like_book_macros() -> dict:
    """Read simple mathsf names from hott.tex without evaluating TeX."""

    source = Path(__file__).resolve().parents[2] / "book" / "hott.tex"
    if not source.is_file():
        return {}
    commands = {}
    definition = re.compile(
        r"\\newcommand\{(\\[A-Za-z@]+)\}(?:\[([^]]+)\])?"
        r"\{[^\n]*?\\mathsf\{((?:[A-Za-z]+|\\usc(?:\{\})?)+)\}"
    )
    for command, argument_count, body in definition.findall(source.read_text()):
        if argument_count:
            continue
        name = re.sub(r"\\usc(?:\{\})?", "-", body)
        if re.fullmatch(r"[A-Za-z]+(?:-[A-Za-z]+)*", name):
            commands[command] = name
    return commands


for _command, _name in _word_like_book_macros().items():
    SIMPLE_COMMANDS.setdefault(_command, _name)


def _replace_simple_commands(value: str) -> str:
    structural_commands = {r"\refl", r"\idtypevar", r"\prd", r"\sm"}
    command_pattern = "|".join(
        re.escape(command)
        for command in sorted(SIMPLE_COMMANDS, key=len, reverse=True)
        if command not in structural_commands
    )
    return re.sub(
        rf"(?:{command_pattern})(?![A-Za-z@])",
        lambda match: SIMPLE_COMMANDS[match.group(0)],
        value,
    )


def _braced_argument(value: str, start: int):
    if start >= len(value) or value[start] != "{":
        return None
    depth = 0
    for position in range(start, len(value)):
        if value[position] == "{":
            depth += 1
        elif value[position] == "}":
            depth -= 1
            if depth == 0:
                return value[start + 1 : position], position + 1
    return None


def _last_command_position(value: str, macro: str) -> int:
    matches = list(re.finditer(re.escape(macro) + r"(?![A-Za-z@])", value))
    return matches[-1].start() if matches else -1


def _replace_binary_macro(value: str, macro: str, separator: str) -> str:
    """Expand a two-argument macro while respecting nested braces."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        first = _braced_argument(value, position + len(macro))
        if first is None:
            return value[:position] + separator.strip() + value[position + len(macro) :]
        second = _braced_argument(value, first[1])
        if second is None:
            return value[:position] + separator.strip() + value[position + len(macro) :]
        replacement = first[0] + separator + second[0]
        value = value[:position] + replacement + value[second[1] :]


def _replace_binary_function(value: str, macro: str, name: str) -> str:
    """Render a two-argument macro as a readable function call."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        first = _braced_argument(value, position + len(macro))
        if first is None:
            return value[:position] + name + value[position + len(macro) :]
        second = _braced_argument(value, first[1])
        if second is None:
            return value[:position] + name + value[position + len(macro) :]
        replacement = f"{name}({first[0]}, {second[0]})"
        value = value[:position] + replacement + value[second[1] :]


def _replace_subscript_function(value: str, macro: str, name: str) -> str:
    """Render a two-argument operation in the fixture's ``name_f(p)`` style."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        first = _braced_argument(value, position + len(macro))
        if first is None:
            return value[:position] + name + value[position + len(macro) :]
        second = _braced_argument(value, first[1])
        if second is None:
            return value[:position] + name + value[position + len(macro) :]
        replacement = f"{name}_{{{first[0]}}}({second[0]})"
        value = value[:position] + replacement + value[second[1] :]


def _replace_truncation(value: str) -> str:
    """Expand ``trunc`` according to its two-argument book definition."""

    macro = r"\trunc"
    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        level = _braced_argument(value, position + len(macro))
        if level is None:
            return value
        body = _braced_argument(value, level[1])
        if body is None:
            return value
        replacement = f"‖{body[0]}‖_{level[0]}"
        value = value[:position] + replacement + value[body[1] :]


def _replace_stirling(value: str) -> str:
    """Render the book's two-row braced Stirling-number notation."""

    macro = r"\stirling"
    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        upper = _braced_argument(value, position + len(macro))
        if upper is None:
            return value
        lower = _braced_argument(value, upper[1])
        if lower is None:
            return value
        replacement = f"Stirling({upper[0]}, {lower[0]})"
        value = value[:position] + replacement + value[lower[1] :]


def _replace_unary_wrapper(
    value: str, macro: str, prefix: str, suffix: str = ""
) -> str:
    """Render a one-argument macro while respecting nested braces."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        argument = _braced_argument(value, position + len(macro))
        if argument is None:
            return value[:position] + prefix + value[position + len(macro) :]
        replacement = prefix + argument[0] + suffix
        value = value[:position] + replacement + value[argument[1] :]


def _replace_optional_unary_wrapper(
    value: str, macro: str, name: str, default_exponent: str = ""
) -> str:
    """Render an optional exponent followed by one braced argument."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        cursor = position + len(macro)
        exponent = default_exponent
        if cursor < len(value) and value[cursor] == "[":
            end = value.find("]", cursor + 1)
            if end < 0:
                return value
            exponent = value[cursor + 1 : end]
            cursor = end + 1
        argument = _braced_argument(value, cursor)
        if argument is None:
            return value[:position] + name + value[position + len(macro) :]
        superscript = f"^{exponent}" if exponent else ""
        replacement = f"{name}{superscript}({argument[0]})"
        value = value[:position] + replacement + value[argument[1] :]


def _replace_optional_symbol(
    value: str, macro: str, name: str, default_subscript: str
) -> str:
    """Render a command whose only argument is optional."""

    while True:
        position = _last_command_position(value, macro)
        if position < 0:
            return value
        cursor = position + len(macro)
        subscript = default_subscript
        end = cursor
        if cursor < len(value) and value[cursor] == "[":
            closing = value.find("]", cursor + 1)
            if closing < 0:
                return value
            subscript = value[cursor + 1 : closing]
            end = closing + 1
        replacement = f"{name}_{subscript}"
        value = value[:position] + replacement + value[end:]


def normalize_math(source: str) -> str:
    """Render confirmed project notation as readable Unicode/plain text."""

    value = _replace_simple_commands(source.strip().replace("~", " "))
    value = re.sub(r"\\begin\{(?:equation|align)\*?\}", "", value)
    value = re.sub(r"\\end\{(?:equation|align)\*?\}", "", value)
    value = re.sub(r"\\text\{([^{}]*)\}", r"\1", value)
    value = re.sub(r"\\mathrm\{([^{}]*)\}", r"\1", value)
    value = _replace_unary_wrapper(value, r"\mathsf", "")
    value = re.sub(r"\\mathcal\{([^{}]*)\}", r"\1", value)
    value = re.sub(
        r"\\mathbb\{([CNQRZ])\}",
        lambda match: {
            "C": "ℂ",
            "N": "ℕ",
            "Q": "ℚ",
            "R": "ℝ",
            "Z": "ℤ",
        }.get(match.group(1), match.group(0)),
        value,
    )
    value = re.sub(r"\\tilde\{([^{}]+)\}", r"\1̃", value)
    value = re.sub(r"\\check\{([^{}]+)\}", r"\1̌", value)
    value = re.sub(r"\\bar\{([^{}]+)\}", r"\1̄", value)
    value = re.sub(r"\\label\{[^{}]*\}", "", value)
    value = re.sub(r"\\frac\{([^{}]+)\}\{([^{}]+)\}", r"\1/\2", value)
    value = _replace_binary_macro(value, r"\ct", " ∙ ")
    value = _replace_binary_macro(value, r"\eqv", " ≃ ")
    value = _replace_truncation(value)
    value = _replace_stirling(value)
    value = _replace_binary_function(value, r"\fib", "fib")
    value = _replace_binary_function(value, r"\binom", "binom")
    value = _replace_binary_function(value, r"\binomtype", "binom")
    value = _replace_subscript_function(value, r"\apd", "apd")
    value = _replace_subscript_function(value, r"\ap", "ap")
    value = _replace_unary_wrapper(value, r"\pairr", "(", ")")
    value = _replace_unary_wrapper(value, r"\tot", "tot(", ")")
    value = _replace_unary_wrapper(value, r"\fibf", "fib_", "")
    value = _replace_unary_wrapper(value, r"\brck", "‖", "‖")
    value = _replace_unary_wrapper(value, r"\Brck", "‖", "‖")
    value = _replace_unary_wrapper(value, r"\sphere", "S^")
    value = _replace_unary_wrapper(value, r"\phantom", "")
    value = _replace_unary_wrapper(value, r"\ind", "ind-")
    value = _replace_unary_wrapper(value, r"\comphtpy", "comp_", "")
    value = _replace_unary_wrapper(value, r"\multiset", "M_", "")
    value = _replace_unary_wrapper(value, r"\issmallmultiset", "is-small_M_", "")
    value = _replace_unary_wrapper(value, r"\tag", "(", ")")
    value = _replace_optional_unary_wrapper(value, r"\loopspace", "Ω")
    value = _replace_optional_symbol(value, r"\yggdrasil", "Y", "𝒰")
    value = _replace_unary_wrapper(value, r"\idtypevar", "Id_")
    value = re.sub(
        r"\\id(?:\[([^\]]+)\])?\{([^{}]+)\}\{([^{}]+)\}",
        lambda match: (
            f"{match.group(2)} =_{match.group(1)} {match.group(3)}"
            if match.group(1)
            else f"{match.group(2)} = {match.group(3)}"
        ),
        value,
    )
    value = _replace_binary_macro(value, r"\id", " = ")
    value = _replace_unary_wrapper(value, r"\prd", "Π(", ") ")
    value = _replace_unary_wrapper(value, r"\sm", "Σ(", ") ")
    value = re.sub(r"\\lam\{([^{}]+)\}", r"λ \1. ", value)
    value = re.sub(
        r"\\dbinomtype(?:\[([^\]]+)\])?\{([^{}]+)\}\{([^{}]+)\}",
        lambda match: (
            f"binom_{match.group(1)}({match.group(2)}, {match.group(3)})"
            if match.group(1)
            else f"binom({match.group(2)}, {match.group(3)})"
        ),
        value,
    )
    value = re.sub(r"\\refl\{[^{}]+\}", "refl", value)
    value = re.sub(r"\\refl(?![A-Za-z@])", "refl", value)
    value = re.sub(r"\\ct(?![A-Za-z@])", "∙", value)
    value = re.sub(r"\\tr(?=_[A-Za-z])", "tr", value)
    value = value.replace(r"\qedhere", "")
    value = value.replace(r"\,", " ").replace(r"\;", " ")
    value = value.replace(r"\{", "{").replace(r"\}", "}")
    value = value.replace("{}", "")
    value = value.replace(r"\qquad", "    ").replace(r"\quad", "  ")
    value = re.sub(r"[ \t]+", " ", value)
    value = re.sub(r" *& *", " ", value)
    value = re.sub(r"\\\\\*?\s*", "\n", value)
    value = "\n".join(line.strip() for line in value.splitlines())
    return value.strip()


def normalize_heading_title(title: str) -> str:
    """Use the readable branch of LaTeX PDF-string title alternatives."""

    value = re.sub(
        r"\\texorpdfstring\{\$[^$]*\$\}\{([^{}]+)\}", r"\1", title
    )
    value = re.sub(
        r"\\texorpdfstring\{\$[^$]*\$[^{}]*\}\{([^{}]+)\}", r"\1", value
    )
    value = value.replace(r'\"o', "ö").replace(r"\'e", "é")
    return value


INLINE_PANDOC_MATH_RE = re.compile(r"\$`(.*?)`\$")
HTML_INLINE_MATH_RE = re.compile(
    r'<span class="math inline">\$(.*?)\$</span>', re.DOTALL
)


def normalize_markdown_math(markdown: str) -> str:
    """Convert Pandoc's math representation to repository conventions."""

    markdown = INLINE_PANDOC_MATH_RE.sub(
        lambda match: f"`{normalize_math(match.group(1))}`", markdown
    )
    markdown = HTML_INLINE_MATH_RE.sub(
        lambda match: f"`{normalize_math(match.group(1))}`", markdown
    )
    lines = markdown.splitlines()
    output = []
    position = 0
    while position < len(lines):
        if lines[position].strip() != "``` math":
            output.append(lines[position])
            position += 1
            continue
        closing = position + 1
        while closing < len(lines) and lines[closing].strip() != "```":
            closing += 1
        if closing == len(lines):
            # Leave malformed input visible for diagnostics.
            output.extend(lines[position:])
            break
        body = "\n".join(lines[position + 1 : closing])
        if TIKZCD_RE.search(body):
            draft = render_tikzcd(body, normalize_math)
            output.extend(
                [
                    f"<!-- rosetta-diagram: {draft.stable_id}; review: pending -->",
                    "",
                    f"*{draft.description.capitalize()} (automatic draft).*",
                    "",
                    "```text",
                    draft.art,
                    "```",
                ]
            )
        else:
            output.extend(["```text", normalize_math(body), "```"])
        position = closing + 1
    result = "\n".join(output)
    if markdown.endswith("\n"):
        result += "\n"
    return result
