# HoTT Rosetta

HoTT Rosetta generates self-contained literate Agda Markdown from the LaTeX
source of *Introduction to Homotopy Type Theory*. Durable inputs are
`book/`, `converter/`, and `data/`; the tracked product is `rosetta-book/`.

The required range is Chapters 3--22. Current work prioritizes completing Agda
for every section; exercise Agda is deferred unless a section depends on it.
File presence and optional review state do not imply completion.

## Setup

```sh
git clone --recurse-submodules https://github.com/daniel-carranza/HoTT-Rosetta.git
cd HoTT-Rosetta
```

For an existing clone, run `git submodule update --init --recursive`.
The project requires Python, Pandoc, and Agda; the converter itself uses only
Python's standard library. The pinned agda-unimath submodule supplies source
provenance but is never imported by generated modules.

## Commands

```text
python3 rosetta.py convert                 # regenerate Chapters 3--22
python3 rosetta.py convert --from 1 --to 22
python3 rosetta.py candidate 8 4           # regenerate one section
python3 rosetta.py typecheck-candidate 8 4
python3 rosetta.py typecheck-all
python3 rosetta.py review --web            # optional local review UI
```

Required validation:

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

The active output directory is configured in `data/project-layout.json`.
Read chapter or section files in that directory. See
[`docs/review-guide.md`](docs/review-guide.md) for the optional review UI.

## Contributing

Put durable corrections in converter code or versioned data, then regenerate.
Never invent Agda: copy exact or analogous code from the pinned agda-unimath
checkout, record commit/file/line/hash provenance, classify adaptations
honestly, and use repository-local imports. If no applicable source exists,
record the gap.

See [`docs/conversion-contract.md`](docs/conversion-contract.md) for enforced
conversion rules and [`docs/implementation-handoff.md`](docs/implementation-handoff.md)
for the current work plan. Agents relocating Agda should also follow the
repository-local
[`Agda block placement`](skills/hott-rosetta-translation/references/agda-block-placement.md)
reference.

## Layout

- `book/`: LaTeX source
- `rosetta-book/`: generated literate Agda
- `converter/`: conversion, checks, and review UI
- `data/`: configuration, provenance, gaps, coverage, and reviews
- `tests/`: unit tests
- `skills/`: agent workflow
- `external/agda-unimath/`: pinned provenance source
- `archive/legacy-rosetta/`: inactive historical backup

The prose comes from the [arXiv book](https://arxiv.org/abs/2212.11082), and
formalizations are sourced from
[agda-unimath](https://unimath.github.io/agda-unimath/).
