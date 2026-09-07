---
name: hott-rosetta-translation
description: Convert HoTT book LaTeX, curate provenance-backed Agda, and maintain the optional review workflow.
---

# HoTT Rosetta translation

## Start

Read `AGENTS.md`, `docs/implementation-handoff.md`,
`docs/conversion-contract.md`, `docs/agda-training-exercises.md`, and
`docs/invisible-math.md`. Then read only the needed references:

- section work: `references/section-files.md` and
  `references/latex-to-markdown.md`;
- block placement or relocation: `references/agda-block-placement.md`;
- chapter aggregation: `references/chapter-files.md`;
- exercise files: `references/exercise-files.md`.

Inspect the LaTeX, converter, manifests, and active generated output in scope.
Read the output path from `data/project-layout.json`. Never use
`archive/legacy-rosetta/`.

## Agda work

Complete section Agda for Chapters 3--22 before remaining exercise Agda.
Chapters 1--2 are optional. File presence and review state do not establish
completion.

For each mathematical item, search pinned agda-unimath for exact code, then
close analogues. Never invent code. Use repository-local imports and record
the required source commit, file, inclusive lines, hash, code, destination,
item, provenance kind, and adaptation note.

Place code where the mathematics belongs while preserving Agda dependency
order. Regenerate and check every changed section and downstream consumer.

If a later block needs auxiliary mathematics whose natural home is an earlier
complete file, leave the later block empty. Follow the full exercise workflow
in `docs/conversion-contract.md`; record the exercise and invisible mathematics,
and publish its complete solution on `proposal/agda-exercise-solutions`. This
workflow is mandatory for agents. Humans may edit either branch freely.

`deferred` means Agda was not run. Do not alter Agda options, hide mathematics,
or reinterpret errors. The proposal and affected later files must pass Agda.

## Validation

Add review comments only for useful mathematical, source, or dependency
questions.

For every changed section containing Agda:

```text
python3 rosetta.py typecheck-candidate N M
```

Also check changed exercise Agda and affected aggregates. Before handoff:

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

Preserve unrelated work. Do not pull, push, reset, clean, amend, or rewrite
history unless the task requires it.
