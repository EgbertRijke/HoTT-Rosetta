---
name: hott-rosetta-translation
description: Convert HoTT book LaTeX, curate provenance-backed Agda, and maintain the optional review workflow.
---

# HoTT Rosetta translation

## Start

Read `AGENTS.md`, `docs/implementation-handoff.md`,
`docs/conversion-contract.md`, `docs/agda-training-exercises.md`, and
`docs/invisible-math.md`. Then read only the references needed:

- section work: `references/section-files.md` and `references/latex-to-markdown.md`
- Agda block placement or manifest relocation:
  `references/agda-block-placement.md`
- chapter aggregation: `references/chapter-files.md`
- requested or required exercise work: `references/exercise-files.md`

Inspect the LaTeX, converter, curated data, and active generated output in
scope. Obtain the output path from `data/project-layout.json`; never use
`archive/legacy-rosetta/`.

## Work

Prioritize remaining section Agda across Chapters 3--22. Defer exercise Agda
unless a section depends on it.

For each section item, search pinned `external/agda-unimath` for exact code and
then close analogues. Copy the closest applicable source; never invent code.
Preserve upstream names and structure when possible, make only necessary local
adaptations, and use repository-local imports.

Record commit, file, inclusive lines, SHA-256 digest, stored code, destination,
item, and honest `exact` or `adapted` provenance in `data/agda-blocks*.json`.
If no source applies, record a gap and continue.

Place each block according to both the prose and Agda's sequential dependency
scope. Prefer the matching item's end marker, use `after_text` only for a
specific intermediate narrative step, and use a labeled section-level
prerequisite group when dependencies make a closer placement invalid. Never
move a declaration without typechecking its new section and its consumers.

Do not enlarge an earlier complete file solely to support a later block. If the
later block needs an absent auxiliary result, leave that block empty. Record
the exercise and its reason in `docs/agda-training-exercises.md`. In
`docs/invisible-math.md`, record the exact upstream results, their natural
mathematical homes, their order, and their later uses.

Use `proposal/agda-exercise-solutions` for every exercise. Create and publish it
from current `main` when the first exercise appears. First publish the empty
block and both mathematical records on `main`. Fetch and inspect both remote
branches. Bring current `main` into the proposal without rewriting its history.
Add the pinned blocks where they fit best, record each choice, and make one
focused solution commit. Regenerate and typecheck every affected section and
later user. Push only the proposal branch. On `main`, record the proposal
branch and solution commit in the exercise index, commit and push that record,
and keep the handoff current. Never merge the proposal automatically or
force-push it.

This workflow is mandatory for agents. Humans may edit either branch without
following it. Inspect and preserve their work.

Make durable prose or notation repairs in converter code or versioned data,
regenerate every affected file, and add regression tests for recurring rules.

## Comments and validation

Add a short `codex` review comment only for a useful mathematical, source, or
dependency question. Do not record routine searches or passing checks.

Typecheck every changed section containing Agda:

```text
python3 rosetta.py typecheck-candidate N M
```

Before handoff run:

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

Preserve unrelated work. Focused commits are allowed: inspect the worktree,
stage only task changes, validate, and use a clear message. Do not reset, clean,
overwrite, pull, push, or rewrite history unless the task requires it.
