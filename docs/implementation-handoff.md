# Implementation handoff

Updated 2026-09-06.

## Objective

Complete section prose and section Agda for Chapters 3--22 before the remaining
exercise Agda. Chapters 1--2 are optional. The next working range is Chapters
10--13.

`docs/conversion-contract.md` is the policy authority. Do not duplicate it
here. Recompute inventories; file presence and review state do not prove
completion.

## Current state

Work continues on `main`.

- Routine checks report `deferred` without running Agda when a file contains or
  imports a manifest block marked `exercise`. `--force` runs the unchanged Agda
  command. Deferred never means passed.
- Sections 10.1 and 10.3 have item-by-item coverage audits and passing candidate
  checks; both are recorded complete. See `docs/section-agda-audit.md`.
- Definition 10.2.1 is marked `exercise` on `main`. Its solution is published
  as `511f171` on the shared proposal, with `ev-point` at Remark 2.2.2.
- Remark 10.1.2 needs no separate declaration. Example 10.2.2 now has an
  upstream-analogous unit singleton witness, checked on the proposal.
- Section 10.4 is deferred on `main` at Lemma 10.4.5. Its solution is commit
  `5e5a5cd` on `proposal/agda-exercise-solutions` and passes Agda there.
- Chapters 11--13 currently have no curated section blocks or recorded complete
  sections. Verify this before work begins.
- Do not transfer stale review evidence for Sections 8.1, 8.5, 9.1, or 9.2;
  these remain reserved for manual review.

The latest validation passed the full unit suite, `python3 rosetta.py check`,
and `git diff --check`. Proposal `511f171` passes candidate Sections 2.2, 10.2,
and 10.4 and aggregate Chapters 2--10. On `main`, Sections 10.2 and 10.4 and
Chapter 10 remain deferred, never recorded as passed.

## Next work

The five assigned Chapter 10 steps are done. Keep Definition 10.2.1 and Lemma
10.4.5 empty on `main`; do not merge the proposal to make `main` pass. The
audit also records that Definition 10.4.4's final cancellation result is
provided only on the proposal as part of the existing coherence exercise.

Formalize Chapters 11, 12, and 13 in order, starting with Section 11.1. Chapter
13 contains Axiom 13.1.3: keep any assumption explicit and never describe it as
a proof.

For each section, inventory every numbered mathematical item, search pinned
agda-unimath for exact code before analogues, record full provenance,
regenerate, and typecheck. If an auxiliary result belongs in an earlier
complete file, follow the exercise and shared-proposal workflow in the contract.
There is no exercise threshold.

## Essential files

- `data/project-layout.json`: active output path.
- `data/rosetta-files.json`: stable generated filenames.
- `data/agda-blocks*.json`: curated Agda and provenance.
- `data/agda-gaps.json`: explicit gaps.
- `data/agda-coverage.json`: audited section-completion evidence.
- `docs/agda-training-exercises.md`: exercise index and proposal commits.
- `docs/invisible-math.md`: required mathematics and natural homes.

Never use `archive/legacy-rosetta/` for active work.

## Validation

For every changed section containing Agda:

```text
python3 rosetta.py typecheck-candidate N M
```

Typecheck changed exercise Agda and affected aggregate chapters. A deferred
result does not satisfy a completed-file check; the proposal must pass Agda.

Before handoff:

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

Preserve unrelated work. Use focused commits. Do not reset, clean, overwrite,
pull, push, amend, or rewrite history unless the task requires it.
