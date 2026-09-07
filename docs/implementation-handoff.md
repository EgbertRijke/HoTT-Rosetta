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
- Sections 10.1 and 10.3 pass candidate checks.
- Definition 10.2.1 is now marked `exercise` on `main`; Section 10.2 is
  deferred because `ev-point` is absent. Publishing and validating its shared
  proposal solution is the immediate next step.
- Section 10.4 is deferred on `main` at Lemma 10.4.5. Its solution is commit
  `5e5a5cd` on `proposal/agda-exercise-solutions` and passes Agda there.
- Chapters 11--13 currently have no curated section blocks or recorded complete
  sections. Verify this before work begins.
- Do not transfer stale review evidence for Sections 8.1, 8.5, 9.1, or 9.2;
  these remain reserved for manual review.

The latest validation passed the full unit suite, `python3 rosetta.py check`,
and `git diff --check`.

## Next work

Finish Chapter 10 before Chapter 11:

1. Audit Remark 10.1.2 and decide whether it needs Agda.
2. Complete the Definition 10.2.1 exercise workflow. Mark its manifest block
   `exercise` on `main`; update and publish the exercise records; bring current
   `main` into the shared proposal; place `ev-point` at its natural home in
   Remark 2.2.2 there; check Sections 2.2 and 10.2 and affected aggregates;
   push the proposal; then record its solution commit on `main`.
3. Decide whether Example 10.2.2 needs Agda.
4. Audit Section 10.3 before recording completion.
5. Leave Lemma 10.4.5 empty on `main`; do not merge its proposal merely to make
   `main` pass.

Then formalize Chapters 11, 12, and 13 in order, one section at a time. Chapter
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
