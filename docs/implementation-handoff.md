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
- All six items in Section 11.1 have curated code, with the needed results
  from Exercises 9.4, 10.2, and 10.3. Section 9.2's formerly blocked Corollary
  9.2.8 is restored from a passing scratchpad, and retract data is defined at
  Definition 9.2.1. These changed files pass candidate checks on `main`.
- Sections 11.2 and 11.3 now have curated code. Proposal `a48a60e` passes
  Section 11.2 and Chapter 11; `c41af9d` passes Section 11.3 and Chapter 11.
  They are deferred on `main` through both Chapter 10 training exercises.
- Theorem 11.4.2 is a new empty training site on `main`: its fiber-orientation
  equivalence belongs at Definition 10.3.1, in complete Section 10.3. The
  solution is published as `63e5e49` on the shared proposal, with the complete
  fiber equivalence at that earlier definition. Main's Section 10.3 is unchanged.
  No Chapter 11 section is recorded complete on `main`.
- Section 11.5 now has all four coproduct identity equivalences, code
  computations, reflexivity, and total-space contraction. Its theorem code
  follows the delayed proof after Proposition 11.5.4. Proposal `3bbc564`
  passes its candidate and aggregate Chapters 9--11; it remains deferred
  on `main`. The indexed upstream relation realizes the book's four cases
  by equivalences, not judgmental reduction; see the section audit.
- Section 11.5's dependencies add equivalence composition to Exercise 9.4
  and the empty-type equivalence criterion to Example 9.2.9. The latter's
  still-missing displayed laws are explicit gaps; neither earlier file was
  complete. Both changed candidates pass on `main`.
  Section 11.6 now has a dependent-identity-system predicate and explicit
  connections between all six theorem conditions, including the converse.
  Exercise 10.6 supplies the required contractible-base equivalence.
  Its Example 11.6.3 is a newly recorded empty training site: the inversion
  equivalence needs `inv-inv` in complete Section 5.2. Proposal solution
  `6bd180b` places this auxiliary after the inverse laws and the two required
  groupoid equivalences at Exercise 9.1. It passes all of Section 11.6 and
  aggregate Chapters 5--11, including the six-condition theorem.
  Section 12.1 now has source-backed code for all four numbered items,
  including the unit-embedding condition and its converse. Exercise 10.1's
  required contractible-identity proof passes on `main`. Section 12.1 is
  deferred through Theorem 11.4.2; its actual proposal validation is the
  immediate next action. Sections 12.2--13.5 have no curated section blocks.
- Total-map base parameters and TikZ spacing options now render correctly;
  affected documents were regenerated. Blocked scratchpad drafts are now
  included in their candidate checks, so omitted code cannot yield a false pass.
- Do not transfer stale review evidence for Sections 8.1, 8.5, 9.1, or 9.2;
  these remain reserved for manual review.

The latest validation passed the full unit suite (151 tests on `main`, 154 on
the proposal), `python3 rosetta.py check`, and `git diff --check`. Proposal
`6bd180b` passes candidate Sections 5.2 and 11.6, Exercises 9.1 and 10.6,
and aggregate Chapters 5--11. Earlier proposal
`3bbc564` passes candidate Section 11.5 and aggregate Chapters 9--11; the
earlier `63e5e49` checks Sections 10.3 and 11.1--11.4. The earlier `511f171`
also checked Section 2.2 and Chapters 2--10.
On `main`, Sections 10.2, 10.4, and 11.1--11.6, Exercise 10.6, and Chapters
10--11 remain deferred, never recorded as passed. The prose of Sections
11.2--11.6 was compared item by item with the book and has no unresolved references or raw
TeX commands. No review evidence or completion status was inferred from this.

## Next work

The five assigned Chapter 10 steps and the Chapter 11 section formalizations
are done, with the recorded training holes retained. Keep Definition 10.2.1,
Lemma 10.4.5, Theorem 11.4.2, and Example 11.6.3 empty on `main`; do not merge
the proposal to make `main` pass. The audit also records that Definition 10.4.4's final cancellation
result is provided only on the proposal as part of the existing coherence exercise.

Validate Section 12.1 and affected aggregates on the shared proposal, then
continue Sections 12.2--13.5 in order. Section 12.1's fourth condition uses
the exact proof in pinned `foundation/subterminal-types`, not the later
truncation-theory wrapper in `foundation/propositions`.
Avoid importing function extensionality from upstream ahead of its narrative
home. Chapter 13 contains Axiom 13.1.3: keep that assumption explicit and
never describe it as a proof.

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
