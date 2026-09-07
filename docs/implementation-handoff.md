# Implementation handoff

Updated 2026-09-07.

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
  deferred through Theorem 11.4.2. Proposal `0c3d8b1` passes its candidate,
  Exercise 10.1, and aggregate Chapters 10--12.
  Section 12.2 now has curated code for all four numbered items, including
  both directions of the embedding and projection criteria. Theorem 12.2.3
  is a new empty training site because it directly needs `equiv-fiber` in
  complete Section 10.3. Published proposal `7b6b28c` reuses the auxiliary
  from `63e5e49` and passes the section, Exercise 10.7, and aggregate Chapters
  10--12. Exercise 10.7(a)'s projection-fiber equivalence also passes on
  `main`; parts (b) and (c) remain explicit gaps.
  Section 12.3 now has source-backed code for all five numbered items,
  including both axiom-K implications and the arbitrary-map assertion in
  Theorem 12.3.4. That theorem's based proof is a new empty training site:
  its retract fundamental theorem and total-map laws belong in the earlier
  Chapter 11 accounts. Proposal `b96fdf3` adds the total-map laws at
  Definition 11.1.1 and the retract variant at Theorem 11.2.2, and restores
  the later proof. Every Chapter 11 section, Sections 12.1--12.3, and
  aggregate Chapters 10--12 pass there. No exercise Agda is added.
  Section 12.4 now has seventeen curated blocks accounting for its
  introduction and seven items. Remark 12.4.2 has an explicit representation
  gap: lifted-type invariance is formalized, but Agda's disjoint universes
  do not literally express the book's overlapping-universe assertion.
  Exercise 12.8(a) is added because the pinned equivalence-invariance proof
  needs identity retracts; its part-(b) proof is a labeled prerequisite at
  Proposition 12.4.5 to avoid an import cycle. Theorem 12.4.7 is a new empty
  training site needing the specialized fiber equivalence at Example 11.6.3
  and transport equivalence at its exact Exercise 9.1 home. Published
  proposal `31222b8` supplies both auxiliaries and restores both theorem
  implications unchanged. It passes Sections 11.6 and 12.4, Exercises
  9.1 and 12.8, and aggregate Chapters 9--12. Section 13.1 now has twenty
  curated blocks for its seven items, keeping both initial equivalence
  results hypothesis-parametric and introducing the pinned coherent-inverse
  postulates only at Axiom 13.1.3. Published proposal merge `dc97e2f` passes
  its actual Agda check and aggregate Chapter 13 with no new auxiliary;
  main correctly defers it. Section 13.2 now has seven curated blocks for
  all four numbered items and the intervening products-of-fibers equivalence.
  Its needed Exercise 9.5(b) passes on main; part (a) remains a gap.
  The choice proof's record-Σ η difference from the book is explicit.
  Proposal `161b3c1` passes its actual Agda check and Chapters 9 and 13.
  Its direct-import correction for existing Exercise 9.4 composition is
  also on main, without any training solution.
  Section 13.3 now has five provenance-backed blocks for the three numbered
  universal properties and both introductory ordinary-family specializations.
  It preserves the explicit Σ-induction and twice-extensional path-induction
  proofs, with no new auxiliary or exercise Agda. Its actual proposal
  validation is pending. Sections 13.4--13.5 have no curated section blocks.
- Total-map base parameters and TikZ spacing options now render correctly;
  affected documents were regenerated. Blocked scratchpad drafts are now
  included in their candidate checks, so omitted code cannot yield a false pass.
- Do not transfer stale review evidence for Sections 8.1, 8.5, 9.1, or 9.2;
  these remain reserved for manual review.

The latest main validation passed all 163 unit tests,
`python3 rosetta.py check`, and `git diff --check`, with 547 manifest blocks
(175 exact, 314 adapted, 58 historical/local). The preceding Exercise 9.5
candidate and aggregate Chapter 9 checks passed; neither changed in the
Section 13.3 work. Sections 13.1--13.3 and Chapter 13
are deferred until their existing training dependencies are supplied.
Proposal `161b3c1` passes all 167 unit tests, repository and whitespace
checks, Section 13.2, Exercise 9.5, and aggregate Chapters 9 and 13.
Proposal `dc97e2f` passes all 165 unit tests, repository and whitespace
checks, candidate Sections 2.2 and 13.1, and aggregate Chapters 1--6 and
13--14. Section 12.3 and
aggregate Chapters 10--12 are deferred. Section 12.4 is also deferred;
its needed Exercise 12.8(a) candidate passes. Proposal `31222b8` passes
all 161 tests, Sections 11.6 and 12.4, Exercises 9.1 and 12.8, and
aggregate Chapters 9--12. Exercise 10.7's unchanged candidate
passed in the preceding validation. Proposal `b96fdf3` passes all 158
unit tests, candidate Sections 11.1--11.6 and 12.1--12.3, aggregate Chapters
10--12, and the repository and whitespace checks. Earlier proposal
`7b6b28c` passes Section 12.2, Exercise 10.7, and aggregate Chapters 10--12.
Earlier proposal
`0c3d8b1` passes candidate Section 12.1, Exercise 10.1, and aggregate Chapters
10--12. Proposal `6bd180b` passes candidate Sections 5.2 and 11.6, Exercises
9.1 and 10.6, and aggregate Chapters 5--11. Earlier proposal
`3bbc564` passes candidate Section 11.5 and aggregate Chapters 9--11; the
earlier `63e5e49` checks Sections 10.3 and 11.1--11.4. The earlier `511f171`
also checked Section 2.2 and Chapters 2--10.
On `main`, Sections 10.2, 10.4, 11.1--11.6, and 12.1--12.4, Exercise 10.6, and
Chapters 10--12 remain deferred, never recorded as passed. The prose of
Sections 11.2--11.6 and 12.1--12.3 was compared item by item with the book and has
no unresolved references or raw TeX commands. No review evidence or completion
status was inferred from this.

## Next work

The five assigned Chapter 10 steps and the Chapter 11 section formalizations
are done, with the recorded training holes retained. Keep Definition 10.2.1,
Lemma 10.4.5, Theorems 11.4.2, 12.2.3, 12.3.4, and 12.4.7, and Example 11.6.3 empty
on `main`; do not merge the proposal to make `main` pass. The audit also
records that Definition
10.4.4's final cancellation result is provided only on the proposal as part
of the existing coherence exercise.

First validate the newly curated Section 13.3 and Chapter 13 on the shared
proposal after bringing in current main. No new training solution is needed.
Then continue Sections 13.4--13.5 in order. Section 13.3 is `book/funext.tex`,
lines 282--377: Theorem 13.3.1 (dependent universal property of Σ),
Corollary 13.3.2 (currying for ordinary products), and Theorem 13.3.3
(dependent universal property of identity types). Preserve both introductory
ordinary-family specializations as well as the numbered statements and
complete proofs. Pinned `foundation/universal-property-dependent-pair-types`
has the explicit `eq-htpy`/Σ-induction proof; `foundation/universal-property-identity-types`
has the two nested function-extensionality applications and path induction.
Copy only the relevant ranges, not that latter module's unrelated later
univalence arguments. Local `ev-pair` already exists at Remark 4.6.3;
inspect all imports and auxiliary homes before adding code.

Section 13.2's four numbered items and intervening equivalence are curated
and validated, but its record-Σ η representation difference remains
explicit in the audit and gap inventory. The book's full proof and the
labeled shorter pinned proof are both retained; the earlier Σ type is
unchanged. Its right-swap prerequisite is at Exercise 9.5(b); part (a)
remains lower-priority exercise work. No earlier complete section was enlarged.

Section 13.1's seven items and complete proofs are accounted for and
validated. Its pre-axiom results use explicit hypotheses, not the global
`is-torsorial-htpy` used by the pinned homotopy-induction convenience
proof. Keep that boundary and the explicit coherent-inverse assumption
label; the audit records the comparison with the book's axiom.

Section 12.4's audit records the explicit overlapping-universe
representation gap and the checked lifted analogue; do not erase that gap
or infer completeness from polymorphism. Its prose is unchanged after
removing the four explicit Agda headings and code, but raw comparison
counts those headings (98.26%, 9/13). Preserve the regression test rather
than calling the raw comparison 100%. The earlier main files stay unchanged.
Add exercise Agda only as needed by sections, accounting for any remaining
exercise assertions. Exercise 10.7's existing custom-list rendering loses
the outer alphabetical labels; the audit records this presentation issue
without claiming the exercise complete.
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
