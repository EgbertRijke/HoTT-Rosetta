# Implementation handoff

Updated 2026-09-07.

## Objective

Complete section prose and section Agda for Chapters 3--22 before the remaining
exercise Agda. Chapters 1--2 are optional. The next working range is Chapters
14--17.

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
  proofs, with no new auxiliary or exercise Agda. Published proposal merge
  `6c408d4` passes its actual candidate and aggregate Chapter 13 checks.
  Section 13.4 now has eleven provenance-backed blocks for all three
  conditions and implications, including the full two-fiber converse.
  Its transport substitution is an expansion of a pinned wrapper around
  Section 9.3's existing `tr-ap`, not a new missing auxiliary. Published
  proposal merge `b42184f` passes actual Agda for the section and aggregate
  Chapter 13 without corrections or new solutions. Section 13.5 now has
  twelve curated blocks for its three items, intervening bounded family,
  both successor-lemma laws, and the full delayed theorem proof with both
  computation rules. The lemma's additional identity-type equivalence is
  a new empty training site needing Exercise 9.1's existing proposal
  inverse-concatenation equivalence. The required Exercise 12.4(c) forward
  implication is curated at its exact home; its other parts remain gaps.
  Published proposal solution `e8105dd` restores that retained equivalence
  without proof corrections or earlier-file additions, and passes the
  entire section, Exercise 12.4, and aggregate Chapters 8 and 12--13.
- Total-map base parameters and TikZ spacing options now render correctly;
  affected documents were regenerated. Blocked scratchpad drafts are now
  included in their candidate checks, so omitted code cannot yield a false pass.
- Do not transfer stale review evidence for Sections 8.1, 8.5, 9.1, or 9.2;
  these remain reserved for manual review.

The latest main validation passed all 169 unit tests,
`python3 rosetta.py check`, and `git diff --check`, with 571 manifest blocks
(176 exact, 337 adapted, 58 historical/local). Section 8.2 and aggregate
Chapter 8 pass after the cases-display repair. Section 13.5, Exercise
12.4, and aggregate Chapters 12--13 defer through recorded training sites.
The preceding Exercise 9.5
candidate and aggregate Chapter 9 checks passed; neither changed in the
Section 13.5 work. Sections 13.1--13.5 and Chapter 13
are deferred until their existing training dependencies are supplied.
Proposal `e8105dd` passes all 174 unit tests, repository and whitespace
checks, candidate Sections 8.2 and 13.5, Exercise 12.4, and aggregate
Chapters 8 and 12--13.
Proposal `b42184f` passes all 169 unit tests, repository and whitespace
checks, candidate Section 13.4, and aggregate Chapter 13.
Proposal `6c408d4` passes all 168 unit tests, repository and whitespace
checks, candidate Section 13.3, and aggregate Chapter 13.
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
Lemma 10.4.5, Theorems 11.4.2, 12.2.3, 12.3.4, and 12.4.7, Example 11.6.3,
and Lemma 13.5.3's case-evaluation-identification equivalence empty
on `main`; do not merge the proposal to make `main` pass. The audit also
records that Definition
10.4.4's final cancellation result is provided only on the proposal as part
of the existing coherence exercise.

Continue Section 14.1, `book/univalence.tex`, lines 11--109, and inspect
the Chapter 14 introduction at lines 1--10. Inventory all six numbered
items and all six parts of Example 14.1.4, not just the axiom.
Theorem 14.1.1's three equivalence conditions must remain hypothesis-
parametric before Axiom 14.1.2. Use the explicit fundamental-theorem and
identity-system conversions, not the globally assumed convenience proofs.
Pinned `foundation-core/univalence` supplies the canonical map and the
two contractibility implications; `foundation/equivalence-induction`
supplies the induction predicate and its two contractibility implications.
The canonical map uses `equiv-tr id`: inspect the existing Exercise 9.1
transport equivalence and apply the training policy before changing any
earlier main account. Introduce the pinned univalence postulates from
`foundation/univalence` only at the book's axiom and label the assumption.
Never call those postulates a proof.

For the smallness material, start with `foundation-core/small-types`
(not the later replacement theorem in `foundation/small-types`) and
`foundation/small-maps`. The core small-type definition has the book's
orientation `Σ X, A ≃ X`; its property proof uses precomposition between
equivalence types, which is distinct from Section 13.4's ordinary-function
precomposition. Trace the dependencies and natural homes. Account for the
intervening type-former invariance statements and all smallness examples,
including finite types and the explicit later Russell reference.
Corollary 14.1.6's literal inclusion of overlapping universes is not
represented by Agda's disjoint universes. Inspect the pinned raising-
universe embedding analogue and retain any representation gap explicitly,
as in Remark 12.4.2; do not claim a literal inclusion from a lifted proof.

Section 13.5's training exercise is solved and published as `e8105dd`.
It reuses Exercise 9.1's existing inverse-concatenation equivalence and
needs no earlier auxiliary addition. Main keeps the later block empty.

Section 13.5's curation preserves both computation rules and the full
delayed theorem proof. Keep its code-order anchors, the complete case-map
equivalence and proposition assertions, and the existing explicit-index
case splitter from Exercise 7.3. The source's successor contradiction is
the existing order contradiction at reflexivity; the separate reflexive
case law is an instance of the already stated `f(p)=x`. No earlier
complete section or existing exercise code is enlarged. The new required
Exercise 12.4(c) supplies only the forward implication; keep its remaining
parts and custom-list presentation gaps explicit. The renderer now
preserves the asterisk reference and both cases displays. Section 8.2's
Collatz display was regenerated by the same tested rule, without Agda
changes or reserved review updates.

Section 13.4 is curated and validated. It preserves all three conditions
and the full converse using the fibers at `id` and `f`. Keep the existing local
coherent-inverse conversion, not upstream path-split machinery. The
missing name `substitution-law-tr` is only a wrapper around the existing
Section 9.3 `tr-ap`: the pinned definition is expanded in the new proof,
with secondary provenance recorded. No earlier complete file was enlarged
and no new training exercise is needed. The converse specializes the full
structured-type proof to ordinary types while retaining its inverse and
both homotopies. The book's entire prose is unchanged.

Section 13.3's three numbered results, both proofs, and introductory
ordinary specializations are curated and validated. Keep the explicit
induction proofs, their scope-order headings, and the original prose's
redundant function-extensionality wording and free-`p` typo as documented
in the audit. No source prose correction, new exercise, or earlier complete
file enlargement was needed.

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
