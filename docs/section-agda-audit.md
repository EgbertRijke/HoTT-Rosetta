# Section Agda audit

Audited against the LaTeX, generated prose, and curated declarations, not file
presence or review state. Source locations and hashes are in the block
manifests at pinned commit `c85d7fb834778f96a66576318cdc4ef3d4b80a26`.
The completion list contains only sections with all required mathematics and
passing candidate checks on `main`. Deferred sections remain outside it.

## Chapter 10 (2026-09-06)

All 19 numbered items and their adjacent proofs/constructions in
`book/contractible.tex` are present in the generated sections. The contraction,
singleton induction, fiber, and coherent inverse proofs were compared to the
stored upstream excerpts. Known choices are recorded below.

| Item | Formalization and coverage |
| --- | --- |
| Definition 10.1.1 | `is-contr`, `center`, and `contraction`; the upstream normalized contraction also supplies `coh-contraction`. |
| Remark 10.1.2 | No separate Agda declaration is needed: expanding homotopy, constant function, and identity gives exactly `(x : A) → c ＝ x`. This is a judgmental restatement of the contraction type, not an additional path equality. |
| Example 10.1.3 | `is-contr-unit`, including the center and contraction. |
| Theorem 10.1.4 | `is-contr-Id`, the center and path-induction contraction of the total path space. The upstream `is-torsorial` abbreviation is expanded to contractibility of the dependent sum. |
| Definition 10.2.1 | Empty training site on `main`; definition, induction operator, and computation rule restored on proposal `511f171`, with evaluation at Remark 2.2.2. |
| Example 10.2.2 | Requires Agda: `is-singleton-unit` packages `ind-unit` and `refl-htpy`. Adapted from the total-path singleton example, preserving its two-field construction and computation proof. Checked on proposal `511f171`. |
| Theorem 10.2.3 | `ind-singleton`, `compute-ind-singleton`, and both directions `is-singleton-is-contr` / `is-contr-is-singleton`; checked on proposal `511f171`. |
| Definition 10.3.1 | `fiber`, with both projections; `fiber'` is the upstream opposite-path variant. |
| Definition 10.3.2 | `Eq-fiber`, reflexivity, the canonical map, and its inverse by pair/path induction. The upstream second path is `ap f α ∙ p' ＝ p`, the inverse orientation of the book's `p ＝ ap f α ∙ p'`. |
| Proposition 10.3.3 | `is-section-eq-Eq-fiber`, `is-retraction-eq-Eq-fiber`, `is-equiv-Eq-eq-fiber`, and the packaged equivalence. This excerpt continues the anonymous module begun at Definition 10.3.2. |
| Definition 10.3.4 | `is-contr-map`, contractibility of each fiber. |
| Theorem 10.3.5 | Inverse from fiber centers, section from the second projection, retraction from the first projection of a path in the fiber, then `is-equiv-is-contr-map`. |
| Definition 10.4.1 | Coherent inverse quadruple, projections, and underlying inverse. |
| Proposition 10.4.2 | Center and contraction of each fiber, then `is-contr-map-is-coherently-invertible`. |
| Definition 10.4.3 | `nat-htpy`; the upstream equation is the inverse orientation of the book's naturality equation. |
| Definition 10.4.4 | `nat-htpy-id` alone is only the intermediate naturality equation. The actual cancellation result `coh-htpy-id` is supplied here on proposal `5e5a5cd` as part of the recorded Lemma 10.4.5 exercise; it remains absent on `main`. |
| Lemma 10.4.5 | Empty on `main`; the adjusted section and higher coherence are proved on proposal `5e5a5cd`, retained and rechecked at `511f171`. |
| Theorem 10.4.6 | Composition of the preceding implications, checked on the proposal because of Lemma 10.4.5. |
| Corollary 10.4.7 | `is-contr-Id'`; upstream reverse path induction proves the same claim directly, while the book uses the fiber of the identity equivalence. |

Sections 10.1 and 10.3 pass candidate Agda checks and have complete required
coverage. Sections 10.2 and 10.4 and Chapter 10 are intentionally deferred on
`main`. Proposal `511f171` passes Sections 2.2, 10.2, and 10.4 and aggregate
Chapters 2--10. No optional reviewer decisions were transferred or refreshed.

## Section 11.1 (2026-09-06)

All six items and their proofs in `book/fundamental.tex` have curated code.
The main source is `foundation-core/functoriality-dependent-pair-types`, with
the separate fiberwise-equivalence predicate from
`foundation-core/families-of-equivalences`. Full commit, ranges, and hashes are
recorded in `data/agda-blocks-chapter-11.json`.

| Item | Formalization |
| --- | --- |
| Definition 11.1.1 | `tot`, preserving the base coordinate. |
| Lemma 11.1.2 | `compute-fiber-tot`, its forward and inverse maps, and both homotopies by pair/path induction. |
| Theorem 11.1.3 | `is-fiberwise-equiv`, both implications between it and `is-equiv (tot f)`, and `equiv-tot`. |
| Lemma 11.1.4 | `map-Σ-map-base`, its fiber equivalence, and the implications for contractible maps and equivalences. |
| Definition 11.1.5 | `map-Σ`, changing the base and fiber coordinates. |
| Theorem 11.1.6 | `triangle-map-Σ`, both equivalence implications, and `equiv-Σ`. The triangle's anonymous module is restored after splitting it from Definition 11.1.5; `map-Σ` therefore receives `D` explicitly. |

Only section dependencies were added to Exercises 9.4, 10.2, and 10.3:
triangle laws and 3-for-2, preservation of contractibility by retracts, and
3-for-2 for contractible types and equivalences. Unused parts of Exercises
9.4 and 10.3 remain explicit gaps. Section 9.2 was not a complete
formalization: Corollary 9.2.8 was blocked. Its existing source excerpt was
completed via a passing scratchpad by restoring its module and using the
section inverse proved in Proposition 9.2.7. The retract-data type belongs
with Definition 9.2.1, which already introduces that notion in the book.
No complete earlier file was enlarged and no review evidence was refreshed.

Section 9.2 and the three changed exercise candidates pass on `main`.
Section 11.1 remains deferred through Lemma 10.4.5 and is not in the
completion list. Published proposal `dc1ffed` passes candidate Sections 10.2,
10.4, and 11.1 and aggregate Chapters 9--11. Its full unit suite and repository
checks pass. The prose preserves the optional base parameter in `tot_f(g)`;
diagram spacing options are excluded from mathematical node labels. Both
conversion repairs have regression tests and were regenerated throughout the
active output.

## Section 11.2 (2026-09-06)

Both numbered items, the canonical-family specialization, and the full proof
in `book/fundamental.tex` are preserved. Seven curated blocks formalize:

| Item | Formalization |
| --- | --- |
| Definition 11.2.1 | Evaluation at the distinguished pair, the universe-level predicate, and the universe-polymorphic identity-system predicate. |
| Theorem 11.2.2, (i) iff (ii) | `fundamental-theorem-id` and its converse for arbitrary families of maps. The upstream result is stronger: neither direction needs the stipulated equation at the base point. |
| Theorem 11.2.2, (ii) iff (iii) | `is-identity-system-is-contr` specializes the pinned singleton-induction package to the dependent sum and curries its section with the existing `ev-pair`; the computation witness is unchanged. The converse is copied from `identity-systems`, with its module restored. |
| Theorem 11.2.2, canonical family | `fundamental-theorem-id-J` and its converse specialize to path induction. |

The exact upstream identity-system construction uses `is-prop-is-contr`, a
later proposition result. The analogous singleton-induction package instead
uses the book's proof route and already available local results; no missing
auxiliary proof is inserted or hidden. `is-torsorial B` is expanded to
`is-contr (Σ A B)`, and upstream `is-torsorial-Id` is the local `is-contr-Id`.
The three conditions are connected by implication functions, not asserted as
an equivalence of proof types.

The prose comparison has all four headings and nine displays, with no
unresolved references or raw TeX commands. Section 11.2 is deferred on `main`
through both recorded Chapter 10 training exercises and is not recorded
complete. Published proposal `a48a60e` passes the Section 11.2 candidate and
aggregate Chapter 11. Its unit suite (147 tests) and repository checks pass.

## Section 11.3 (2026-09-06)

Theorem 11.3.1 and its full induction proof are preserved. The pinned natural
number equality module supplies `map-total-Eq-ℕ`, the center and contraction
of `Σ ℕ (Eq-ℕ m)`, and `is-equiv-Eq-eq-ℕ` by Theorem 11.2.2. The mixed
zero/successor cases are impossible because their equality code is empty;
Agda's coverage checker handles them. The successor case uses `ap` of the
same total-space successor map as the book.

The introductory definitions and canonical map are reused from complete
Section 6.3 without changing it. Only the `is-torsorial` abbreviation is
expanded in the excerpt. Section 11.3 is deferred on `main` through both
Chapter 10 training exercises and is not recorded complete. Published proposal
`c41af9d` passes its candidate and aggregate Chapter 11, all 148 unit tests,
and repository checks. The prose comparison preserves all three headings and
eleven displays, with no unresolved references or raw TeX commands.

## Section 11.4 (2026-09-06)

Both numbered items and the complete proof are preserved.

| Item | Formalization |
| --- | --- |
| Definition 11.4.1 | `is-emb`, the type `_↪_`, its projections, and the induced equivalence on identity types. |
| Theorem 11.4.2 | Empty training block on `main`, solved on proposal `63e5e49`: specialize the pinned contractible-fiber embedding criterion using Theorem 10.4.6 and the fiber-orientation equivalence placed at Definition 10.3.1. The packaged `is-emb-equiv` and `emb-equiv` are retained downstream. |

The auxiliary belongs at Definition 10.3.1, but complete Section 10.3 must
remain unchanged on `main`. The exercise index and invisible-math record
describe the proposal placement. No direct coherent-inverse proof or new
unproven assumption is substituted. Section 11.4 and Chapter 11 are deferred
on `main`, and no Chapter 11 section is marked complete. Proposal `63e5e49`
passes Sections 10.3 and 11.1--11.4 and aggregate Chapters 10--11, all 150
unit tests, and repository checks. The Section 11.4 prose comparison preserves
all four headings and six displays, with no unresolved references or raw TeX
commands. Main's 148 tests pass; its affected Agda checks remain deferred.

## Section 11.5 (2026-09-06)

All four numbered items and both proofs are preserved. The source is the
pinned `foundation/equality-coproduct-types` module.

| Item | Formalization |
| --- | --- |
| Theorem 11.5.1 | `extensionality-coproduct` and all four `compute-eq-coproduct-*` equivalences, placed at the theorem's delayed proof after Proposition 11.5.4, not at its opening announcement. |
| Definition 11.5.2 | Upstream's indexed `Eq-coproduct` and four case equivalences. This represents the book's case table up to equivalence, not by judgmental reduction; both mixed cases are proved equivalent to `empty`. |
| Lemma 11.5.3 | Reflexivity, the canonical map by path induction, and its inverse map. |
| Proposition 11.5.4 | The centers and contractions for both summands. The copied proof contracts the indexed code directly by path induction; the prose retains the book's equivalent calculation with sums and total path spaces. |

Only two dependencies were added earlier. Exercise 9.4 receives equivalence
composition from its existing section/retraction composition laws. Example
9.2.9 receives the general empty-type equivalence criterion underlying the
absorption laws and mixed coproduct cases. Neither earlier file was complete:
Exercise 9.4 has recorded remaining parts, and Example 9.2.9 had none of its
displayed equivalences formalized. An explicit gap keeps those laws visible
despite the new auxiliary; no earlier complete section was enlarged.

The final theorem block keeps `theorem-11.5.1` as its mathematical identity
and uses an exact `after_text` anchor in its later proof. A regression test
checks that all dependencies precede it and that the four case conclusions
occur there. Trailing newlines are normalized after block insertion so an
anchor at the document end does not add a blank line. The prose comparison
has all seven headings and eight displays without unresolved references or
raw TeX commands. Section 11.5 remains deferred on `main` through the Chapter
10 exercises. Published proposal `3bbc564` passes the Section 11.5 candidate
and aggregate Chapters 9--11. Its 151-test suite and repository checks pass;
Section 9.2 and Exercise 9.4 also pass candidate checks on `main`.

Splitting the upstream modules requires explicit `x` and `y` arguments in
the four final composites and an explicit opposite summand in each of the
same-summand cases. The exact corrected draft passed the proposal scratchpad
check, was compared against the unchanged target block on `main`, and was
promoted with an atomic backup. No manual review evidence was refreshed.

## Section 11.6 (2026-09-06)

All three numbered items and the theorem's proof are preserved from
`book/fundamental.tex`, lines 427--515. Definition 11.6.1 specializes the
identity-system predicate to `λ y → D a y c`, with distinguished point `b`
and witness `d`. This is the same alias construction as the pinned homotopy
induction predicate, not a new induction proof.

Theorem 11.6.2 is not represented solely by the upstream forward structure
identity principle. The following explicitly typed specializations are curated
in addition to that construction and its packaged extensionality map:

| Conditions | Declarations and mathematical content |
| --- | --- |
| (i) ↔ (ii) | `dependent-equiv-from-contr` / `dependent-contr-from-equiv` instantiate both fundamental-theorem implications at `B a` and `λ y → D a y c`. The canonical family exists by path induction from `d`, so the universal assertion in (i) implies the hypothesis of the converse. |
| (ii) ↔ (iii) | `dependent-identity-system-from-contr` / `dependent-contr-from-identity-system` instantiate both identity-system implications of Theorem 11.2.2. |
| (iv) ↔ (v) | `structure-equiv-from-contr` / `structure-contr-from-equiv` instantiate the same fundamental theorem at `Σ A B` and its stated structure relation; `(c,d)` supplies the canonical family. |
| (v) ↔ (vi) | `structure-identity-system-from-contr` / `structure-contr-from-identity-system` instantiate the identity-system implications at `(a,b)` and `(c,d)`. |
| (ii) ↔ (v) | `interchange-Σ-Σ`, followed by Exercise 10.6's `left-unit-law-Σ-is-contr`, gives `equiv-total-Eq-structure`. The base identity-system hypothesis is used explicitly by `equiv-total-dependent-identity-system`. `is-torsorial-Eq-structure` and its prime converse transfer contractibility in the two directions. |

These are implication functions, not a claim that the six proof types have
been proved equivalent as types. The generic proofs are reused from their
pinned-source formalizations in Theorem 11.2.2 and Exercise 10.3. The only
earlier exercise added on `main` is Exercise 10.6, whose full inclusion-map
equivalence is needed by the book's displayed total-space calculation.
No generic dependent-sum contraction theorem is added to complete Section
10.1 solely to satisfy the upstream forward construction.

Example 11.6.3 is a new empty training site on `main`. The retained exact
proof route from `foundation/equality-fibers-of-maps` uses dependent-pair
identities, a fiberwise equivalence, and a commuting triangle to establish
the book's first displayed equivalence. Its inversion equivalence requires
`inv-inv` in complete Section 5.2, so its solution belongs on the shared
proposal. Required placements and source ranges are in the exercise index
and invisible-math record. The source proof differs from the book's direct
structure-identity-principle argument; the book's proof prose remains intact.

Two source discrepancies are made explicit rather than silently repaired:
the later formulas write `\ct{p}{q}^{-1}` where the first formula correctly
has `\ct{p}{q^{-1}}`; and the center of `Σ(y:A) x=y` is printed with
`refl_{f(x)}` rather than `refl_x`. The Agda statement uses the correctly
typed `p ∙ inv q`. The renderer's existing unannotated `refl` convention
does not expose that subscript discrepancy in the generated prose.

The `multline` display wrapper is now normalized by the converter, with a
regression test preserving each line. Full Chapters 3--22 regeneration changes
only this section and the new Exercise 10.6. The prose comparison preserves
all five headings and fourteen displays, without unresolved references or
raw TeX commands. Published proposal `6bd180b` passes candidate Sections 5.2
and 11.6, Exercises 9.1 and 10.6, and aggregate Chapters 5--11, with all 154
unit tests and repository checks passing. Main's 151 tests pass, but its Agda
checks remain deferred through the existing Chapter 10 exercises and this new
example. No Section 11.6 completion or optional review decision is recorded.

## Section 12.1 (2026-09-06)

All four numbered items, both proofs, and the transition prose in
`book/hierarchy.tex` are preserved. The generated prose has seven heading
occurrences (six distinct headings) and nine displays. The comparison is
100%, with no unresolved references or raw TeX commands; the duplicate
“Proof” heading is checked by inspecting both proof bodies, not by the
comparison's set-valued heading count alone.

| Item | Formalization |
| --- | --- |
| Definition 12.1.1 | `is-prop`, `Prop`, and their projections from `foundation-core/propositions`. The predicate is exactly contractibility of every identity type. |
| Example 12.1.2 | The generic `is-prop-is-contr` comes from the explicitly cited Exercise 10.1; its type expands the proposition predicate. The unit and empty proposition witnesses and packaged propositions are copied verbatim. |
| Proposition 12.1.3, (i)--(iii) | `all-elements-equal`, `is-proof-irrelevant`, and the implication functions from the pinned proposition module. In particular, `eq-is-prop'` gives (i) → (ii), and `is-proof-irrelevant-all-elements-equal` gives (ii) → (iii). |
| Proposition 12.1.3, (iii) → (iv) → (i) | The exact book proof route is in `foundation/subterminal-types`: assume a point with `is-emb-is-emb`, apply equivalence of contractible types and Theorem 11.4.2, then transfer contractibility along `ap` of the unit map for the converse. The copied `is-subterminal` predicate names condition (iv). |
| Proposition 12.1.4 | `is-equiv-has-converse-is-prop`, the two proposition-homotopies, and the packaged `equiv-iff*` maps from `foundation-core/logical-equivalences`; `iff-equiv` gives the reverse logical implication using the local inverse map. For a fixed map, its converse under `is-equiv` is already `map-section-is-equiv` from Section 9.2. |

The terminal map is expanded to `(λ (_ : A) → star)`, by the pinned
definitions of `terminal-map` and `const`. No general constant-map API is
added to the earlier complete function or unit sections. The point-assumption
lemma belongs in Proposition 12.1.3 because that proof explicitly states it.
Only Exercise 10.1 is added early: it was empty and is required here, and its
contractible-identity proof has no Chapter 12 dependency. Exercise 10.3's
already curated equivalence of contractible types suffices for the proof;
its remaining terminal-map characterization is still lower-priority work.

This section introduces no new training exercise. Its subterminal proof
depends on the existing Theorem 11.4.2 exercise, and transitively on the two
Chapter 10 exercises. Main's Exercise 10.1 candidate passes; Section 12.1 is
deferred, not passed. Published proposal `0c3d8b1` passes Section 12.1,
Exercise 10.1, and aggregate Chapters 10--12, with all 155 tests and repository
checks passing. Main's 152 tests and repository checks also pass, but no
completion or optional review state is inferred from its deferred Agda check.
All generated imports are repository-local; no later truncation theory or
function-extensionality assumption is imported ahead of its narrative home.

## Section 12.2 (2026-09-06)

All four numbered items, three proof bodies, and the introductory and
transition prose in `book/hierarchy.tex`, lines 97--191, are preserved.
The generated section has eight heading occurrences (six distinct headings)
and eleven displays. The prose comparison is 100%, with no unresolved
references or raw TeX commands; the three proof bodies were also inspected
individually, since the comparison counts distinct headings only.

| Item | Formalization |
| --- | --- |
| Definition 12.2.1 | `is-subtype`, `is-property`, the proposition-valued family `subtype`, its total space, membership predicate, inclusion, and action on identities. |
| Lemma 12.2.2 | Both `is-prop-equiv` and `is-prop-equiv'`, together with their map-level versions. The pinned `foundation-core/propositions` proof transfers inhabited contractibility. This proves the book's assertion by a different route from its direct `ap` argument; that full book proof is retained. |
| Theorem 12.2.3 | `is-prop-map` states the fiber condition. The retained `foundation-core/propositional-maps` proof gives both `is-emb-is-prop-map` and `is-prop-map-is-emb` using the fundamental theorem, the fiber-orientation equivalence, and inhabited contractibility. This proof block is a new empty training site on `main`. |
| Corollary 12.2.4 | Proposition-valued inclusion fibers, the subtype-inclusion embedding, its bundled embedding and identity equivalence, and both unbundled implications `is-subtype-is-emb-pr1` / `is-emb-pr1-is-subtype`. Exercise 10.7(a) supplies the projection-fiber equivalence at its exact book home. |

The final forward implication is an explicitly typed application of the
copied bundled-inclusion proof to `(λ x → (B x , H x))`; inclusion reduces
to `pr1`. No new proof is invented. The identity equivalence at the
corollary also supplies the introductory claim that equality in a subtype
is equivalent to equality of the underlying terms. The unused upstream
`injection-subtype` packaging is omitted; no injection API is imported.

Main's complete Section 10.3 is unchanged. The theorem directly requires
its absent `equiv-fiber`, so the new training site is recorded even though
proposal `63e5e49` already supplies that auxiliary for Theorem 11.4.2.
The shared-proposal solution must reuse the existing placement and restore
only this retained theorem block. Its fundamental-theorem applications also
depend on the two existing Chapter 10 exercises. Published proposal `7b6b28c`
implements exactly that solution and passes Section 12.2, Exercise 10.7, and
aggregate Chapters 10--12. All 156 proposal tests and repository checks pass.
Section 12.2 remains deferred on `main`, not complete or passed.

Exercise 10.7(a) passes its ordinary candidate check on `main`. Parts (b)
and (c) remain explicit Agda gaps. All problem text is retained, but the
existing converter renders its custom `subexenum` as a visible div without
the outer alphabetical part labels; this pre-existing exercise presentation
issue is not a claim of complete exercise prose fidelity. Section 12.2 itself
has no such custom list. All 153 main unit tests, repository checks, and
whitespace checks pass. No optional review evidence was refreshed.

## Section 12.3 (2026-09-06)

All five numbered items and the three full proof bodies in
`book/hierarchy.tex`, lines 191--287, are preserved. The generated section
has nine heading occurrences (seven distinct headings) and ten displays.
The prose comparison is 100%, with no unresolved references or raw TeX
commands. All three proof bodies were compared individually, not inferred
from the comparison's set-valued heading count.

| Item | Formalization |
| --- | --- |
| Definition 12.3.1 | `is-set` is the exact identity-propositionality predicate, with only `UU` renamed to `Type`. The general universe of truncated types belongs in Definition 12.4.1. |
| Example 12.3.2 | The verbatim induction proving `is-prop-Eq-ℕ`, followed by the explicitly typed specialization of `is-prop-is-equiv` to Theorem 11.3.1's equality-code equivalence. This follows the book's proof without using the later relation criterion. |
| Proposition 12.3.3 | The type-specific `instance-axiom-K` and both implication functions. The source's converse uses path induction with the explicit K hypothesis instead of the book's concatenation-cancellation presentation. No global K witness, postulate, or compiler-option change is introduced. |
| Theorem 12.3.4 | The pinned based and binary relation proofs, including total-space contraction and `is-set-prop-in-id`. The separate `is-equiv-id-in-prop` specializes the existing fundamental theorem to that contraction for an arbitrary family `(f : (x y : A) → x ＝ y → R x y)`. Equivalence of the chosen reverse map alone would not cover the statement. |
| Theorem 12.3.5 | The unit/empty relation chosen by the equality decision, its propositionality and reflexivity, its map back to identity, and the application of Theorem 12.3.4. All three hypotheses of the relation criterion are supplied explicitly, matching the book's Hedberg proof. |

The based proof at Theorem 12.3.4 is a new empty training site on `main`.
Its general retract fundamental theorem belongs at Theorem 11.2.2, after
the existing variants; its total-map homotopy, identity, and composition
laws belong after `tot` at Definition 11.1.1. The existing earlier
mathematical accounts pass on the proposal but remain deferred on main
through their recorded dependencies. Keep those earlier main files unchanged.
The exercise index and invisible-math record specify all source ranges,
local adaptations, dependency order, and later users. Published proposal
`b96fdf3` implements these placements, and passes candidate Sections
11.1--11.6 and 12.1--12.3 and aggregate Chapters 10--12. All 158 proposal
unit tests, repository checks, and whitespace checks pass. The generated
prose of the two changed earlier sections is unchanged; their comparison
checks remain 100%. Section 12.3 is deferred on `main`, never recorded
complete or passed. All 154 main unit tests, repository checks, and
whitespace checks pass. No exercise Agda or optional review evidence is changed.

## Section 12.4 (2026-09-07)

The seven numbered items and four proof bodies in `book/hierarchy.tex`,
lines 288--421, retain their complete prose. The introductory indexing
type and natural-number inclusion are curated before Definition 12.4.1.
The introduction's announced future identification with integers at least
-2 is not presented by the book as a theorem proved here.

| Item | Formalization and limits |
| --- | --- |
| Introduction | The inductive `𝕋`, common aliases, and pinned `truncation-level-ℕ`. Its two defining computations agree judgmentally with the book's inclusion after unfolding the shifted maps. |
| Definition 12.4.1 | Recursive `is-trunc`, the proper-successor predicate as a specialization of complements, the universe `Truncated-Type` and its projections, and `is-trunc-map` with its map bundle. |
| Remark 12.4.2 | The pinned lift and its equivalence, followed by both lifted truncation implications after Proposition 12.4.5. **Representation gap:** Agda's disjoint universes do not literally express the book's same type in two overlapping universes. Neither polymorphism nor the lifted analogue proves those judgmental base equalities. The original claim stays in the prose and the gap inventory. |
| Proposition 12.4.3 | The pinned base contraction and recursive successor proof. |
| Corollary 12.4.4 | Identity truncatedness as the preceding successor theorem. |
| Proposition 12.4.5 | Both map-level and bundled equivalence transfers. Upstream uses a broader retract induction, included as a labeled prerequisite; the book's equivalence-on-identities induction is retained, not claimed to be the copied proof. |
| Corollary 12.4.6 | Transfer along the equivalence on identities supplied by the embedding hypothesis. |
| Theorem 12.4.7 | Both pinned implications using the general and specialized fiber identity equivalences. Their single block is a new empty training site on main; the retained converse requires an absent specialization and transport equivalence at earlier mathematical homes. |

Exercise 12.8(a)'s identity-retract proof is needed by the section, so it
is added now and imports no Chapter 12 section. The proof of part (b)
appears at Proposition 12.4.5 to avoid a section/exercise import cycle;
there is no outstanding mathematical part-(b) proof to invent. The
exercise's pre-existing custom-list presentation drops its alphabetical
labels, as in Exercise 10.7, and remains an explicit presentation issue.
Corollary 12.4.4 also retains the existing tight inline QED spacing.
No complete-file or optional-review status is inferred from these blocks.

Main passes all 156 unit tests, repository checks, and whitespace checks;
Exercise 12.8(a) passes its ordinary Agda candidate check. Section 12.4
and Chapter 12 are deferred, never passed. Published shared-proposal
solution `31222b8` passes candidate Sections 11.6 and 12.4, Exercises
9.1 and 12.8, and aggregate Chapters 9--12; all 161 proposal unit tests
and repository checks pass. It supplies the transport equivalence at
Exercise 9.1 and the fiber specialization at Example 11.6.3, restoring
both later theorem implications without changing their code. The literal
overlapping-universe gap remains explicit on both branches.

The raw prose comparison is 98.26%, with 9/13 distinct
headings matching: its four unmatched headings are precisely the new,
explicit Agda headings. After removing only those headings and curated
Agda, a regression test confirms equality with the rendered book text,
including all item markers and thirteen displays, modulo whitespace.
The book itself has twelve heading occurrences, nine distinct. There are
no unresolved references or raw TeX commands. No review data is changed.
Section 11.6's unchanged prose still compares at 100%.

## Section 13.1 (2026-09-07)

All seven numbered items and three full proof bodies in `book/funext.tex`,
lines 28--152, are preserved. Twenty provenance-backed blocks account for
the mathematics; the inference-rule remark needs no second declaration.

| Item | Formalization |
| --- | --- |
| Proposition 13.1.1 | `htpy-eq` with its reflexivity computation, instance and based extensionality predicates, evaluation at the reflexivity homotopy, and the homotopy-induction predicate. Four explicitly typed applications of the existing fundamental-theorem and identity-system proofs give (i) iff (ii) iff (iii). These are implications, not an equivalence between the types of proofs. |
| Theorem 13.1.2 | Fixed-universe extensionality and weak-extensionality predicates and both pinned implication proofs. The weak-to-strong proof retains the two maps of the section-retraction pair and its identity homotopy. Both implications use their hypotheses, before any global axiom is in scope. The two-level version specializes to the book's single universe. |
| Axiom 13.1.3 | The pinned coherent-inverse presentation: `eq-htpy`, its section and retraction homotopies, and their coherence are explicitly postulated. `funext` and the two equivalence bundles are consequences of those assumptions, not a proof of function extensionality. Proposition 9.2.7 and Lemma 10.4.5 relate this chosen coherent-inverse presentation to the book's equivalence formulation. |
| Remark 13.1.4 | The full contextual inference rule is retained as a faithful proof-tree draft. Its mathematical content is the preceding context-polymorphic assumption, so no separate Agda declaration or extra axiom is added. |
| Theorem 13.1.5 | The contractible-dependent-product base case, induction on truncation level using `funext` and Section 12.4's equivalence invariance, and the needed proposition-valued specialization. |
| Corollary 13.1.6 | Both the general truncation result and the proposition specialization for constant families. |
| Remark 13.1.7 | `is-prop-neg`, by functions into the empty proposition. This proof uses function extensionality; the prose observation about needing the axiom is not presented as a formal independence theorem. |

The pinned `homotopy-induction` implication from based extensionality uses
the global `is-torsorial-htpy`, ignoring its explicit hypothesis. Importing
that proof would assume the conclusion before Axiom 13.1.3. Instead, the
four typed specializations use the already curated hypothesis-parametric
Theorem 11.2.2. No new general proof or earlier auxiliary is invented.
The `ev a` in `htpy-eq` is definitionally expanded to `(λ h → h a)` using
the pinned evaluation definition; complete Section 2.2 is not enlarged.
The book's incomplete binder `f,g:Π(x:A)` in the prose of Theorem 13.1.5
is retained as written; the Agda statement includes the codomain `B x`.

The raw comparison is 99.57%, with 9/10 distinct headings: the only added
heading labels the assumed coherent-inverse presentation. Removing that
heading and curated Agda gives exactly the rendered book text, modulo
whitespace, as a regression test checks. The book has eleven heading
occurrences and thirteen text fences, including its inference rule.
The labelled retraction arrows now render as `⟶[i]` and `⟶[r]`, and
the rule's type judgment renders `type`, using `book/hott.tex` line 212.
No unresolved references or raw TeX commands remain in this section.

Those converter rules regenerated thirteen affected sections: 1.1--1.4,
2.1--2.2, 3.1--3.2, 5.1, 6.1--6.2, 13.1, and 14.2. Regeneration also
refreshes the existing item-end boundaries, notably in Section 2.2;
all pre-existing Agda code and its order remain byte-identical. All
thirteen candidate checks and aggregate Chapters 1--6 and 13--14 passed
after the prose repair, before new Section 13.1 Agda was inserted.
That earlier empty-section check is not evidence for the new mathematics.

Main passes all 160 unit tests, repository checks (534 verified blocks),
and whitespace checks. The new Section 13.1 and Chapter 13 are deferred on
main through existing training dependencies. Published proposal merge
`dc97e2f5941b950b2cfd3283794adee1278891b2` passes actual candidate checks
for Sections 2.2 and 13.1, aggregate Chapters 1--6 and 13--14, all 165
unit tests, repository checks (546 verified blocks), and whitespace checks.
The Section 2.2 merge was regenerated from the combined manifest and
preserves every proposal Agda block and its order byte-for-byte. Both
branches' regression tests were retained. No new training site, exercise
Agda, complete-file record, or review decision is added.

## Section 13.2 (2026-09-07)

The four numbered items, three complete proofs, and intervening
products-of-fibers equivalence in `book/funext.tex`, lines 153--281, are
preserved. Seven section blocks and the one needed Exercise 9.5(b) block
carry full pinned provenance.

| Item | Formalization |
| --- | --- |
| Theorem 13.2.1 | Both choice types, both maps, both inverse homotopies, and both equivalence bundles. The Agda record-Σ representation has judgmental η, so the pinned second homotopy is `refl`; this does not formalize the book's explicit assertion that its inductive Σ lacks this rule. The full book proof using function extensionality is retained. A visible heading and gap record mark the representation difference; the existing Section 4.6 record is unchanged. |
| Corollary 13.2.2 | The ordinary-function map, its equivalence proof, and equivalence bundle, specialized from choice. |
| Intervening display | `equiv-Π-fiber-section` is a typed specialization of choice to the family `f a ＝ b`. Its block follows that display, outside Corollary 13.2.2 and before Corollary 13.2.3, with an exact `after_text` anchor checked by regression. |
| Corollary 13.2.3 | The pinned three-equivalence calculation using choice on the base, the Exercise 9.5(b) right swap, and the existing Exercise 10.6 contractible-base law. The total reverse-homotopy space is contracted using inverse choice, products of contractible types, and `is-contr-Id'`. The alternative citation to Exercise 13.1 remains prose; that exercise is not needed or filled. |
| Theorem 13.2.4 | The pinned total-space contractibility proof, then a typed application of the existing identity-system/contractibility conversions at `f` and its pointwise reflexivity data. The declaration explicitly takes identity systems as hypotheses and returns the dependent-product identity system; it is not merely the intermediate contraction. |

Exercise 9.5 was previously uncurated, not an earlier complete file.
Only its exact part (b) is needed and added, with a labeled solution heading.
Part (a) and the existing loss of alphabetical problem labels in custom-list
rendering remain explicit gaps. No new training site or earlier complete
section enlargement is needed. Main still defers Section 13.2 through the
existing training dependencies.

Removing the two visible Agda headings and all code reproduces the rendered
book prose exactly modulo whitespace. Raw comparison is 99.21%, with 6/8
distinct headings, all 21 text fences, no unresolved references, and no raw
TeX commands. Regression tests check the complete prose, declaration scope,
the intervening display, full inverse data, and the remaining exercise gap.
Main passes all 162 unit tests, repository checks (542 verified blocks),
Exercise 9.5's candidate and aggregate Chapter 9, and whitespace checks.
Section 13.2 and aggregate Chapter 13 are deferred, not passed. Actual
proposal validation is pending. No review state or complete-file record is changed.
