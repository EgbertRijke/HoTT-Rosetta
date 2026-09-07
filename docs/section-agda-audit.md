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
| Theorem 11.4.2 | Empty training block on `main`: specialize the pinned contractible-fiber embedding criterion using Theorem 10.4.6; it needs the missing equivalence between ordinary and reverse fibers. The packaged `is-emb-equiv` and `emb-equiv` are retained downstream. |

The auxiliary belongs at Definition 10.3.1, but complete Section 10.3 must
remain unchanged on `main`. The exercise index and invisible-math record
describe the proposal placement. No direct coherent-inverse proof or new
unproven assumption is substituted. Section 11.4 and Chapter 11 are deferred
on `main`, and no Chapter 11 section is marked complete. Proposal publication
and actual typechecking of this new exercise are pending.
