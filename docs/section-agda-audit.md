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
