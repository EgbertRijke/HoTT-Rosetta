# Invisible mathematics

This file records the mathematics behind each empty auxiliary Agda block.

For each exercise, record:

- the same stable name used in `docs/agda-training-exercises.md`;
- each needed definition or lemma;
- its mathematical role;
- the book item where it most naturally belongs;
- its dependency order;
- its pinned agda-unimath commit, file, and lines;
- any necessary change of notation;
- every later use.

Record all non-obvious decomposition choices. Keep the explanation short.

## Entries

### Section 10.2: evaluation at a point

- **Exercise:** `definition-10.2.1-singleton-induction`.
- **Needed result:**
  `ev-point a : ((x : A) → P x) → P a`.
- **Role:** It defines the evaluation map whose section expresses singleton
  induction.
- **Natural home:** Remark 2.2.2, which presents function evaluation.
- **Order:** Define `ev-point` before `is-singleton`.
- **Source:** Commit `c85d7fb834778f96a66576318cdc4ef3d4b80a26`,
  `src/foundation-core/function-types.lagda.md`, lines 48--50.
- **Notation:** Replace `UU` by `Type`.
- **Uses:** Definition 10.2.1, Example 10.2.2, Theorem 10.2.3, and the
  identity-system implication of Theorem 11.2.2; through it, Sections 11.3--11.5.

On the proposal, restore the retained Definition 10.2.1 block after adding
evaluation at Remark 2.2.2. Its source is
`src/foundation/singleton-induction.lagda.md`, lines 39--52, at the same
commit. The example uses the analogous singleton witness at lines 103--108:
replace the total path space and its eliminator by `unit`, `star`, and the
already available `ind-unit`. The computation witness remains `refl-htpy`.
No new dependency from Section 2.2 to singleton induction is introduced.

Section 2.2 already typechecks and tells a complete story. Do not add
`ev-point` there solely to make Section 10.2 compile. Section 10.2 is the
training exercise because the need arises there.

### Lemma 10.4.5: coherent inverse

- **Exercise:** `lemma-10.4.5-coherent-inverse`.
- **Goal:** Construct a coherent inverse from a two-sided inverse.
- **Main source:** Commit `c85d7fb`,
  `src/foundation-core/coherently-invertible-maps.lagda.md`, lines 464--524.
- **Later use:** Theorem 10.4.6; its contractible-fiber result is used by
  Theorem 11.1.3 and Lemma 11.1.4, then Theorem 11.1.6 and Sections 11.2--11.5.

Required mathematics, in dependency order:

1. **Cancellation of concatenation.** Natural home: Definition 5.2.5, after
   the inverse laws. Source: `src/foundation-core/identity-types.lagda.md`,
   lines 507--517.
2. **Right whiskering of path identifications.** Natural home: Definition
   5.3.1, where action on paths is introduced. Source:
   `src/foundation-core/whiskering-identifications-concatenation.lagda.md`,
   lines 78--83.
3. **Transposing concatenated homotopies.** Natural home: Proposition 9.1.6,
   after the groupoid laws for homotopies. Source:
   `src/foundation-core/homotopies.lagda.md`, lines 153--163.
4. **Whiskering concatenated homotopies.** Natural home: Proposition 9.1.6.
   Source: `src/foundation-core/whiskering-homotopies-concatenation.lagda.md`,
   lines 79--85.
5. **Composition and left whiskering.** Natural home: Definition 9.1.7,
   where whiskering is introduced. Source:
   `src/foundation/whiskering-homotopies-composition.lagda.md`, lines 269--285.
6. **Left whiskering of higher homotopies.** Natural home: Definition 9.1.7.
   Source: `src/foundation/whiskering-higher-homotopies-composition.lagda.md`,
   lines 62--69.
7. **Coherence of a homotopy to the identity.** Natural home: Definition
   10.4.4, after its naturality formula. Source:
   `src/foundation/whiskering-homotopies-composition.lagda.md`, lines 310--318.

All sources use commit `c85d7fb`. Replace `UU` by `Type`. The first result is
needed by the seventh. The second is needed by the fourth. Results 3--7 are
needed by the proof of Lemma 10.4.5.

### Theorem 11.4.2: reversing fiber paths

- **Exercise:** `theorem-11.4.2-equivalences-are-embeddings`.
- **Needed result:** `equiv-fiber : fiber f y ≃ fiber' f y`, including its
  two maps, their section and retraction homotopies, and the equivalence proof.
- **Role:** Convert contractibility of the ordinary fiber at `f a` into
  contractibility of `Σ A (λ x → f a ＝ f x)`, then apply Theorem 11.2.2 to
  `ap f`. The underlying maps preserve the first coordinate and invert the
  path. Their inverse laws are copied path-induction proofs.
- **Natural home:** Definition 10.3.1, immediately after the existing ordinary
  and reverse fiber definitions. Section 10.3 is already complete, so this
  addition belongs only on the shared proposal.
- **Source:** Commit `c85d7fb834778f96a66576318cdc4ef3d4b80a26`,
  `src/foundation-core/fibers-of-maps.lagda.md`, lines 215--244.
- **Notation:** Replace `UU` by `Type`; all other declarations are unchanged.
- **Order:** Section 5.2 supplies path inversion, Section 9.2 supplies
  equivalence construction, and Definition 10.3.1 supplies the two fiber
  types. Add the auxiliary there before any Section 11.4 consumer.
- **Uses:** Theorem 11.4.2's `is-emb-is-equiv`, then `is-emb-equiv` and
  `emb-equiv`. Recheck Section 10.3, Sections 11.1--11.4, and Chapters 10--11.

The retained theorem excerpt comes from `src/foundation/embeddings.lagda.md`,
lines 431--448 at the same commit. Its contractible-ordinary-fiber argument
is specialized using `is-contr-map-is-equiv H (f a)`, already proved in
Theorem 10.4.6. This keeps the book's fundamental-theorem proof route; the
alternative coherent-inverse proof in `foundation-core/equivalences` is not
used. The auxiliary fiber equivalence is proved directly by path inversion
rather than by a separate appeal to Exercise 9.1 and `equiv-tot`.

Published proposal `63e5e49` places the whole 215--244 excerpt in
`definition-10.3.1-fiber-orientation-equivalence`, after the existing fiber
types and before the item's closing marker. It adds no imports and no
Chapter 11 dependency to Section 10.3. The stored Theorem 11.4.2 block is
restored without changing its specialized proof. A regression test checks
this placement and the transition prose boundary. Section 10.3, Sections
11.1--11.4, and Chapters 10--11 pass ordinary Agda checks there.

### Example 11.6.3: identities in fibers

- **Exercise:** `example-11.6.3-identities-in-fibers`.
- **Source commit:** `c85d7fb834778f96a66576318cdc4ef3d4b80a26` for every
  range below; full hashes are recorded with the curated blocks.
- **Needed involution:** `inv-inv`,
  `src/foundation-core/identity-types.lagda.md`, lines 322--327.
  Its natural home is Definition 5.2.5, immediately after the inverse laws.
  Section 5.2 is complete, so add this only on the proposal.
- **Needed equivalences:** `is-equiv-inv` and `is-equiv-concat`, with their
  explicit inverses, from `src/foundation/identity-types.lagda.md`, lines
  80--119. Their natural home is Exercise 9.1, which asks for these exact
  equivalences. Only the section-required inversion and left-concatenation
  parts are in scope; right concatenation and transport remain gaps.
- **Inverse data for concatenation:** `inv-concat` and its two homotopies,
  `src/foundation-core/identity-types.lagda.md`, lines 212--217 and 367--377.
  Place these with Exercise 9.1's explicitly requested inverse data, before
  its equivalence proof. They use only the existing groupoid operations.
- **Order and uses:** `inv-inv` in Section 5.2 precedes the Exercise 9.1
  inversion equivalence. Both Exercise 9.1 equivalences are needed by the
  fiberwise map in Example 11.6.3; its total map and commuting triangle then
  give the claimed equivalence of identity types with fibers of `ap f`.
- **Retained example:** `src/foundation/equality-fibers-of-maps.lagda.md`,
  lines 47--97. Preserve its map, triangle, and equivalence proof, replacing
  `UU` by repository-local `Type`. This proof uses Theorem 9.3.4 and the
  total-map criterion of Theorem 11.1.3, rather than the book's direct
  structure-identity-principle contraction argument; the claim is the same.

Theorem 11.6.2 does not require adding a generic `is-contr-Σ` theorem to
complete Section 10.1. Its prose explicitly constructs a total-space
equivalence. The pinned interchange equivalence belongs in that proof, and
the contractible-base unit equivalence belongs in Exercise 10.6, which asks
for precisely that result. Compose them and specialize the already copied
contractibility transfers from Exercise 10.3 in both directions. This also
exposes the converse absent from the upstream structure-identity-principle
module. Exercise 10.6 and Section 11.6 extend the existing singleton-induction
exercise's later uses; the fundamental theorem extends the coherence
exercise's later uses. No new auxiliary contraction proof is invented.

Published proposal `6bd180b` implements these placements. Its regression
test verifies that the involution follows the inverse laws inside Definition
5.2.5 and that the equivalences remain at Exercise 9.1, not in the later
example. The unused right-concatenation and transport parts of Exercise 9.1
remain explicit gaps on that branch. Candidate Sections 5.2 and 11.6,
Exercises 9.1 and 10.6, and aggregate Chapters 5--11 pass ordinary Agda checks.

Section 12.1 uses the existing Theorem 11.4.2 solution in the proof that an
inhabited-contractible type embeds into the unit type. The pinned
`foundation/subterminal-types`, lines 48--86, provides the book's exact proof
route. Its point-assumption lemma, `foundation-core/embeddings` lines
126--132, belongs in the proof of Proposition 12.1.3, where the book states
that observation explicitly. Expand `terminal-map A` to `(λ (_ : A) → star)`
using `foundation/unit-type` lines 54--59 and `foundation-core/constant-maps`
lines 29--30; this avoids introducing a general API in an earlier complete
section. The required `is-prop-is-contr` is copied from
`foundation-core/contractible-types` lines 197--200 to the previously empty
Exercise 10.1, its exact book home. All ranges use the same pinned commit.
These choices add no new training exercise or function-extensionality axiom.
Proposal `0c3d8b1` validates Section 12.1, Exercise 10.1, and aggregate
Chapters 10--12 with these placements and the existing training solutions.

### Theorem 12.2.3: embeddings and propositional fibers

- **Exercise:** `theorem-12.2.3-embeddings-propositional-fibers`.
- **Needed result:** `equiv-fiber : fiber f y ≃ fiber' f y`, with the
  forward and inverse maps, section, retraction, and equivalence proof.
- **Source:** Commit `c85d7fb834778f96a66576318cdc4ef3d4b80a26`,
  `src/foundation-core/fibers-of-maps.lagda.md`, lines 215--244.
- **Natural home:** Definition 10.3.1, after the ordinary and reverse fiber
  definitions. Main's complete Section 10.3 stays unchanged. Proposal
  `63e5e49` already provides this entire auxiliary for Theorem 11.4.2;
  reuse it without adding a duplicate or moving it beside the later theorem.
- **Role and order:** The fundamental theorem applies to the reverse fiber
  over `f x`. Transfer contractibility between it and the ordinary fiber;
  Proposition 12.1.3 converts inhabited contractibility into propositionality.
  In the converse direction, eliminate the fiber path by path induction.
- **Retained theorem:** `src/foundation-core/propositional-maps.lagda.md`,
  lines 81--105 at the same commit. Replace only `UU` by local `Type`.
- **Uses:** Both directions of Theorem 12.2.3, the embedding criterion for
  projections in Corollary 12.2.4, and its packaged equivalence on identities.
  Recheck Section 12.2 and aggregate Chapters 10--12 on the proposal.

Corollary 12.2.4 also needs `equiv-fiber-pr1` and its inverse data, from
`src/foundation-core/fibers-of-maps.lagda.md`, lines 250--290 at the same
commit. Exercise 10.7(a) asks for precisely this result and was previously
empty; add it there on both branches, without a Chapter 12 dependency.
Parts (b) and (c) are not section prerequisites and remain Agda gaps.
The unbundled forward implication simply applies the copied subtype-inclusion
embedding proof to `(λ x → (B x , H x))`; it does not invent a new proof.
No function-extensionality assumption or later truncation result is imported.

Published proposal `7b6b28c` restores the retained theorem with no new
auxiliary or proof changes. It reuses Definition 10.3.1's existing fiber
equivalence. Section 12.2, Exercise 10.7, and aggregate Chapters 10--12
pass ordinary Agda checks, as do all 156 proposal tests and repository
checks. Main keeps its complete Section 10.3 unchanged and the new theorem
site empty. Both implications and the later projection results are included
in the proposal's passing candidate check.

### Theorem 12.3.4: propositional identity relations

- **Exercise:** `theorem-12.3.4-propositional-identity-relation`.
- **Source commit:** `c85d7fb834778f96a66576318cdc4ef3d4b80a26` for all
  ranges below; each curated block records its inclusive-range SHA-256.
- **Total-map laws:** `tot-htpy`, `tot-id`, and `preserves-comp-tot`, from
  `src/foundation-core/functoriality-dependent-pair-types.lagda.md`, lines
  110--113, 119--122, and 128--133. Their natural home is Definition 11.1.1,
  immediately after `tot`. The homotopy law uses the already available
  `eq-pair-eq-fiber` from Theorem 9.3.4; import that local section.
- **Retract fundamental theorem:** `fundamental-theorem-id-retraction`,
  `src/foundation/fundamental-theorem-of-identity-types.lagda.md`, lines
  105--126. Its natural home is Theorem 11.2.2 after the existing variants.
  The three laws above assemble the retraction on total spaces. Exercise
  10.2 transfers contractibility from the total identity space, after which
  the existing total-map criterion proves the fiberwise equivalence.
- **Notation:** Replace `UU` by `Type`, `id' (Σ A B)` by
  `id {A = Σ A B}`, and `is-torsorial-Id` by the local `is-contr-Id`.
  The first identity-map replacement only makes the same type argument
  implicit; the pinned definitions are `foundation-core/function-types`,
  lines 24--28. Do not introduce a new identity-map API in Section 2.2.
- **Retained later proof:** `src/foundation-core/sets.lagda.md`, lines
  115--137. Expand `is-torsorial R` to `is-contr (Σ A R)` and use the local
  `map-section-is-equiv` and `is-equiv-map-section-is-equiv` names. The
  binary criterion is at lines 141--154. The arbitrary-map conclusion is
  an explicitly typed specialization of the existing fundamental theorem
  to the copied total-space contraction, not a new proof.
- **Order and uses:** The total-map laws precede the retract variant; both
  precede Theorem 12.3.4, which precedes Hedberg's Theorem 12.3.5. Recheck
  Sections 11.1--11.6 and 12.1--12.3 and aggregate Chapters 10--12 on the
  proposal. Keep the earlier main files unchanged.

The natural-number example does not require moving the later relation
criterion ahead of its narrative home. Copy `is-prop-Eq-ℕ` from
`elementary-number-theory/equality-natural-numbers`, lines 61--67, then
specialize the already copied `is-prop-is-equiv` to Theorem 11.3.1's
`is-equiv-Eq-eq-ℕ`. This is exactly the book's equality-code proof route.
The axiom-K characterization keeps the source's explicit hypothesis and
both implications; it adds no postulate or global K assumption. The source's
converse uses path induction with K rather than the book's cancellation
presentation. All original proof prose remains intact.

Published proposal `b96fdf3` implements these placements and restores the
retained based proof without changing its code. Its regression tests check
all four auxiliary placements, declaration order, absence of Chapter 12
imports in the earlier modules, and the arbitrary-map conclusion in the
later theorem. Candidate Sections 11.1--11.6 and 12.1--12.3 and aggregate
Chapters 10--12 pass ordinary Agda checks, as do all 158 proposal unit tests
and repository checks. Main retains the empty site and its earlier files
unchanged; no completeness or review state is inferred from deferred checks.

### Theorem 12.4.7: truncated action on identities

- **Exercise:** `theorem-12.4.7-truncated-action-on-identities`.
- **Pinned commit:** `c85d7fb834778f96a66576318cdc4ef3d4b80a26` throughout.
- **Transport equivalence:** `src/foundation/transport-along-identifications.lagda.md`,
  lines 42--70, gives `is-equiv-tr`, both inverse-transport homotopies,
  the inverse equivalence, and the two equivalence bundles.
  Exercise 9.1 explicitly requests this equivalence and its inverse;
  use that exact home, refining the initially suggested Example 9.2.3.
  Replace `UU` by `Type` and expand `inv-tr B p` to `tr B (inv p)` using
  `src/foundation-core/transport-along-identifications.lagda.md`, lines
  42--43. Import local Section 5.4; do not enlarge complete Section 5.4.
- **Specialized fiber equivalence:**
  `src/foundation/equality-fibers-of-maps.lagda.md`, lines 113--130,
  gives `eq-fiber-fiber-ap` and `is-equiv-eq-fiber-fiber-ap`. Put them
  after the existing general fiber identity equivalence at Example 11.6.3.
  Replace only `UU` by `Type`. The extra transport along `right-unit`
  changes the fiber target from `q ∙ refl` to `q`; it must not be erased
  as a judgmental equality. The equivalence proof uses Exercise 9.4's
  existing composition theorem and the new transport equivalence.
- **Retained later theorem:**
  `src/foundation-core/truncated-maps.lagda.md`, lines 112--133.
  Both implications are retained together in the empty main block.
  The first uses Example 11.6.3's existing general equivalence, and the
  converse uses the specialized one above. Replace only `UU` by `Type`.
- **Order and validation:** Transport equivalence precedes the fiber
  specialization, which precedes the truncation theorem. Check changed
  Sections 11.6 and 12.4, Exercise 9.1, and aggregate Chapters 9--12 on the proposal.
  Main's earlier modules remain unchanged; preserve reserved manual reviews.

Proposition 12.4.5 uses the pinned retract induction in
`foundation-core/truncated-types`, lines 117--126, followed by its
equivalence transfers at lines 132--161. The needed identity retraction
belongs at the previously empty Exercise 12.8(a): copy
`foundation-core/retractions`, lines 77--110, then
`foundation-core/retracts-of-types`, lines 129--136. Expand the latter's
two retract projections to `pr1 R` and `pr2 R`; their definitions are in
the same file, lines 66--70. This avoids enlarging Definition 9.2.1.
The truncation-of-retracts theorem also proves Exercise 12.8(b), but must
remain beside Proposition 12.4.5 as a labeled upstream prerequisite to
avoid the cycle through the exercise module and this section's `is-trunc`.
The book's original equivalence-on-identities induction stays in the prose.

Remark 12.4.2 requires a separate universe interpretation: pinned
`foundation-core/raising-universe-levels`, lines 26--28, says Agda universes
do not overlap. Its `raise` (33--34) and `compute-raise` proof (45--67)
provide equivalent lifted types. After Proposition 12.4.5, specialize both
copied equivalence-transfer directions to `compute-raise l A`. Those
typed applications prove lifted truncation invariance without function
extensionality or a universe axiom. They do not prove the book's literal
same-type-in-two-universes assertion; its representation gap is explicit.
The proper-successor-type predicate is a typed specialization of
`foundation/complements`, lines 25--27, to the constant family of
`is-trunc k A` over `is-trunc (succ-𝕋 k) A`, not a new proof.

Published proposal `31222b8` implements the two auxiliary placements and
restores Theorem 12.4.7 unchanged. It passes candidate Sections 11.6 and
12.4, Exercises 9.1 and 12.8, and aggregate Chapters 9--12. All 161
proposal unit tests and repository checks pass. Its Exercise 9.1 gap now
names only right concatenation; the needed transport assertion is supplied.
Main keeps its earlier files and all seven training sites unchanged and
empty. No Section 9.2 code or reserved manual-review data is changed.
