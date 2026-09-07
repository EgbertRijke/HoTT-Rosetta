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
