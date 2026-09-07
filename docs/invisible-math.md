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

### Section 13.1: assumptions and pre-axiom equivalence proofs

No new absent auxiliary or training site is introduced. All source ranges
below are at `c85d7fb834778f96a66576318cdc4ef3d4b80a26`, with hashes in
`data/agda-blocks-chapter-13.json`.

- `foundation/function-extensionality-axiom`, lines 63--71, defines
  `htpy-eq`. Expand `ev a` using `foundation/evaluation-functions`, lines
  31--36, instead of enlarging complete Section 2.2. Its instance and
  based predicates (85--90 and 104--110) belong at Proposition 13.1.1;
  its fixed-universe predicate (116--119) belongs at Theorem 13.1.2.
- The hypothesis-parametric fundamental theorem (56--75 of
  `foundation/fundamental-theorem-of-identity-types`) specializes to the
  function space and homotopy family for (i) iff (ii). The local
  identity-system proof from the singleton-induction package (77--82 of
  `foundation/singleton-induction`) gives (ii) to (iii), and
  `foundation/identity-systems`, lines 109--114, gives its converse.
  These typed applications reuse the Section 11.2 declarations; they do
  not copy `homotopy-induction`'s globally assumed contraction.
- `foundation/homotopy-induction`, lines 41--48 and 62--66, supplies
  evaluation and the induction predicate. Its later implication from
  based extensionality calls the global `is-torsorial-htpy` despite
  taking a hypothesis. That is not suitable before the book's axiom.
- `foundation/weak-function-extensionality`, lines 43--54 and 79--106,
  supplies the predicates and both implications with explicit hypotheses.
  Rename `map-inv-is-equiv` to `map-section-is-equiv` and
  `is-torsorial-Id` to `is-contr-Id`. Keep the entire retract, including
  its `eq-pair-eq-fiber refl` identity homotopy, in the later theorem's
  own proof rather than moving the choice equivalence ahead of Section 13.2.
- At Axiom 13.1.3 only, copy `foundation/function-extensionality`, lines
  76--96: the inverse map, two inverse homotopies, and coherence are
  postulates. Their derived `funext` is not a proof of the axiom. The
  pinned inverse presentation and the book's equivalence formulation are
  related by the already available invertibility/coherence results in
  Chapters 9--10. The bundles and computations (98--122) follow here;
  rename the local retraction-of-section theorem, but retain the proof.
- `foundation/dependent-products-contractible-types`, lines 33--39,
  and `foundation/dependent-products-truncated-types`, lines 45--53,
  supply Theorem 13.1.5's base and induction. The ordinary function
  corollary is at lines 97--102 of the latter. The required proposition
  specializations are at lines 33--39 and 88--92 of
  `foundation/dependent-products-propositions`, and `is-prop-neg` is at
  lines 38--39 of `foundation/negation`.

No `postulate` or global `funext` declaration occurs before Axiom 13.1.3.
The regression test checks this boundary, the four implication functions,
the actual use of both weak-extensionality hypotheses, and the later
induction order. Remark 13.1.4's rule is represented by the contextual
postulates, not by a new redundant assumption.

Published proposal merge `dc97e2f5941b950b2cfd3283794adee1278891b2`
validates this section against the existing auxiliaries without adding
any new one. Section 13.1 and aggregate Chapter 13 pass actual Agda;
main retains its conservative training-dependency deferral.

### Section 13.2: dependent choice and projection sections

All ranges below are at `c85d7fb834778f96a66576318cdc4ef3d4b80a26`;
the eight new records in `data/agda-blocks-chapter-13.json` carry hashes.

- `foundation-core/type-theoretic-principle-of-choice`, lines 40--49
  and 73--115, supplies the explicit-function types, maps, both inverse
  homotopies, and both bundles at Theorem 13.2.1. Lines 177--191 give
  Corollary 13.2.2. The intervening products-of-fibers/sections equivalence
  is the typed specialization to `C b a = (f a ＝ b)`; local `fiber` and
  `section` expand to its two sides. No new general proof is added.
- Both pinned and local Section 4.6 Σ types are records with judgmental η.
  The book explicitly uses inductive Σ without that rule. Retain the
  book's full function-extensionality proof, label the shorter pinned
  record proof, and retain the representation gap in `data/agda-gaps.json`.
  Do not change the earlier Σ representation to make the proofs look alike.
- `foundation/type-arithmetic-dependent-pair-types`, lines 377--408,
  supplies the exact right-swap content of Exercise 9.5(b). This is its
  natural, explicitly cited mathematical home, and the exercise was
  previously uncurated. Its earlier placement introduces no import cycle.
  Part (a) is not needed and remains unfilled.
- `foundation/sections`, lines 135--148, supplies the three composed
  equivalences at Corollary 13.2.3. Rename `is-torsorial-Id'` to the local
  `is-contr-Id'`; use the existing Section 11.1 base-change equivalence,
  Exercise 10.3 contractibility transfer, and Exercise 10.6 contractible-base
  law. The reverse total-homotopy contraction is already in this pinned
  proof; the alternative Exercise 13.1 is not needed.
- `foundation/equality-dependent-function-types`, lines 38--48,
  supplies Theorem 13.2.4's contraction. Expand `is-torsorial` to its local
  dependent-sum contractibility. The final typed application uses the
  existing Theorem 11.2.2 identity-system conversions, from
  `foundation/singleton-induction`, lines 77--82, and
  `foundation/identity-systems`, lines 109--114, to expose the exact
  identity-system hypothesis and conclusion.

No new absent auxiliary at an earlier complete site is found. The section
still has the existing transitive training dependencies; its ordinary
main check is deferred. Published proposal
`161b3c1b0b270cbcd06a4a60513271df4690f969` passes Section 13.2, Exercise
9.5, and aggregate Chapters 9 and 13. The candidate check exposed one
missing direct import: equivalence composition already lives in Exercise
9.4. That import was validated through a passing scratchpad, with every
proof body unchanged, and the focused correction was carried to main.

### Section 13.3: universal properties by induction

No new absent auxiliary is needed. All five new records use pinned commit
`c85d7fb834778f96a66576318cdc4ef3d4b80a26`, with hashes in the Chapter 13
manifest.

- `foundation/universal-property-dependent-pair-types`, lines 32--49,
  supplies the full forward evaluation equivalence at Theorem 13.3.1.
  Replace `UU` by `Type`; omit only the separate `is-equiv-ind-Σ`
  declaration. The two inverse maps, reflexivity computation, and explicit
  function-extensionality/Σ-induction homotopy remain intact. Local
  `ev-pair` already belongs at Remark 4.6.3, and `ind-Σ` at Definition
  4.6.1; neither earlier account is enlarged.
- The introductory ordinary Σ universal property and Corollary 13.3.2
  are typed specializations of that same proof and bundle. First make
  only the result family constant; then also make the input family
  constant for the product corollary. The direction remains evaluation
  on pairs, as in the book.
- `foundation/universal-property-identity-types`, lines 52--79, supplies
  Theorem 13.3.3: `ev-refl`, both inverse homotopies, equivalence proof,
  and bundle. Replace only `UU` by `Type`. Keep both nested `eq-htpy`
  applications and the exact path-induction body. The local `ind-Id`,
  `is-section`, and `is-retraction` already have the required signatures.
  No postulate or later univalence argument is brought into this section.
- The ordinary type-theoretic Yoneda statement from the introduction
  specializes the result family to be independent of its path argument.
  Both introductory specializations follow the general proofs they use,
  with visible headings recording this dependency-order choice.

The imports of Section 13.1 retain conservative transitive training
deferral on main. Published proposal merge
`6c408d4247f512bc7ce8cfbafbd4b11edce697b8` passes Section 13.3 and
aggregate Chapter 13 with these exact five blocks. All 168 tests and
repository checks pass. No additional mathematical auxiliary or exercise
solution was needed; no earlier complete file was enlarged.

### Section 13.4: precomposition characterizes equivalences

No new auxiliary mathematics is absent. All eleven new blocks cite pinned
commit `c85d7fb834778f96a66576318cdc4ef3d4b80a26`, with inclusive source
ranges and hashes in the Chapter 13 manifest.

- The dependent and ordinary precomposition maps first occur in Theorem
  13.4.1. Copy `foundation-core/precomposition-dependent-functions`, lines
  35--40, and `foundation-core/precomposition-functions`, lines 33--38,
  there; do not enlarge the earlier complete function-type account.
- `foundation/dependent-universal-property-equivalences`, lines 48--54,
  62--79, 85--95, and 116--120, supplies the dependent condition, full
  coherent-inverse/transport proof, implication from equivalence, and
  bundle. Replace `UU`/`UUω` by `Type`/`Typeω`. The existing local
  `is-coherently-invertible-is-invertible (is-invertible-is-equiv H)`
  applies Lemma 10.4.5 to the explicit hypothesis; no path-split machinery
  is needed. That lemma remains an existing training dependency on main.
- The apparent transport gap is only an absent wrapper name.
  `foundation-core/transport-along-identifications`, lines 87--91,
  defines `substitution-law-tr B f p {x'} = tr-ap f (λ _ → id) p x'`.
  Its SHA256 is
  `7797856fc5326bea4d72b58fc0a7c4ba6e56480bc1d099ad80db52b2c59a0b6c`.
  The general result already lives in Section 9.3's transport-action
  block, from the same source's lines 51--56. Instantiate it in the new
  proof at `x' = s (g (f x))`. The substitution identity's natural
  subject is transport as in Section 5.4, but it is already supplied by
  this existing theorem: neither Section 5.4 nor Section 9.3 is enlarged,
  and no artificial training exercise is created.
- `foundation/universal-property-equivalences`, lines 36--41, 51--56,
  62--85, and 110--116, supplies the ordinary condition, constant-family
  implication, ordinary bundle, and dependent converse by composition.
- The full ordinary converse is
  `foundation/precomposition-functions-into-subuniverses`, lines 49--84.
  Remove only the structured-type predicate and parameters, use ordinary
  A and B and `H : universal-property-equiv f`, and strip the declaration
  suffix. This is the specialization in
  `foundation/universal-property-equivalences`, lines 91--104 (secondary
  hash recorded in the manifest). Keep the inverse and both homotopies,
  using the two fibers at id and f. Existing Section 10.1 supplies
  `center` and `eq-is-contr'`; Section 10.4 supplies contractible fibers
  of equivalences. No later subuniverse theory is imported.

The entire section and aggregate Chapter 13 defer on main. Published
proposal merge `b42184ff92633edf5d9dd24eebc5a0b79babd86b` passes actual
Agda for Section 13.4 and aggregate Chapter 13, all 169 tests, repository
checks, and whitespace checks. No code correction, new training solution,
or earlier complete-file enlargement was needed.
