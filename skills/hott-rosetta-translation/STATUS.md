# HoTT-Rosetta Translation Status

This status was prepared from the current repository contents.
The source inventory follows `book/hott-intro.tex` and the uncommented `\input` chain in the chapter source files.

Current totals:

- Chapter files: 14/22 created
- Section files: 62/98 created
- Exercise files: 118/216 created

## Summary By Source

| No. | Title | Source | Chapter | Sections | Exercises |
| --- | --- | --- | --- | ---: | ---: |
| 1 | Dependent type theory | `book/dtt.tex` | created | 4/4 | 0/1 |
| 2 | Dependent function types | `book/pi.tex` | created | 2/2 | 1/4 |
| 3 | The natural numbers | `book/nat.tex` | created | 3/3 | 6/6 |
| 4 | More inductive types | `book/inductive.tex` | created | 6/6 | 3/4 |
| 5 | Identity types | `book/identity.tex` | created | 6/6 | 8/8 |
| 6 | Universes | `book/universes.tex` | created | 4/4 | 6/6 |
| 7 | Modular arithmetic via the Curry-Howard interpretation | `book/modular-arithmetic.tex` | created | 5/5 | 10/10 |
| 8 | Decidability in elementary number theory | `book/number-theory.tex` | created | 6/6 | 15/15 |
| 9 | Equivalences | `book/equivalences.tex` | created | 3/3 | 9/9 |
| 10 | Contractible types and contractible maps | `book/contractible.tex` | created | 4/4 | 8/8 |
| 11 | The fundamental theorem of identity types | `book/fundamental.tex` | created | 6/6 | 11/11 |
| 12 | Propositions, sets, and the higher truncation levels | `book/hierarchy.tex` | created | 4/4 | 14/14 |
| 13 | Function extensionality | `book/funext.tex` | created | 5/5 | 18/18 |
| 14 | Propositional truncations | `book/propositional-truncation.tex` | created | 4/4 | 9/9 |
| 15 | Image factorizations | `book/images.tex` | missing | 0/3 | 0/5 |
| 16 | Finite types | `book/finite-types.tex` | missing | 0/3 | 0/11 |
| 17 | The univalence axiom | `book/univalence.tex` | missing | 0/6 | 0/20 |
| 18 | Set quotients | `book/set-quotients.tex` | missing | 0/5 | 0/14 |
| 19 | Groups in univalent mathematics | `book/groups.tex` | missing | 0/6 | 0/17 |
| 20 | General inductive types | `book/W-types.tex` | missing | 0/6 | 0/7 |
| 21 | The circle | `book/circle.tex` | missing | 0/3 | 0/8 |
| 22 | The universal cover of the circle | `book/circle-universal-cover.tex` | missing | 0/4 | 0/11 |

## Created Files

Chapter files:

- `src/chapter-1-dependent-type-theory.lagda.md`
- `src/chapter-2-dependent-function-types.lagda.md`
- `src/chapter-3-the-natural-numbers.lagda.md`
- `src/chapter-4-more-inductive-types.lagda.md`
- `src/chapter-5-identity-types.lagda.md`
- `src/chapter-6-universes.lagda.md`
- `src/chapter-7-modular-arithmetic-via-the-curry-howard-interpretation.lagda.md`
- `src/chapter-8-decidability-in-elementary-number-theory.lagda.md`
- `src/chapter-9-equivalences.lagda.md`
- `src/chapter-10-contractible-types-and-contractible-maps.lagda.md`
- `src/chapter-11-the-fundamental-theorem-of-identity-types.lagda.md`
- `src/chapter-12-propositions-sets-and-the-higher-truncation-levels.lagda.md`
- `src/chapter-13-function-extensionality.lagda.md`
- `src/chapter-14-propositional-truncations.lagda.md`

Section files:

- `src/section-1-1-judgments-and-contexts-in-type-theory.lagda.md`
- `src/section-1-2-type-families.lagda.md`
- `src/section-1-3-inference-rules.lagda.md`
- `src/section-1-4-derivations.lagda.md`
- `src/section-2-1-the-rules-for-dependent-function-types.lagda.md`
- `src/section-2-2-ordinary-function-types.lagda.md`
- `src/section-3-1-the-formal-specification-of-the-type-of-natural-numbers.lagda.md`
- `src/section-3-2-addition-on-the-natural-numbers.lagda.md`
- `src/section-3-3-pattern-matching.lagda.md`
- `src/section-4-1-the-idea-of-general-inductive-types.lagda.md`
- `src/section-4-2-the-unit-type.lagda.md`
- `src/section-4-3-the-empty-type.lagda.md`
- `src/section-4-4-coproducts.lagda.md`
- `src/section-4-5-the-type-of-integers.lagda.md`
- `src/section-4-6-dependent-pair-types.lagda.md`
- `src/section-5-1-the-inductive-definition-of-identity-types.lagda.md`
- `src/section-5-2-the-groupoidal-structure-of-types.lagda.md`
- `src/section-5-3-the-action-on-identifications-of-functions.lagda.md`
- `src/section-5-4-transport.lagda.md`
- `src/section-5-5-the-uniqueness-of-refl.lagda.md`
- `src/section-5-6-the-laws-of-addition-on-natural-numbers.lagda.md`
- `src/section-6-1-specification-of-type-theoretic-universes.lagda.md`
- `src/section-6-2-assuming-enough-universes.lagda.md`
- `src/section-6-3-observational-equality-of-the-natural-numbers.lagda.md`
- `src/section-6-4-peanos-seventh-and-eighth-axioms.lagda.md`
- `src/section-7-1-the-curry-howard-interpretation.lagda.md`
- `src/section-7-2-the-congruence-relations-on-natural-numbers.lagda.md`
- `src/section-7-3-the-standard-finite-types.lagda.md`
- `src/section-7-4-the-natural-numbers-modulo-k-plus-one.lagda.md`
- `src/section-7-5-the-cyclic-groups.lagda.md`
- `src/section-8-1-decidability-and-decidable-equality.lagda.md`
- `src/section-8-2-constructions-by-case-analysis.lagda.md`
- `src/section-8-3-the-well-ordering-principle-of-natural-numbers.lagda.md`
- `src/section-8-4-the-greatest-common-divisor.lagda.md`
- `src/section-8-5-the-infinitude-of-primes.lagda.md`
- `src/section-8-6-boolean-reflection.lagda.md`
- `src/section-9-1-homotopies.lagda.md`
- `src/section-9-2-bi-invertible-maps.lagda.md`
- `src/section-9-3-characterizing-the-identity-types-of-dependent-pair-types.lagda.md`
- `src/section-10-1-contractible-types.lagda.md`
- `src/section-10-2-singleton-induction.lagda.md`
- `src/section-10-3-contractible-maps.lagda.md`
- `src/section-10-4-equivalences-are-contractible-maps.lagda.md`
- `src/section-11-1-families-of-equivalences.lagda.md`
- `src/section-11-2-the-fundamental-theorem.lagda.md`
- `src/section-11-3-equality-on-the-natural-numbers.lagda.md`
- `src/section-11-4-embeddings.lagda.md`
- `src/section-11-5-disjointness-of-coproducts.lagda.md`
- `src/section-11-6-the-structure-identity-principle.lagda.md`
- `src/section-12-1-propositions.lagda.md`
- `src/section-12-2-subtypes.lagda.md`
- `src/section-12-3-sets.lagda.md`
- `src/section-12-4-general-truncation-levels.lagda.md`
- `src/section-13-1-equivalent-forms-of-function-extensionality.lagda.md`
- `src/section-13-2-identity-systems-on-pi-types.lagda.md`
- `src/section-13-3-universal-properties.lagda.md`
- `src/section-13-4-composing-with-equivalences.lagda.md`
- `src/section-13-5-the-strong-induction-principle-of-the-natural-numbers.lagda.md`
- `src/section-14-1-the-universal-property-of-propositional-truncations.lagda.md`
- `src/section-14-2-propositional-truncations-as-higher-inductive-types.lagda.md`
- `src/section-14-3-logic-in-type-theory.lagda.md`
- `src/section-14-4-mapping-propositional-truncations-into-sets.lagda.md`

Exercise files:

- `src/exercise-2-1-judgmental-extensionality.lagda.md`
- `src/exercise-3-1-multiplication-and-exponentiation.lagda.md`
- `src/exercise-3-2-min-and-max.lagda.md`
- `src/exercise-3-3-triangular-numbers-and-factorials.lagda.md`
- `src/exercise-3-4-binomial-coefficients.lagda.md`
- `src/exercise-3-5-fibonacci-sequence.lagda.md`
- `src/exercise-3-6-division-by-two.lagda.md`
- `src/exercise-4-2-boolean-operations.lagda.md`
- `src/exercise-4-3-negation.lagda.md`
- `src/exercise-4-4-lists.lagda.md`
- `src/exercise-5-1-distributive-inv-concat.lagda.md`
- `src/exercise-5-2-inverse-concatenation-maps.lagda.md`
- `src/exercise-5-3-lift.lagda.md`
- `src/exercise-5-4-mac-lane-pentagon.lagda.md`
- `src/exercise-5-5-semiring-laws-natural-numbers.lagda.md`
- `src/exercise-5-6-successor-predecessor-integers.lagda.md`
- `src/exercise-5-7-group-laws-integers.lagda.md`
- `src/exercise-5-8-ring-laws-integers.lagda.md`
- `src/exercise-6-1-injectivity-addition-multiplication.lagda.md`
- `src/exercise-6-2-observational-equality-booleans.lagda.md`
- `src/exercise-6-3-order-natural-numbers.lagda.md`
- `src/exercise-6-4-strict-order-natural-numbers.lagda.md`
- `src/exercise-6-5-distance-natural-numbers.lagda.md`
- `src/exercise-6-6-absolute-value-integers.lagda.md`
- `src/exercise-7-1-divisibility-three-for-two.lagda.md`
- `src/exercise-7-2-divisibility-poset.lagda.md`
- `src/exercise-7-3-divisibility-factorials.lagda.md`
- `src/exercise-7-4-successor-finite-types-addition.lagda.md`
- `src/exercise-7-5-observational-equality-finite-types.lagda.md`
- `src/exercise-7-6-predecessor-finite-types.lagda.md`
- `src/exercise-7-7-classical-finite-types.lagda.md`
- `src/exercise-7-8-ring-laws-finite-cyclic-types.lagda.md`
- `src/exercise-7-9-euclidean-division.lagda.md`
- `src/exercise-7-10-k-ary-natural-numbers.lagda.md`
- `src/exercise-8-1-open-number-theory-conjectures.lagda.md`
- `src/exercise-8-2-decidability-of-decidability.lagda.md`
- `src/exercise-8-3-finite-choice-decidable.lagda.md`
- `src/exercise-8-4-prime-and-prime-counting-functions.lagda.md`
- `src/exercise-8-5-characterization-prime.lagda.md`
- `src/exercise-8-6-decidable-equality-products.lagda.md`
- `src/exercise-8-7-decidable-equality-coproducts.lagda.md`
- `src/exercise-8-8-decidable-equality-sigma-types.lagda.md`
- `src/exercise-8-9-finite-dependent-products.lagda.md`
- `src/exercise-8-10-maximal-elements.lagda.md`
- `src/exercise-8-11-bezouts-identity.lagda.md`
- `src/exercise-8-12-prime-factorization.lagda.md`
- `src/exercise-8-13-primes-congruent-three-mod-four.lagda.md`
- `src/exercise-8-14-fields-integers-modulo-prime.lagda.md`
- `src/exercise-8-15-cofibonacci-sequence.lagda.md`
- `src/exercise-9-1-groupoid-operations-equivalences.lagda.md`
- `src/exercise-9-2-nonequivalences-booleans-natural-numbers.lagda.md`
- `src/exercise-9-3-homotopic-equivalences.lagda.md`
- `src/exercise-9-4-three-for-two-equivalences.lagda.md`
- `src/exercise-9-5-sigma-swap.lagda.md`
- `src/exercise-9-6-coproduct-functor-equivalences.lagda.md`
- `src/exercise-9-7-product-functor-equivalences.lagda.md`
- `src/exercise-9-8-finite-type-arithmetic-equivalences.lagda.md`
- `src/exercise-9-9-finitely-cyclic-maps.lagda.md`
- `src/exercise-10-1-identity-types-contractible.lagda.md`
- `src/exercise-10-2-contractible-retracts.lagda.md`
- `src/exercise-10-3-contractible-equivalences.lagda.md`
- `src/exercise-10-4-finite-types-not-contractible.lagda.md`
- `src/exercise-10-5-contractible-products.lagda.md`
- `src/exercise-10-6-dependent-pair-contractible-base.lagda.md`
- `src/exercise-10-7-fibers-of-projections.lagda.md`
- `src/exercise-10-8-fiber-replacement.lagda.md`
- `src/exercise-11-1-coproduct-embeddings.lagda.md`
- `src/exercise-11-2-paths-along-equivalences.lagda.md`
- `src/exercise-11-3-homotopic-embeddings.lagda.md`
- `src/exercise-11-4-embedding-triangles.lagda.md`
- `src/exercise-11-5-composite-embeddings-equivalences.lagda.md`
- `src/exercise-11-6-embeddings-from-coproducts.lagda.md`
- `src/exercise-11-7-coproduct-functor-reflection.lagda.md`
- `src/exercise-11-8-total-map-retractions.lagda.md`
- `src/exercise-11-9-embedding-from-path-sections.lagda.md`
- `src/exercise-11-10-path-split-maps.lagda.md`
- `src/exercise-11-11-fiber-triangles.lagda.md`
- `src/exercise-12-1-booleans-are-sets.lagda.md`
- `src/exercise-12-2-posets-are-sets.lagda.md`
- `src/exercise-12-3-injective-maps-into-sets.lagda.md`
- `src/exercise-12-4-coproduct-truncation.lagda.md`
- `src/exercise-12-5-diagonal.lagda.md`
- `src/exercise-12-6-truncated-sigma-types.lagda.md`
- `src/exercise-12-7-truncated-products.lagda.md`
- `src/exercise-12-8-retracts-of-truncated-types.lagda.md`
- `src/exercise-12-9-list-concatenation-truncated-map.lagda.md`
- `src/exercise-12-10-constant-maps-truncated.lagda.md`
- `src/exercise-12-11-truncated-maps-triangles.lagda.md`
- `src/exercise-12-12-total-maps-truncated.lagda.md`
- `src/exercise-12-13-fiber-inclusions-truncated.lagda.md`
- `src/exercise-12-14-isolated-elements.lagda.md`
- `src/exercise-13-1-homotopy-operations-equivalences.lagda.md`
- `src/exercise-13-2-identity-types-of-structured-function-types.lagda.md`
- `src/exercise-13-3-truncatedness-is-a-proposition.lagda.md`
- `src/exercise-13-4-equivalence-structure-is-a-proposition.lagda.md`
- `src/exercise-13-5-path-split-and-coherently-invertible-propositions.lagda.md`
- `src/exercise-13-6-universal-property-empty-types.lagda.md`
- `src/exercise-13-7-universal-property-contractible-types.lagda.md`
- `src/exercise-13-8-universal-property-coproducts.lagda.md`
- `src/exercise-13-9-uniqueness-of-identity-types.lagda.md`
- `src/exercise-13-10-universal-property-natural-numbers.lagda.md`
- `src/exercise-13-11-ordinal-induction-natural-numbers.lagda.md`
- `src/exercise-13-12-dependent-products-of-truncated-maps.lagda.md`
- `src/exercise-13-13-pi-types-distribute-over-coproducts.lagda.md`
- `src/exercise-13-14-section-retraction-triangles.lagda.md`
- `src/exercise-13-15-morphisms-over-a-type.lagda.md`
- `src/exercise-13-16-equivalences-and-isomorphisms-of-sets.lagda.md`
- `src/exercise-13-17-contractible-products-over-decidable-sets.lagda.md`
- `src/exercise-13-18-retracts-as-limits.lagda.md`
- `src/exercise-14-1-propositional-truncation-properties.lagda.md`
- `src/exercise-14-2-mere-equality.lagda.md`
- `src/exercise-14-3-products-of-propositional-truncations.lagda.md`
- `src/exercise-14-4-dependent-universal-property-truncations.lagda.md`
- `src/exercise-14-5-propositional-truncations-with-sections.lagda.md`
- `src/exercise-14-6-propositional-truncations-of-decidable-types.lagda.md`
- `src/exercise-14-7-precomposition-with-truncation.lagda.md`
- `src/exercise-14-8-impredicative-encodings.lagda.md`
- `src/exercise-14-9-interval.lagda.md`

## Missing Chapter Files

- `src/chapter-15-image-factorizations.lagda.md`
- `src/chapter-16-finite-types.lagda.md`
- `src/chapter-17-the-univalence-axiom.lagda.md`
- `src/chapter-18-set-quotients.lagda.md`
- `src/chapter-19-groups-in-univalent-mathematics.lagda.md`
- `src/chapter-20-general-inductive-types.lagda.md`
- `src/chapter-21-the-circle.lagda.md`
- `src/chapter-22-the-universal-cover-of-the-circle.lagda.md`

## Missing Section Files

These filenames are mechanically generated from the current source titles.
When a title contains mathematical notation, the final slug may need a small human adjustment to match nearby style.

Chapter 15:

- `src/section-15-1-the-image-of-a-map.lagda.md`
- `src/section-15-2-surjective-maps.lagda.md`
- `src/section-15-3-cantor-s-diagonal-argument.lagda.md`

Chapter 16:

- `src/section-16-1-counting-in-type-theory.lagda.md`
- `src/section-16-2-double-counting-in-type-theory.lagda.md`
- `src/section-16-3-finite-types.lagda.md`

Chapter 17:

- `src/section-17-1-equivalent-forms-of-the-univalence-axiom.lagda.md`
- `src/section-17-2-propositional-extensionality.lagda.md`
- `src/section-17-3-univalence-implies-function-extensionality.lagda.md`
- `src/section-17-4-maps-and-families-of-types.lagda.md`
- `src/section-17-5-classical-mathematics-with-the-univalence-axiom.lagda.md`
- `src/section-17-6-the-binomial-types.lagda.md`

Chapter 18:

- `src/section-18-1-equivalence-relations-and-the-replacement-axiom.lagda.md`
- `src/section-18-2-the-universal-property-of-set-quotients.lagda.md`
- `src/section-18-3-partitions.lagda.md`
- `src/section-18-4-unique-representatives-of-equivalence-classes.lagda.md`
- `src/section-18-5-set-truncations.lagda.md`

Chapter 19:

- `src/section-19-1-the-type-of-all-groups.lagda.md`
- `src/section-19-2-group-homomorphisms.lagda.md`
- `src/section-19-3-isomorphic-groups-are-equal.lagda.md`
- `src/section-19-4-homotopy-groups-of-types.lagda.md`
- `src/section-19-5-the-eckmann-hilton-argument.lagda.md`
- `src/section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics.lagda.md`

Chapter 20:

- `src/section-20-1-the-type-of-well-founded-trees.lagda.md`
- `src/section-20-2-observational-equality-of-w-types.lagda.md`
- `src/section-20-3-functoriality-of-w-types.lagda.md`
- `src/section-20-4-the-elementhood-relation-on-w-types.lagda.md`
- `src/section-20-5-extensional-w-types.lagda.md`
- `src/section-20-6-russell-s-paradox-in-type-theory.lagda.md`

Chapter 21:

- `src/section-21-1-the-induction-principle-of-the-circle.lagda.md`
- `src/section-21-2-the-dependent-universal-property-of-the-circle.lagda.md`
- `src/section-21-3-multiplication-on-the-circle.lagda.md`

Chapter 22:

- `src/section-22-1-the-universal-cover-of-the-circle.lagda.md`
- `src/section-22-2-working-with-descent-data.lagda.md`
- `src/section-22-3-the-dependent-universal-property-of-the-integers.lagda.md`
- `src/section-22-4-the-fundamental-group-of-the-circle.lagda.md`

## Missing Exercise Files

Exercise files still to create:

- Chapter 1: `src/exercise-1-1-<slug>.lagda.md`
- Chapter 2: `src/exercise-2-2-<slug>.lagda.md` through `src/exercise-2-4-<slug>.lagda.md`
- Chapter 4: `src/exercise-4-1-<slug>.lagda.md`
- Chapter 15: `src/exercise-15-1-<slug>.lagda.md` through `src/exercise-15-5-<slug>.lagda.md`
- Chapter 16: `src/exercise-16-1-<slug>.lagda.md` through `src/exercise-16-11-<slug>.lagda.md`
- Chapter 17: `src/exercise-17-1-<slug>.lagda.md` through `src/exercise-17-20-<slug>.lagda.md`
- Chapter 18: `src/exercise-18-1-<slug>.lagda.md` through `src/exercise-18-14-<slug>.lagda.md`
- Chapter 19: `src/exercise-19-1-<slug>.lagda.md` through `src/exercise-19-17-<slug>.lagda.md`
- Chapter 20: `src/exercise-20-1-<slug>.lagda.md` through `src/exercise-20-7-<slug>.lagda.md`
- Chapter 21: `src/exercise-21-1-<slug>.lagda.md` through `src/exercise-21-8-<slug>.lagda.md`
- Chapter 22: `src/exercise-22-1-<slug>.lagda.md` through `src/exercise-22-11-<slug>.lagda.md`

Choose each exercise slug from the mathematical topic of the corresponding `\exitem`.
