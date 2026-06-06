# Chapter 17 The univalence axiom

```agda
module chapter-17-the-univalence-axiom where
```

The univalence axiom characterizes the identity type of a universe.
Roughly speaking, it asserts that equivalent types are equal.
The univalence axiom therefore postulates the common mathematical habit of
identifying equivalent objects, such as equivalent types, isomorphic groups,
isomorphic rings, logically equivalent propositions, subsets with the same
elements, and so on.
The univalence axiom is due to Voevodsky, who also showed that it is modeled in
the simplicial sets.
He also showed, in one of his first applications, that the univalence axiom
implies function extensionality, which we will also prove here.

One way to think about the univalence axiom is that it *expands* the notion of
equality to encapsulate the notion of equivalence.
It asserts that for each equivalence `e` between two types `X` and `Y` in a
universe `𝒰` there is a unique identification `p_e : X = Y` in the universe
`𝒰` such that transporting along `p_e` in the universal type family over `𝒰`
is homotopic to the original equivalence `e : X ≃ Y`.

Since there might be many distinct equivalences between two types `X` and `Y`,
there will be equally many identifications of those types.
The univalence axiom is therefore inconsistent with the commonly assumed axiom
that all identity types are propositions, i.e., that all types are sets.
Indeed, there are two equivalences `bool ≃ bool`, so a univalent universe
cannot be a set.

```agda
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-17-3-univalence-implies-function-extensionality
open import section-17-4-maps-and-families-of-types
open import section-17-5-classical-mathematics-with-the-univalence-axiom
open import section-17-6-the-binomial-types
open import exercise-17-1-universes-of-truncated-types
open import exercise-17-2-not-all-negated-products
open import exercise-17-3-excluded-middle-and-decidable-equality
open import exercise-17-4-object-classifier-points
open import exercise-17-5-surjective-precomposition
open import exercise-17-6-identity-type-embedding
open import exercise-17-7-sigma-and-coproduct-truncated-maps
open import exercise-17-8-pi-over-propositions
open import exercise-17-9-binary-correspondences
open import exercise-17-10-complements-of-finite-subtypes
open import exercise-17-11-complements-of-pointed-finite-types
open import exercise-17-12-automorphisms-of-k-element-types
open import exercise-17-13-binomial-types-and-isolated-points
open import exercise-17-14-binomial-theorem
open import exercise-17-15-small-retracts-and-products
open import exercise-17-16-finite-retracts
open import exercise-17-17-truncated-retracts
open import exercise-17-18-surjections-into-truncated-types
open import exercise-17-19-embeddings-between-uniform-finite-types
open import exercise-17-20-prime-decompositions
```
