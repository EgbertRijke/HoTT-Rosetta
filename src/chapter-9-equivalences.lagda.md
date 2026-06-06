# Chapter 9 Equivalences

```agda
module chapter-9-equivalences where
```

In this section we will define equivalences of types.
However, we have to be a bit careful in how we define the condition for a map
to be an equivalence.
It turns out to be important that being an equivalence is a *property* of maps,
and not a *structure* on maps.
In other words, we want to define the type

```text
  is-equiv(f)
```

in such a way that we will be able to prove that the type `is-equiv(f)` is a
*proposition*.
Propositions will be defined in the chapter on propositions, sets, and higher
truncation levels, and in the chapter on function extensionality we will be able
to prove that `is-equiv(f)` is indeed a proposition.

It turns out that if we naively define a function `f` to be an equivalence if it
has an inverse, then we won't be able to show that `is-equiv(f)` is a property.
We will therefore say that `f` is an equivalence if it has a separate left and
right inverse.
This may look odd, but when we define equivalences in this way we will be able
to show that `is-equiv(f)` is a property.


```agda
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-2-nonequivalences-booleans-natural-numbers
open import exercise-9-3-homotopic-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import exercise-9-6-coproduct-functor-equivalences
open import exercise-9-7-product-functor-equivalences
open import exercise-9-8-finite-type-arithmetic-equivalences
open import exercise-9-9-finitely-cyclic-maps
```
