# Exercise 17.5

```agda
module exercise-17-5-surjective-precomposition where

```

## Problem statement

Consider a map `f : A → B`.
Show that the following are equivalent:

1. The map `f` is surjective.

2. For every set `C`, the precomposition function
```text
_ ∘ f : (B → C) → (A → C)
```
    is an embedding.

Hint: To show that (ii) implies (i), use the assumption with the set `C ≔ Prop_𝒰`, where `𝒰` is a univalent universe containing both `A` and `B`.

## Solution

PARTIAL BENCHMARK PROBLEM

The implication (i) ⇒ (ii) is formalized as `is-epimorphism-is-surjective-Set` in the [supplement to Section 15.2](section-15-2-surjective-maps.lagda.md#surjective-maps-are-epimorphisms-with-respect-to-maps-into-sets). The converse remains to be formalized.

```agda
open import section-15-2-surjective-maps using
  ( is-epimorphism-is-surjective-Set)
```
