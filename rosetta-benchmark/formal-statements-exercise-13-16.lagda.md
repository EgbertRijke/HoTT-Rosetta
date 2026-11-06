# Formal Statements for Exercise 13.16

```agda
module formal-statements-exercise-13-16 where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-12-3-sets
open import section-13-1-equivalent-forms-of-function-extensionality
```

## Problem statement

Let `A` and `B` be sets.
Show that type `A ≃ B` of equivalences from `A` to `B` is equivalent to the type `A ≅ B` of **isomorphisms** from `A` to `B`, i.e., the type of quadruples `(f, g, H, K)` consisting of

```text
  f : A → B
  g : B → A
  H : f ∘ g = id[B]
  K : g ∘ f = id[A].
```

## Formal Statements

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  is-iso-Set :
    (f : hom-Set A B) → UU (l1 ⊔ l2)
  is-iso-Set f = Σ (hom-Set B A) (λ g → (f ∘ g ~ id) × (g ∘ f ~ id))

  iso-Set : UU (l1 ⊔ l2)
  iso-Set = Σ (hom-Set A B) is-iso-Set

  compute-iso-Set : 
    (type-Set A ≃ type-Set B) ≃ iso-Set
  compute-iso-Set = {!!}
```
