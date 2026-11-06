# Formal Statements for Exercise 13.10

```agda
module formal-statements-exercise-13-10 where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-10-1-contractible-types
```

## Problem statement

Prove the **universal property of `ℕ`**: For any type `X` equipped with `x : X` and `f : X → X`, the type

```text
  Σ(h : ℕ → X) (h(0) = x) × (h ∘ succ-ℕ ~ f ∘ h)
```

is contractible.

## Formal Statements

```agda
structure-map-ℕ :
  {l : Level} (X : UU l) (x : X) (f : X → X) → UU l
structure-map-ℕ X x f =
  Σ (ℕ → X) (λ h → (h 0 ＝ x) × coherence-square-maps h succ-ℕ f h)

universal-property-ℕ :
  {l : Level} {X : UU l} (x : X) (f : X → X) → is-contr (structure-map-ℕ X x f)
universal-property-ℕ = {!!}
```
