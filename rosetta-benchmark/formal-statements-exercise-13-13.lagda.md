# Formal Statements for Exercise 13.13

```agda
module formal-statements-exercise-13-13 where

open import universe-levels
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-9-2-bi-invertible-maps
```

## Problem statement

Show that *`Π`-types distribute over coproducts*, i.e., construct for any type `X` and any two families `A` and `B` over `X` an equivalence from the type `Π(x : X) A(x) + B(x)` to the type

```text
  Σ(f : X → Fin 2) (Π(x : X) A(x)^{f(x) = 0}) × (Π(x : X) B(x)^{f(x) = 1}).
```

## Formal Statements

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  distributive-Π-coproduct :
    ((x : X) → A x + B x) ≃
    Σ ( X → Fin 2)
      ( λ f →
        ( (x : X) → (f x ＝ zero-Fin 1) → A x) ×
        ( (x : X) → (f x ＝ one-Fin 1) → B x))
  distributive-Π-coproduct = ?
```
