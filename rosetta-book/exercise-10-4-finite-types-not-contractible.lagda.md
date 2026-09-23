# Exercise 10.4

```agda
module exercise-10-4-finite-types-not-contractible where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import exercise-10-1-identity-types-contractible
open import exercise-10-3-contractible-equivalences
open import section-11-5-disjointness-of-coproducts
open import section-12-1-propositions
open import section-12-2-subtypes
```

## Problem statement

Show that `Fin_{k}` is not contractible for all `k ≠ 1`.

## Solution

```agda
is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = (n ＝ 1)

is-one-ℕ' : ℕ → UU lzero
is-one-ℕ' n = (1 ＝ n)

is-not-one-ℕ : ℕ → UU lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → UU lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  neq-inl-inr (eq-is-contr' C (neg-two-Fin (succ-ℕ k)) (neg-one-Fin (succ-ℕ k)))
```

## Supplement

### The type `Fin 1` is contractible

```agda
map-equiv-Fin-1 : Fin 1 → unit
map-equiv-Fin-1 (inr x) = x

map-inv-equiv-Fin-1 : unit → Fin 1
map-inv-equiv-Fin-1 = inr

is-section-map-inv-equiv-Fin-1 :
  ( map-equiv-Fin-1 ∘ map-inv-equiv-Fin-1) ~ id
is-section-map-inv-equiv-Fin-1 _ = refl

is-retraction-map-inv-equiv-Fin-1 :
  ( map-inv-equiv-Fin-1 ∘ map-equiv-Fin-1) ~ id
is-retraction-map-inv-equiv-Fin-1 (inr _) = refl

is-equiv-map-equiv-Fin-1 : is-equiv map-equiv-Fin-1
is-equiv-map-equiv-Fin-1 =
  is-equiv-is-invertible
    map-inv-equiv-Fin-1
    is-section-map-inv-equiv-Fin-1
    is-retraction-map-inv-equiv-Fin-1

equiv-Fin-1 : Fin 1 ≃ unit
pr1 equiv-Fin-1 = map-equiv-Fin-1
pr2 equiv-Fin-1 = is-equiv-map-equiv-Fin-1

is-contr-Fin-1 : is-contr (Fin 1)
is-contr-Fin-1 = is-contr-equiv unit equiv-Fin-1 is-contr-unit

is-prop-Fin-1 : is-prop (Fin 1)
is-prop-Fin-1 = is-prop-is-contr is-contr-Fin-1

Fin-1-Prop : Prop lzero
Fin-1-Prop = (Fin 1 , is-prop-Fin-1)
```
