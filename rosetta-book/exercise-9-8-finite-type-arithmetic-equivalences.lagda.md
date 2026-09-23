# Exercise 9.8

```agda
module exercise-9-8-finite-type-arithmetic-equivalences where

open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-4-4-coproducts
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-6-coproduct-functor-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-13-1-equivalent-forms-of-function-extensionality
```

## Problem statement

Construct equivalences

```text
  Fin_{k+l} ≃ Fin_{k} + Fin_{l}
   Fin_{kl} ≃ Fin_{k} × Fin_{l}.
```

## Solution

```agda
compute-coproduct-Fin : (k l : ℕ) → (Fin k + Fin l) ≃ Fin (k +ℕ l)
compute-coproduct-Fin k zero-ℕ = right-unit-law-coproduct (Fin k)
compute-coproduct-Fin k (succ-ℕ l) =
  ( equiv-coproduct (compute-coproduct-Fin k l) id-equiv) ∘e
  ( inv-associative-coproduct)

map-compute-coproduct-Fin : (k l : ℕ) → (Fin k + Fin l) → Fin (k +ℕ l)
map-compute-coproduct-Fin k l = map-equiv (compute-coproduct-Fin k l)

inv-compute-coproduct-Fin : (k l : ℕ) → Fin (k +ℕ l) ≃ (Fin k + Fin l)
inv-compute-coproduct-Fin k l = inv-equiv (compute-coproduct-Fin k l)

map-inv-compute-coproduct-Fin : (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-inv-compute-coproduct-Fin k l = map-equiv (inv-compute-coproduct-Fin k l)

inl-coproduct-Fin : (k l : ℕ) → Fin k → Fin (k +ℕ l)
inl-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inl

inr-coproduct-Fin : (k l : ℕ) → Fin l → Fin (k +ℕ l)
inr-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inr

compute-inl-coproduct-Fin : (k : ℕ) → inl-coproduct-Fin k 0 ~ id
compute-inl-coproduct-Fin k x = refl

map-compute-map-inv-compute-coproduct-Fin :
  (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-compute-map-inv-compute-coproduct-Fin k zero-ℕ = inl
map-compute-map-inv-compute-coproduct-Fin k (succ-ℕ l) =
  ( map-equiv (associative-coproduct {A = Fin k} {B = Fin l})) ∘
  ( map-coproduct (map-compute-map-inv-compute-coproduct-Fin k l) id)

abstract
  compute-map-inv-compute-coproduct-Fin :
    (k l : ℕ) →
    map-inv-compute-coproduct-Fin k l ~
    map-compute-map-inv-compute-coproduct-Fin k l
  compute-map-inv-compute-coproduct-Fin k zero-ℕ x = refl
  compute-map-inv-compute-coproduct-Fin k (succ-ℕ l) x =
    ( htpy-eq
      ( distributive-map-inv-comp-equiv
        ( inv-associative-coproduct)
        ( equiv-coproduct (compute-coproduct-Fin k l) id-equiv))
      ( x)) ∙
    ( htpy-eq-equiv
      ( inv-inv-equiv associative-coproduct)
      ( map-inv-equiv-coproduct (compute-coproduct-Fin k l) id-equiv x)) ∙
    ( ap
      ( map-associative-coproduct)
      ( htpy-map-coproduct
        ( compute-map-inv-compute-coproduct-Fin k l)
        ( refl-htpy)
        ( x)))
```
