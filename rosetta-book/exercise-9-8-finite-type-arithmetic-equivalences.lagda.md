# Exercise 9.8

```agda
module exercise-9-8-finite-type-arithmetic-equivalences where

open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-7-3-the-standard-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-6-coproduct-functor-equivalences
```

## Problem statement

Construct equivalences

```text
  Fin (k + l) ≃ Fin k + Fin l
   Fin (k *ℕ l) ≃ Fin k × Fin l.
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
inv-compute-coproduct-Fin k l =
  ( _ , 
    is-equiv-is-invertible'
      ( is-invertible-map-inv-is-invertible
        ( is-invertible-is-equiv
          ( is-equiv-map-equiv (compute-coproduct-Fin k l)))))

map-inv-compute-coproduct-Fin : (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-inv-compute-coproduct-Fin k l = map-equiv (inv-compute-coproduct-Fin k l)

inl-coproduct-Fin : (k l : ℕ) → Fin k → Fin (k +ℕ l)
inl-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inl

inr-coproduct-Fin : (k l : ℕ) → Fin l → Fin (k +ℕ l)
inr-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inr

compute-inl-coproduct-Fin : (k : ℕ) → inl-coproduct-Fin k 0 ~ id
compute-inl-coproduct-Fin k x = refl

product-Fin : (k l : ℕ) → Fin k × Fin l ≃ Fin (k *ℕ l)
product-Fin zero-ℕ l = left-absorption-product (Fin l)
product-Fin (succ-ℕ k) l =
  ( ( compute-coproduct-Fin (k *ℕ l) l) ∘e
    ( equiv-coproduct (product-Fin k l) left-unit-law-product)) ∘e
  ( right-distributive-product-coproduct)

Fin-mul-ℕ : (k l : ℕ) → (Fin (k *ℕ l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l =
  ( _ , 
    is-equiv-is-invertible'
      ( is-invertible-map-inv-is-invertible
        ( is-invertible-is-equiv
          ( is-equiv-map-equiv (product-Fin k l)))))
```

## Supplement

### Computing the inclusion of a coproduct of standard finite types into the natural numbers

```agda
abstract
  nat-coproduct-Fin :
    (n m : ℕ) (x : Fin n + Fin m) →
    nat-Fin (n +ℕ m) (map-compute-coproduct-Fin n m x) ＝
    ind-coproduct _ (nat-Fin n) (λ i → n +ℕ (nat-Fin m i)) x
  nat-coproduct-Fin n zero-ℕ (inl x) = refl
  nat-coproduct-Fin n (succ-ℕ m) (inl x) = nat-coproduct-Fin n m (inl x)
  nat-coproduct-Fin n (succ-ℕ m) (inr (inl x)) = nat-coproduct-Fin n m (inr x)
  nat-coproduct-Fin n (succ-ℕ m) (inr (inr _)) = refl

abstract
  nat-inl-coproduct-Fin :
    (n m : ℕ) (i : Fin n) →
    nat-Fin (n +ℕ m) (inl-coproduct-Fin n m i) ＝ nat-Fin n i
  nat-inl-coproduct-Fin n m i = nat-coproduct-Fin n m (inl i)

abstract
  nat-inr-coproduct-Fin :
    (n m : ℕ) (i : Fin m) →
    nat-Fin (n +ℕ m) (inr-coproduct-Fin n m i) ＝ n +ℕ (nat-Fin m i)
  nat-inr-coproduct-Fin n m i = nat-coproduct-Fin n m (inr i)
```
