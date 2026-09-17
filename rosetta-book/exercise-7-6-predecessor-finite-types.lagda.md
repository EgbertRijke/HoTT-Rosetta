# Exercise 7.6

```agda
module exercise-7-6-predecessor-finite-types where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
```

## Problem statement

The predecessor function `pred-Fin_k:Fin{k}→Fin{k}` is defined in three steps, just as in the definition of the successor function on `Fin{k}`.

1. We define the element `neg-two_k:Fin{k+1}` by
```text
neg-two_0 ≔⋆
neg-two_{k+1} ≔ i(⋆).
```

2. We define the function `skip-neg-two_k:Fin{k}→Fin{k+1}` recursively by

```text
skip-neg-two_{k+1}(i(x)) ≔ i(i(x))
skip-neg-two_{k+1}(⋆) ≔ ⋆.
```

3. Finally, we define the **predecessor function** `pred-Fin_k:Fin{k}→Fin{k}` recursively by

```text
pred-Fin_{k+1}(i(x)) ≔ skip-neg-two_k(pred-Fin_k(x))
pred-Fin_{k+1}(⋆) ≔ neg-two_k.
```

Show that `pred-Fin_k` is an inverse to `succ-Fin_k`, i.e., construct identifications
```text
succ-Fin_k(pred-Fin_k(x))=x, and pred-Fin_k(succ-Fin_k(x))=x
```
for each `x:Fin{k}`.

## Solution

<!-- rosetta-agda-block: exercise-7-6-negative-finite-elements -->

```agda
neg-one-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-one-Fin k = inr star

is-neg-one-Fin : (k : ℕ) → Fin k → UU lzero
is-neg-one-Fin (succ-ℕ k) x = x ＝ neg-one-Fin k

neg-two-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-two-Fin zero-ℕ = inr star
neg-two-Fin (succ-ℕ k) = inl (inr star)
```

<!-- rosetta-agda-block: exercise-7-6-skip-negative-two -->

```agda
skip-neg-two-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin (succ-ℕ k) (inl x) = inl (inl x)
skip-neg-two-Fin (succ-ℕ k) (inr x) = neg-one-Fin (succ-ℕ k)
```

<!-- rosetta-agda-block: exercise-7-6-predecessor -->

```agda
pred-Fin : (k : ℕ) → Fin k → Fin k
pred-Fin (succ-ℕ k) (inl x) = skip-neg-two-Fin k (pred-Fin k x)
pred-Fin (succ-ℕ k) (inr x) = neg-two-Fin k
```

<!-- rosetta-agda-block: exercise-7-6-predecessor-inverse -->

```agda
pred-zero-Fin :
  (k : ℕ) → is-neg-one-Fin (succ-ℕ k) (pred-Fin (succ-ℕ k) (zero-Fin k))
pred-zero-Fin (zero-ℕ) = refl
pred-zero-Fin (succ-ℕ k) = ap (skip-neg-two-Fin (succ-ℕ k)) (pred-zero-Fin k)

succ-skip-neg-two-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ (succ-ℕ k)) (skip-neg-two-Fin (succ-ℕ k) x) ＝
  inl (succ-Fin (succ-ℕ k) x)
succ-skip-neg-two-Fin zero-ℕ (inr star) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inl x) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inr star) = refl

is-section-pred-Fin :
  (k : ℕ) (x : Fin k) → succ-Fin k (pred-Fin k x) ＝ x
is-section-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
is-section-pred-Fin (succ-ℕ (succ-ℕ k)) (inl x) =
  ( succ-skip-neg-two-Fin k (pred-Fin (succ-ℕ k) x)) ∙
  ( ap inl (is-section-pred-Fin (succ-ℕ k) x))
is-section-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = refl

is-retraction-pred-Fin :
  (k : ℕ) (x : Fin k) → pred-Fin k (succ-Fin k x) ＝ x
is-retraction-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inl x)) =
  ap (skip-neg-two-Fin (succ-ℕ k)) (is-retraction-pred-Fin (succ-ℕ k) (inl x))
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inr star)) = refl
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = pred-zero-Fin (succ-ℕ k)
```
