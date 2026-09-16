# Exercise 5.6

```agda
module exercise-5-6-successor-predecessor-integers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-4-1-arithmetic-operations-integers
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-5-1-the-inductive-definition-of-identity-types
```

## Problem statement

Show that

```text
  succ-ℤ(pred-ℤ(k)) = k
  pred-ℤ(succ-ℤ(k)) = k
```

for any `k : ℤ`, where `pred-ℤ` is the predecessor function on the integers defined in Exercise 4.1(a).

## Solution

```agda
abstract
  is-retraction-pred-ℤ : (k : ℤ) → pred-ℤ (succ-ℤ k) ＝ k
  is-retraction-pred-ℤ (inl zero-ℕ) = refl
  is-retraction-pred-ℤ (inl (succ-ℕ x)) = refl
  is-retraction-pred-ℤ (inr (inl _)) = refl
  is-retraction-pred-ℤ (inr (inr zero-ℕ)) = refl
  is-retraction-pred-ℤ (inr (inr (succ-ℕ x))) = refl

  is-section-pred-ℤ : (k : ℤ) → succ-ℤ (pred-ℤ k) ＝ k
  is-section-pred-ℤ (inl zero-ℕ) = refl
  is-section-pred-ℤ (inl (succ-ℕ x)) = refl
  is-section-pred-ℤ (inr (inl _)) = refl
  is-section-pred-ℤ (inr (inr zero-ℕ)) = refl
  is-section-pred-ℤ (inr (inr (succ-ℕ x))) = refl
```
