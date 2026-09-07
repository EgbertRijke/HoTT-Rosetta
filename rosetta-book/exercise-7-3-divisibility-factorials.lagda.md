# Exercise 7.3

```agda
module exercise-7-3-divisibility-factorials where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import exercise-3-3-triangular-numbers-and-factorials
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
open import exercise-7-2-divisibility-poset
```

## Problem statement

Construct a dependent function
```text
Π(x:ℕ) (x≠ 0)→ ((x≤ n)→ (x| n!))
```
for every `n:ℕ`.

## Solution

<!-- rosetta-item: exercise-7-3 -->

<!-- rosetta-agda-block: exercise-7-3-identity-function-adapted -->

```agda
id : {l : Level} {A : Type l} → A → A
id a = a
```

<!-- rosetta-agda-block: exercise-7-3-decide-below-successor -->

```agda
decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → (m ≤-ℕ n) + (m ＝ succ-ℕ n)
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (ap succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coproduct id (ap succ-ℕ) (decide-leq-succ-ℕ m n l)
```

<!-- rosetta-agda-block: exercise-7-3-divisibility-factorial -->

```agda
abstract
  div-factorial-ℕ :
    (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
  div-factorial-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
  div-factorial-ℕ (succ-ℕ n) x l H with
    decide-leq-succ-ℕ x n l
  ... | inl l' =
    transitive-div-ℕ x
      ( factorial-ℕ n)
      ( factorial-ℕ (succ-ℕ n))
      ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
      ( div-factorial-ℕ n x l' H)
  ... | inr refl = pair (factorial-ℕ n) refl
```
