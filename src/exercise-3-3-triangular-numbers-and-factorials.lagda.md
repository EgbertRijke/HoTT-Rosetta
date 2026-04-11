# Exercise 3.3 Triangular numbers and factorials

```agda
module exercise-3-3-triangular-numbers-and-factorials where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
```

## Problem statement

1. Define the **triangular numbers**

   ```text
      1 + ⋯ + n.
   ```
2. Define the **factorial** operation `n ↦ n!`.

## Solutions

```agda
inductive-triangular-number-ℕ : ℕ → ℕ
inductive-triangular-number-ℕ 0 = 0
inductive-triangular-number-ℕ (succ-ℕ n) =
  inductive-triangular-number-ℕ n +ℕ succ-ℕ n

factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = (factorial-ℕ m) *ℕ (succ-ℕ m)
```

## Agda-unimath source

In agda-unimath, the triangular numbers are defined in multiple ways, which are shown to be equivalent.
The intended solution here was to define the triangular numbers by induction.
An alternative solution is to define the `n`th triangular number as the bounded sum

```text
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ n = bounded-sum-ℕ n (λ x H → x)
```

The bounded sum is defined as follows, and requires in particular the inequality relation `≤` to be already defined.
We will define this relation in Chapter 6.

```text
bounded-sum-ℕ :
  (N : ℕ) → ((i : ℕ) → leq-ℕ i N → ℕ) → ℕ
bounded-sum-ℕ zero-ℕ f =
  f 0 (refl-leq-ℕ 0)
bounded-sum-ℕ (succ-ℕ N) f =
  add-ℕ
    ( bounded-sum-ℕ N (λ x H → f x (preserves-order-succ-ℕ x N H)))
    ( f (succ-ℕ N) (refl-leq-ℕ N))
```
