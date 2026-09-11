# Exercise 3.6

```agda
module exercise-3-6-division-by-two where

open import exercise-2-3-exercise
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
```

## Problem statement

Define division by two rounded down as a function `ℕ→ℕ` in two ways: first by pattern matching, and then directly by the induction principle of `ℕ`.

## Solution

<!-- rosetta-item: exercise-3-6 -->

<!-- rosetta-agda-block: exercise-3-6-division-by-two-block-1 -->

```agda
division-by-two : ℕ → ℕ 
division-by-two zero-ℕ = 0
division-by-two (succ-ℕ zero-ℕ) = 0
division-by-two (succ-ℕ (succ-ℕ n)) = succ-ℕ (division-by-two n)

shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ = const ℕ ℕ zero-ℕ

div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f =
  shift-two (f 1) (succ-ℕ (f zero-ℕ)) (const ℕ ℕ zero-ℕ)

div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)

div-two-ℕ : ℕ → ℕ
div-two-ℕ n = div-two-function n zero-ℕ
```
