# Exercise 3.6

```agda
module exercise-3-6-division-by-two where

open import exercise-2-3-constant-maps
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-3-5-fibonacci-sequence
```

## Problem statement

Define division by two rounded down as a function `ℕ → ℕ` in two ways: first by pattern matching, and then directly by the induction principle of `ℕ`.

## Solution

We first define division by two by pattern matching:

```agda
division-by-two : ℕ → ℕ
division-by-two zero-ℕ = 0
division-by-two (succ-ℕ zero-ℕ) = 0
division-by-two (succ-ℕ (succ-ℕ n)) = succ-ℕ (division-by-two n)
```

Next, we define division by two using the induction principle:

```agda
div-two-zero-ℕ : ℕ → ℕ
div-two-zero-ℕ = const ℕ zero-ℕ

div-two-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
div-two-succ-ℕ f =
  shift-two (f 1) (succ-ℕ (f zero-ℕ)) (const ℕ zero-ℕ)

div-two-function : ℕ → ℕ → ℕ
div-two-function = ind-ℕ div-two-zero-ℕ (λ n → div-two-succ-ℕ)

div-two-ℕ : ℕ → ℕ
div-two-ℕ n = div-two-function n zero-ℕ
```
