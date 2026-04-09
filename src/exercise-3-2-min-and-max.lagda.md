# Exercise 3.2 Min and max

```agda
module exercise-3-2-min-and-max where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
```

## Problem statement

Define the binary **min** and **max** functions

```text
    min-ℕ, max-ℕ : ℕ → (ℕ → ℕ).
```

## Solution

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)
```

## Agda-unimath sources

- The definition of the min function is implemented in `elementary-number-theory.minimun-natural-numbers`.
- The definition of the max function is implemented in `elementary-number-theory.maximum-natural-numbers`.
