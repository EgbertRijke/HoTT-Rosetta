# Exercise 3.4 Binomial coefficients

```agda
module exercise-3-4-binomial-coefficients where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers    
open import section-3-2-addition-on-the-natural-numbers
```

## Problem statement

Define the **binomial coefficient**  `n choose k` for any `n k : ℕ`, making sure that `n choose k ≐ 0` when `n < k`.

## Solution 

```agda
binomial-coefficient-ℕ : ℕ → ℕ → ℕ
binomial-coefficient-ℕ zero-ℕ zero-ℕ = 1
binomial-coefficient-ℕ zero-ℕ (succ-ℕ k) = 0
binomial-coefficient-ℕ (succ-ℕ n) zero-ℕ = 1
binomial-coefficient-ℕ (succ-ℕ n) (succ-ℕ k) =
  (binomial-coefficient-ℕ n k) +ℕ (binomial-coefficient-ℕ n (succ-ℕ k))
```

## Agda-unimath sources

- The definition of the binomial coefficient is implemented in `elementary-number-theory.binomial-coefficients`.
