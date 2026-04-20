# Exercise 3.1 Multiplication and exponentiation

```agda
module exercise-3-1-multiplication-and-exponentiation where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers

open import universe-levels
```

## Problem statement

1. Define the **multiplication** operation

   ```text
      mul-ℕ : ℕ → (ℕ → ℕ).
   ```
2. Define the **exponentiation function** `n,m ↦ m^n` of type `ℕ → (ℕ → ℕ)`.

## Solution

**Note.** Our definition of `exp-ℕ` is a reimplementation of the function `power-Monoid` in agda-unimath. A reimplementation was necessary, so as to avoid loading the theory of semirings, which is built on the theory of monoids, which is in turn built on a large portion of the foundation files, the development of which is the purpose of this book and which could therefore not be superseeded.

```agda
mul-ℕ : ℕ → ℕ → ℕ
mul-ℕ 0 n = 0
mul-ℕ (succ-ℕ m) n = (mul-ℕ m n) +ℕ n

infixl 40 _*ℕ_
_*ℕ_ = mul-ℕ

{-# BUILTIN NATTIMES _*ℕ_ #-}

mul-ℕ' : ℕ → ℕ → ℕ
mul-ℕ' x y = mul-ℕ y x

exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ m zero-ℕ = 1
exp-ℕ m (succ-ℕ zero-ℕ) = m
exp-ℕ m (succ-ℕ (succ-ℕ n)) = mul-ℕ (exp-ℕ m (succ-ℕ n)) m

infixr 45 _^ℕ_
_^ℕ_ = exp-ℕ
```

## Agda-unimath sources

- The definition of multiplication of natural numbers is implemented in `elementary-number-theory.multiplication-natural-numbers`
- The definition of exponentiation of natural numbers is implemented in `elementary-number-theory.exponentiation-natural-numbers`. This definition fits in the following tower of instantiations, where each next entry is more specialized than the previous:

  | Name                         | Module                                               |
  | ---------------------------- | -------------------------------------------------- |
  | `power-Monoid`               | [`group-theory.powers-of-elements-monoids`](https://unimath.github.io/agda-unimath/group-theory.powers-of-elements-monoids.html)          |
  | `power-Semiring`             | [`ring-theory.powers-of-elements-semirings`](https://unimath.github.io/agda-unimath/ring-theory.powers-of-elements-semirings.html)         |
  | `power-Commutative-Semiring` | [`commutative-algebra.powers-of-elements-semirings`](https://unimath.github.io/agda-unimath/commutative-algebra.powers-of-elements-commutative-semirings.html) |
  | `power-ℕ`                    | [`elementary-number-theory.exponentiation-natural-numbers`](https://unimath.github.io/agda-unimath/elementary-number-theory.exponentiation-natural-numbers.html) |
