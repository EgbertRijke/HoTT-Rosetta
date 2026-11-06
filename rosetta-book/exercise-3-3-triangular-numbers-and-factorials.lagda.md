# Exercise 3.3 Triangular numbers and factorials

```agda
module exercise-3-3-triangular-numbers-and-factorials where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
```

## Problem statements

### Exercise 3.3(a)

Define the **triangular numbers**

```text
  1 + ⋯ + n.
```

## Solution

```agda
inductive-triangular-number-ℕ : ℕ → ℕ
inductive-triangular-number-ℕ 0 = 0
inductive-triangular-number-ℕ (succ-ℕ n) =
  inductive-triangular-number-ℕ n +ℕ succ-ℕ n
```

### Exercise 3.3(b)

Define the **factorial** operation `n ↦ n!`.

## Solution 

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = factorial-ℕ m *ℕ succ-ℕ m
```

Agda-unimath sources:

- The inductive definition `inductive-triangular-number-ℕ` corresponds to `triangular-number-ℕ` in `elementary-number-theory.triangular-numbers`.
- The factorial function is defined in `elementary-number-theory.factorials`.
