# Exercise 14.1 Propositional truncation properties

```agda
module exercise-14-1-propositional-truncation-properties where
```

## Problem statement

Let `A` be a type.
Show that:

1. `∥ ∥ A ∥ ∥ ↔ ∥ A ∥`.
2. `∥ is-decidable(A) ∥ ↔ is-decidable(∥ A ∥)`.
3. `is-decidable(A) → (∥ A ∥ → A)`.
4. `¬¬ ∥ A ∥ ↔ ¬¬ A`.
5. `∥ A ∥ ∨ ∥ B ∥ ↔ ∥ A + B ∥`.
6. `∃(x : A), ∥ B(x) ∥ ↔ ∥ Σ(x : A) B(x) ∥`.
7. `¬¬(∥ A ∥ → A)`.

## Solution
