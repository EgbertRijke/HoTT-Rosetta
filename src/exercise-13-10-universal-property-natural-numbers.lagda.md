# Exercise 13.10 Universal property natural numbers

```agda
module exercise-13-10-universal-property-natural-numbers where
```

## Problem statement

Prove the **universal property of `ℕ`**: For any type `X` equipped with
`x : X` and `f : X → X`, the type

```text
  Σ(h : ℕ → X) (h(0) = x) × (h ∘ succ ~ f ∘ h)
```

is contractible.

## Solution
