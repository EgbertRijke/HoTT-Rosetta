# Exercise 13.10

```agda
module exercise-13-10-universal-property-natural-numbers where

```

## Problem statement

Prove the **universal property of `ℕ`**: For any type `X` equipped with `x:X` and `f:X→ X`, the type
```text
Σ(h:ℕ→ X) (h(0)= x)× (h∘ succ-ℕ~ f∘ h)
```
is contractible.

## Solution

BENCHMARK PROBLEM
