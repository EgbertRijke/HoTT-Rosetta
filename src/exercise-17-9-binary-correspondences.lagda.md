# Exercise 17.9 Binary correspondences

```agda
module exercise-17-9-binary-correspondences where
```

## Problem statement

Consider two types `A` and `B` and a universe `𝒰` containing both `A` and `B`.
A **binary correspondence** `R : A → (B → 𝒰)` is said to be a **function** if it
satisfies the condition

```text
  is-function(R) := Π(a : A) is-contr(Σ(b : B) R(a, b)),
```

and `R` is said to be an **opposite function** if the **opposite
correspondence** `op(R) : B → (A → 𝒰)` given by `op(R)(b, a) := R(a, b)` is
functional.

Construct an equivalence

```text
  (A → B) ≃ Σ(R : A → (B → 𝒰)) is-function(R).
```

## Solution

## Problem statement

Construct an equivalence

```text
  (A ≃ B) ≃
  Σ(R : A → (B → 𝒰)) is-function(R) × is-function(op(R)).
```

## Solution
