# Exercise 17.4 Object classifier points

```agda
module exercise-17-4-object-classifier-points where
```

## Problem statement

Consider a type `A` and a univalent universe `𝒰` containing `A`.
Construct an equivalence

```text
  A ≃ Σ(B : A → 𝒰) is-contr(Σ(a : A) B(a)).
```

## Solution
