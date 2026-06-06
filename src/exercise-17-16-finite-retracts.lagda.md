# Exercise 17.16 Finite retracts

```agda
module exercise-17-16-finite-retracts where
```

## Problem statement

Consider a finite type `X` and a univalent universe `𝒰` containing `X`.
Show that the type

```text
  Retr_𝒰(X) :=
    Σ(A : 𝒰) Σ(i : A → X) Σ(r : X → A) r ∘ i ~ id
```

of all retracts of `X` is finite.

## Solution
