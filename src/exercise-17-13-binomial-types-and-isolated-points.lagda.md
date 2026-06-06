# Exercise 17.13 Binomial types and isolated points

```agda
module exercise-17-13-binomial-types-and-isolated-points where
```

## Problem statement

Consider a type `A`.
Recall from Exercise `ex:isolated-point` that an element `a : A` is isolated if
and only if the map `const_a : unit → A` is a decidable embedding.
Construct an equivalence

```text
  binom(A, unit) ≃ Σ(a : A) is-isolated(a).
```

## Solution

## Problem statement

Construct an equivalence

```text
  binom(A, unit) ≃ Σ(X : 𝒰) (X + unit) ≃ A.
```

Conclude that the map `X ↦ X + unit` on a univalent universe `𝒰` is
`0`-truncated.

## Solution

## Problem statement

More generally, construct an equivalence

```text
  binom(A, B) ≃ Σ(X : 𝒰_B) Σ(Y : 𝒰) (X + Y ≃ A).
```

## Solution
