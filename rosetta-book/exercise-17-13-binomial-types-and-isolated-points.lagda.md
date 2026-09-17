# Exercise 17.13

```agda
module exercise-17-13-binomial-types-and-isolated-points where

```

## Problem statement

Consider a type `A`.

Recall from Exercise 12.14 that an element `a:A` is isolated if and only if the map `const_a:unit→ A` is a decidable embedding.
Construct an equivalence
```text
binom(A, unit)≃ Σ(a:A) is-isolated(a).
```

Construct an equivalence
```text
binom(A, unit)≃(Σ(X:𝒰) (X+unit)≃ A).
```
Conclude that the map `X↦ X+unit` on a univalent universe `𝒰` is `0`-truncated.

More generally, construct an equivalence
```text
binom(A, B) ≃ Σ(X:𝒰_B) Σ(Y:𝒰) (X+Y≃ A).
```

## Solution

No formalization has been curated yet.
