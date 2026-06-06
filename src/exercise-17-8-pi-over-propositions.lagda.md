# Exercise 17.8 Pi over propositions

```agda
module exercise-17-8-pi-over-propositions where
```

## Problem statement

Consider a proposition `P` and a universe `𝒰` containing `P`.
Show that the map

```text
  Π_P : (P → 𝒰) → 𝒰,
```

given by `A ↦ Π(p : P) A(p)`, is an embedding.

## Solution
