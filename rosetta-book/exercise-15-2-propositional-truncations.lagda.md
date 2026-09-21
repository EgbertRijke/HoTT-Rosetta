# Exercise 15.2

```agda
module exercise-15-2-propositional-truncations where

```

## Problem statement

### Exercise 15.2(a)

Show that for any proposition `P`, the constant map

```text
  const_⋆ : P → unit
```
is an embedding.
Use this fact to construct an equivalence

```text
  (Σ(A : 𝒰) A ↪ unit) ≃ Prop_𝒰.
```

### Exercise 15.2(b)

Consider a map `f : A → P` into a proposition `P`.
Show that the following are equivalent:

1. The map `f` is a propositional truncation of `A`.

2. The constant map `P → unit` satisfies the universal property of the image of the constant map `A → unit`.

## Solution
