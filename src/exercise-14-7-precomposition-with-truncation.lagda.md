# Exercise 14.7 Precomposition with truncation

```agda
module exercise-14-7-precomposition-with-truncation where
```

## Problem statement

Consider a family `B` of `(k + 1)`-truncated types over the propositional
truncation `∥ A ∥` of a type `A`.
Show that the map

```text
  (Π(x : ∥ A ∥) B(x)) → (Π(x : A) B(x))
```

given by `f ↦ f ∘ η` is a `k`-truncated map.

## Solution
