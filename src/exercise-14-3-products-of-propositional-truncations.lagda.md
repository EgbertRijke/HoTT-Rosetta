# Exercise 14.3 Products of propositional truncations

```agda
module exercise-14-3-products-of-propositional-truncations where
```

## Problem statement

Consider two maps `f : A → P` and `g : B → Q` into propositions `P` and `Q`.
Show that if both `f` and `g` are propositional truncations then the map
`f × g : A × B → P × Q` is also a propositional truncation.
Conclude that

```text
  ∥ A × B ∥ ≃ ∥ A ∥ × ∥ B ∥.
```

## Solution
