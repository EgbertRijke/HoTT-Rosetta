# Exercise 13.5 Path-split and coherently invertible propositions

```agda
module exercise-13-5-path-split-and-coherently-invertible-propositions where
```

## Problem statement

Show that `path-split(f)` and `is-coh-invertible(f)` are propositions for any
map `f : A → B`.
Conclude that we have equivalences

```text
  is-equiv(f) ≃ path-split(f) ≃ is-coh-invertible(f).
```

## Solution

## Problem statement

Construct for any type `A` an equivalence

```text
  has-inverse(id_A) ≃ (id_A ~ id_A).
```

Note: We will use this fact in Exercise `ex:is_invertible_id_S1` to show that
there are types for which `has-inverse(id_A) ≄ is-equiv(id_A)`.

## Solution
