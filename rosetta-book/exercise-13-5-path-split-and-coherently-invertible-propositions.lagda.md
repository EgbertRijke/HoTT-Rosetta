# Exercise 13.5

```agda
module exercise-13-5-path-split-and-coherently-invertible-propositions where

```

## Problem statement

### Exercise 13.5(a)

Show that `is-path-split(f)` and `is-coh-invertible(f)` are propositions for any map `f : A → B`.
Conclude that we have equivalences
```text
is-equiv(f) ≃ is-path-split(f) ≃ is-coh-invertible(f).
```

### Exercise 13.5(b)

Construct for any type `A` an equivalence
```text
has-inverse(id[A]) ≃ (id[A] ~ id[A]).
```
Note: We will use this fact in Exercise 22.5 to show that there are types for which `has-inverse(id[A]) ≄ is-equiv(id[A])`.

## Solution

BENCHMARK PROBLEM
