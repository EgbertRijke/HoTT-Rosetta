# Exercise 14.6 Propositional truncations of decidable types

```agda
module exercise-14-6-propositional-truncations-of-decidable-types where
```

## Problem statement

Consider a type `A` equipped with an element `d : is-decidable(A)`.
Define a function

```text
  f : A → Σ(x : A) inl(x) = d
```

and show that `f` is a propositional truncation of `A`.

## Solution

## Problem statement

Consider the function `π : is-decidable(A) → Fin(2)` defined by

```text
  π(inl(x)) := 1
  π(inr(x)) := 0.
```

Define a function `g : A → (π(d) = 1)` and show that `g` is a propositional
truncation of `A`.

## Solution
