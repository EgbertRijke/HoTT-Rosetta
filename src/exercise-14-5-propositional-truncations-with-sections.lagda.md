# Exercise 14.5 Propositional truncations with sections

```agda
module exercise-14-5-propositional-truncations-with-sections where
```

## Problem statement

Consider a map `f : A → P` into a proposition `P`.
Show that if there is a map `g : P → A`, then `f` is a propositional
truncation.
Conclude that for any type `A` equipped with a point `a : A`, the constant map

```text
  const_star : A → unit
```

is a propositional truncation of `A`.

## Solution

## Problem statement

Show that if `A` is a proposition, then `f` is a propositional truncation if
and only if `f` is an equivalence.
Conclude that if `A` is a proposition, then the identity function
`id : A → A` is a propositional truncation.

## Solution
