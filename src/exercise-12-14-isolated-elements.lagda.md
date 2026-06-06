# Exercise 12.14 Isolated elements

```agda
module exercise-12-14-isolated-elements where
```

## Problem statement

Consider a type `A` equipped with an element `a : A`.
We say that `a` is an **isolated element** of `A` if it comes equipped with an
element of type

```text
  is-isolated(a) := Π(x : A) (a = x) + (a ≠ x).
```

Show that `a` is isolated if and only if the map `const_a : unit → A` has
decidable fibers.

## Solution

## Problem statement

Show that if `a` is isolated, then `a = x` is a proposition, for every `x : A`.
Conclude that if `a` is isolated, then the map `const_a : unit → A` is an
embedding.

## Solution
