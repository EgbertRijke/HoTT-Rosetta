# Exercise 13.9 Uniqueness of identity types

```agda
module exercise-13-9-uniqueness-of-identity-types where
```

## Problem statement

Consider a type `A` equipped with an element `a : A` and consider a type family
`B` over `A` equipped with an element `b : B(a)`.
Show that the following are equivalent:

1. The map

```text
  ev_b : (Π(x : A) B(x) → C(x)) → C(a)
```

given by `ev_b(h) := h(a, b)` is an equivalence for any type family `C` over
`A`.

2. The map

```text
  h : Π(x : A) (a = x) → B(x)
```

given by `h(a, refl) := b` is an equivalence.

## Solution
