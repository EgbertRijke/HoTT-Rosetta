# Exercise 10.7 Fibers of projections

```agda
module exercise-10-7-fibers-of-projections where
```

## Problem statement

Let `B` be a family of types over `A`, and consider the projection map

```text
  pr1 : (Σ(x : A) B(x)) → A.
```

Show that for any `a : A`, the map

```text
  λ ((x, y), p). tr_B(p, y) : fib_pr1(a) → B(a)
```

is an equivalence.

## Solution

## Problem statement

Show that the following are equivalent:

1. The projection map `pr1` is an equivalence.
2. The type `B(x)` is contractible for each `x : A`.

## Solution

## Problem statement

Consider a dependent function `b : Π(x : A) B(x)`.
Show that the following are equivalent:

1. The map

```text
  λ x. (x, b(x)) : A → Σ(x : A) B(x)
```

is an equivalence.

2. The type `B(x)` is contractible for each `x : A`.

## Solution
