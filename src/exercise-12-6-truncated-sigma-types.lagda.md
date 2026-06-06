# Exercise 12.6 Truncated Sigma types

```agda
module exercise-12-6-truncated-sigma-types where
```

## Problem statement

Consider a type family `B` over a `k`-truncated type `A`.
Show that the following are equivalent:

1. The type `B(x)` is `k`-truncated for each `x : A`.
2. The type `Σ(x : A) B(x)` is `k`-truncated.

Hint: for the base case, use Exercises `ex:contr_in_sigma` and
`ex:contr_equiv`.

## Solution

## Problem statement

Consider a map `f : A → B` into a `k`-type `B`.
Show that the following are equivalent:

1. The type `A` is `k`-truncated.
2. The map `f` is `k`-truncated.

## Solution
