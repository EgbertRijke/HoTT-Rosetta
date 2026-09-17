# Exercise 19.14

```agda
module exercise-19-14-exercise where

```

## Problem statement

Consider a subtype
```text
P:𝒰→Prop_𝒱
```
of a universe `𝒰`.
We say that a type `A:𝒰` is a **`P`-type** if `P(A)` holds, we say that a map `f:A→ B` is a **`P`-map** if its fibers are `P`-types, and we say that `A` is **`P`-separated** if its identity types are `P`-types.

Now consider a connected type `A:𝒰` equipped with an element `a:A`, and consider a family of types `B(x):𝒰` indexed by `x:A`.
Show that the following are equivalent:

1. Every family of maps
```text
f:Π(x:A) (a=x)→ B(x)
```
    is a family of `P`-maps.

2. The total space
```text
Σ(x:A) B(x)
```
    is `P`-separated.

For readers familiar with the notion of `k`-connectedness: Conclude that every `f:Π(x:A) (a=x)→ B(x)` is a family of `k`-connected maps if and only if `Σ(x:A) B(x)` is a `(k+1)`-connected type.

## Solution

<!-- rosetta-item: exercise-19-14 -->

No formalization has been curated yet.
