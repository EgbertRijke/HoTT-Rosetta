# Exercise 16.5

```agda
module exercise-16-5-finite-dependent-products where

```

## Problem statement

Consider a family `B` of types over `A`.

<div class="subexenum">

Show that if `A` is finite and if each `B(x)` is finite, then the type
```text
Π(x:A) B(x)
```
is finite.

Show that if `A` is finite and if `Π(x:A) B(x)` is finite, then we have
```text
(Π(x:A) ‖B(x)‖)→(Π(x:A) is-finite(B(x))).
```

Show that if `Π(x:A) B(x)` is finite and if each `B(x)` is finite, then `A` is finite if and only if the following three conditions hold:

1. `A` has decidable equality.

2. The type
```text
Σ(x:A) |B(x)|≤ 1
```
    is finite.

3. The type
```text
Π(x:A) (2≤|B(x)|)→ B(x)
```
    is finite.

</div>

## Solution

<!-- rosetta-item: exercise-16-5 -->

No formalization has been curated yet.
