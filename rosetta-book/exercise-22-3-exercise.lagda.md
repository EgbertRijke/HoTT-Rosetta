# Exercise 22.3

```agda
module exercise-22-3-exercise where

```

## Problem statement

The **(twisted) double cover** of the circle is defined as the type family `T≔D(bool,neg-bool):S^1→𝒰`, where `neg-bool:bool ≃ bool` is the negation equivalence of Example 9.2.4.

Show that `¬(Π(t:S^1) T(t))`.

Construct an equivalence `e:S^1 ≃ Σ(t:S^1) T(t)` for which the triangle

*Triangle-shaped diagram (automatic draft).*

```text
[S^1]               [Σ(t:S^1) T(t)]

          [S^1]

Arrows:
- S^1 --e--> Σ(t:S^1) T(t)
- S^1 --deg(2)--> S^1
- Σ(t:S^1) T(t) --pr 1--> S^1
```
commutes.

## Solution

No formalization has been curated yet.
