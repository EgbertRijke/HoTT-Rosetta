# Exercise 21.6

```agda
module exercise-21-6-exercise where

```

## Problem statement

Show that the circle, equipped with the multiplicative operation `mul_(S^1)` is an abelian group, i.e. construct an inverse operation
```text
inv : S^1→S^1
```
and construct identifications
```text
left-inv_{S^1} : mul_(S^1)(inv(x),x) = base
right-inv_{S^1} : mul_(S^1)(x,inv(x)) = base.
```
Moreover, show that the square

*Square-shaped diagram (automatic draft).*

```text
        [inv(base)]        ---->[mul_(S^1)(base,inv(base))]
             |                               |
[mul_(S^1)(inv(base),base)]---->           [base]

Arrows:
- inv(base) --unlabeled--> mul_(S^1)(inv(base),base)
- inv(base) --unlabeled--> mul_(S^1)(base,inv(base))
- mul_(S^1)(base,inv(base)) --unlabeled--> base
- mul_(S^1)(inv(base),base) --unlabeled--> base
```
commutes.

## Solution

No formalization has been curated yet.
