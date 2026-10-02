# Exercise 22.8

```agda
module exercise-22-8-exercise where

```

## Problem statement

For convenience, we will write `x ·_{S¹} y ≔ mul_(S¹)(x,y)` in this exercise.
Construct the **Mac Lane pentagon** for the circle, i.e. show that the pentagon

```text
[((x ·_{S¹} y) ·_{S¹} z) ·_{S¹} w] -------------------------> [(x ·_{S¹} y) ·_{S¹} (z ·_{S¹} w)]
                 |                                                             |
                 V                                                             V
[(x ·_{S¹} (y ·_{S¹} z)) ·_{S¹} w]                            [x ·_{S¹} (y ·_{S¹} (z ·_{S¹} w))]
                 \                                                             ^
                      \                                                   /
                          \                                          /
                               V                                /
                               [x ·_{S¹} ((y ·_{S¹} z) ·_{S¹} w)]
```
commutes for every `x,y,z,w : S¹`.

## Solution

BENCHMARK PROBLEM
