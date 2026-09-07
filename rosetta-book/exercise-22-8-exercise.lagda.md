# Exercise 22.8

```agda
module exercise-22-8-exercise where

```

## Problem statement

For convenience, we will write `x·_{S^1}y≔mul_(S^1)(x,y)` in this exercise.
Construct the **Mac Lane pentagon** for the circle, i.e. show that the pentagon
<!-- rosetta-diagram: c6643147c2b2; review: pending -->

*3-by-5 diagram (automatic draft).*

```text
                                       [((x·_{S^1} y)·_{S^1} z)·_{S^1} w]                                            [(x·_{S^1} y)·_{S^1} (z·_{S^1} w)]

[(x·_{S^1} (y·_{S^1} z))·_{S^1} w]                                                                                                                          [x·_{S^1} (y·_{S^1} (z ·_{S^1} w))]

                                                                              [x·_{S^1} ((y·_{S^1} z)·_{S^1} w)]

Arrows:
- ((x·_{S^1} y)·_{S^1} z)·_{S^1} w --unlabeled--> (x·_{S^1} y)·_{S^1} (z·_{S^1} w)
- ((x·_{S^1} y)·_{S^1} z)·_{S^1} w --unlabeled--> (x·_{S^1} (y·_{S^1} z))·_{S^1} w
- (x·_{S^1} y)·_{S^1} (z·_{S^1} w) --unlabeled--> x·_{S^1} (y·_{S^1} (z ·_{S^1} w))
- (x·_{S^1} (y·_{S^1} z))·_{S^1} w --unlabeled--> x·_{S^1} ((y·_{S^1} z)·_{S^1} w)
- x·_{S^1} ((y·_{S^1} z)·_{S^1} w) --unlabeled--> x·_{S^1} (y·_{S^1} (z ·_{S^1} w))
```
commutes for every `x,y,z,w:S^1`.

## Solution

<!-- rosetta-item: exercise-22-8 -->

No formalization has been curated yet.
