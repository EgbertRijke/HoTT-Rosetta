# Exercise 11.2

```agda
module exercise-11-2-paths-along-equivalences where

```

## Problem statement

Consider an equivalence `e:A≃ B`.
Construct an equivalence
```text
p↦ p̃:(e(x)=y)≃(x=e^{-1}(y))
```
for every `x:A` and `y:B`, such that the triangle
<!-- rosetta-diagram: 7bba382ff5fc; review: pending -->

```text
[e(x)]---->[e(e^{-1}(y))]

        [y]

Arrows:
- e(x) --ap_{e}(p̃)--> e(e^{-1}(y))
- e(x) --p--> y
- e(e^{-1}(y)) --G(y)--> y
```
commutes for every `p:e(x)=y`.
In this diagram, the homotopy `G:e∘ e^{-1}~ id` is the homotopy witnessing that `e^{-1}` is a section of `e`.

## Solution

<!-- rosetta-item: exercise-11-2 -->

No formalization has been curated yet.
