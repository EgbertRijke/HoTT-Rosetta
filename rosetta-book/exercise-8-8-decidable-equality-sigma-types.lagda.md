# Exercise 8.8

```agda
module exercise-8-8-decidable-equality-sigma-types where

```

## Problem statement

Consider a family `B` over `A`, and consider the following three conditions:

1. The type `A` has decidable equality.

2. The type `B(x)` has decidable equality for each `x:A`.

3. The type `Σ(x:A) B(x)` has decidable equality.

Show that if (i) holds, then (ii) and (iii) are equivalent, and show that if `B` has a section `b:Π(x:A) B(x)`, then (ii) and (iii) together imply (i).

## Solution

BENCHMARK PROBLEM
