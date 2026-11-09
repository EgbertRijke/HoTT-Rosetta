# Exercise 11.5

```agda
module exercise-11-5-composite-embeddings-equivalences where

```

## Problem statement

Consider two embeddings `f : A ↪ B` and `g : B ↪ C`.
Show that the following are equivalent:

1. The composite `g ∘ f` is an equivalence.

2. Both `f` and `g` are equivalences.

## Solution

PARTIAL BENCHMARK PROBLEM

The implication (2) ⇒ (1) is formalized by `is-equiv-comp` in Exercise 9.4.
The converse, (1) ⇒ (2), remains to be formalized.

```agda
open import exercise-9-4-three-for-two-equivalences using (is-equiv-comp)
```
