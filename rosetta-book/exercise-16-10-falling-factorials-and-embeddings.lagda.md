# Exercise 16.10

```agda
module exercise-16-10-falling-factorials-and-embeddings where

```

## Problem statement

For any two types `A` and `B`, construct an equivalence
```text
((A+unit)↪ᵈ(B+unit))≃ (unit ↪ᵈ (B+unit))× (A↪ᵈ B).
```

Construct an equivalence `Fin{\fallingfactorial{n}{m}}≃(Fin{m}↪Fin{n})`, where `\fallingfactorial{n}{m}` is the **`m`-th falling factorial** of `n`, which is defined recursively by
```text
\fallingfactorial{0}{0} ≔ 1 \fallingfactorial{0}{m+1} ≔ 0
\fallingfactorial{n+1}{0} ≔ 1 \fallingfactorial{n+1}{m+1} ≔ (n+1)\fallingfactorial{n}{m}.
```
Conclude that if `A` and `B` are finite with cardinality `m` and `n`, then the type `A↪ B` is finite with cardinality `\fallingfactorial{n}{m}`.

## Solution

No formalization has been curated yet.
