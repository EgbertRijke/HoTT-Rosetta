# Exercise 10.8

```agda
module exercise-10-8-fiber-replacement where

```

## Problem statement

Construct for any map `f:A→ B` an equivalence `e:A ≃ Σ(y:B) fib(f, y)` and a homotopy `H:f~ pr 1∘ e` witnessing that the triangle
<!-- rosetta-diagram: 2e82e7bed468; review: pending -->

```text
 [A]                [Σ(y:B) fib(f, y)]

           [B]

Arrows:
- A --e--> Σ(y:B) fib(f, y)
- A --f--> B
- Σ(y:B) fib(f, y) --pr 1--> B
```
commutes.
The projection `pr 1 : (Σ(y:B) fib(f, y))→ B` is sometimes also called the **fibrant replacement** of `f`, because first projection maps are fibrations in the homotopy interpretation of type theory.

## Solution

No formalization has been curated yet.
