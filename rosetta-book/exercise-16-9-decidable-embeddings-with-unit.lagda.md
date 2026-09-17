# Exercise 16.9

```agda
module exercise-16-9-decidable-embeddings-with-unit where

```

## Problem statement

<div class="subexenum">

Consider a set `A` and an arbitrary type `B`.
Show that any embedding `A↪ B` factors uniquely through the embedding `(unit↪ B)↪ B` given by `e↦ e(⋆)`.

A map `f:A→ B` is said to be **decidable** if the type `fib(f, b)` is decidable for all `b:B`.
Write `A↪ᵈ B` for the type of decidable embeddings from `A` to `B`.
Show that for any type `A` with decidable equality and an arbitrary type `B`, any decidable embedding `A↪ᵈ B` factors uniquely through the embedding `(unit↪ᵈ B)↪ B`.

(Escardó) For any two types `A` and `B`, construct an equivalence
```text
((A+unit)≃(B+unit))≃ (unit↪ᵈ (B+unit))×(A≃ B).
```

</div>

## Solution

No formalization has been curated yet.
