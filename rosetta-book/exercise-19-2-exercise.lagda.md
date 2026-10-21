# Exercise 19.2

```agda
module exercise-19-2-exercise where

```

## Problem statement

Let `f : hom(G,H)` be a group homomorphism.
Show that `f` preserves units and inverses, i.e., show that
```text
f(e_G) = e_H
f(x⁻¹) = f(x)⁻¹.
```

## Solution

PARTIAL BENCHMARK PROBLEM

Preservation of units is formalized as `preserves-unit-hom-Group` in the [supplement to Section 19.5](section-19-5-the-eckmann-hilton-argument.lagda.md#group-homomorphisms-preserve-the-unit-element). Preservation of inverses remains to be formalized.

```agda
open import section-19-5-the-eckmann-hilton-argument using
  ( preserves-unit-hom-Group)
```
