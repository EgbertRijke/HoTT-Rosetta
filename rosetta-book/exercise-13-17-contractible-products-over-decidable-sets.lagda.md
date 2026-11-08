# Exercise 13.17

```agda
module exercise-13-17-contractible-products-over-decidable-sets where

```

## Problem statement

Suppose that `A : I → 𝒰` is a type family over a set `I` with decidable equality.
Show that

```text
  (Π(i : I) is-contr(Aᵢ)) ↔ is-contr(Π(i : I) Aᵢ).
```

## Solution

PARTIAL BENCHMARK PROBLEM

The forward implication is formalized by `is-contr-Π` in [Section 13.1](section-13-1-equivalent-forms-of-function-extensionality.lagda.md).
The converse remains to be formalized.

```agda
open import section-13-1-equivalent-forms-of-function-extensionality
  using (is-contr-Π)
```
