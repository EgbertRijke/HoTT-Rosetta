# Exercise 13.17 Contractible products over decidable sets

```agda
module exercise-13-17-contractible-products-over-decidable-sets where
```

## Problem statement

Suppose that `A : I → 𝒰` is a type family over a set `I` with decidable
equality.
Show that

```text
  (Π(i : I) is-contr(A_i)) ↔ is-contr(Π(i : I) A_i).
```

## Solution
