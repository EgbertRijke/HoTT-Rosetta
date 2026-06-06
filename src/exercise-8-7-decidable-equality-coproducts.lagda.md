# Exercise 8.7 Decidable equality of coproducts

```agda
module exercise-8-7-decidable-equality-coproducts where
```

## Problem statement

Consider two types `A` and `B`, and consider the observational equality
`Eq-coprod` on the coproduct `A + B` defined by

```text
  Eq-coprod(inl(x), inl(x')) := x = x'
  Eq-coprod(inl(x), inr(y')) := ∅
  Eq-coprod(inr(y), inl(x')) := ∅
  Eq-coprod(inr(y), inr(y')) := y = y'.
```

Show that `(x = y) ↔ Eq-coprod(x, y)` for every `x, y : A + B`.

## Solution

## Problem statement

Show that the following are equivalent:

1. Both `A` and `B` have decidable equality.
2. The coproduct `A + B` has decidable equality.

Conclude that `ℤ` has decidable equality.

## Solution
