# Exercise 8.6 Decidable equality of products

```agda
module exercise-8-6-decidable-equality-products where
```

## Problem statement

Consider two types `A` and `B`.
Show that the following are equivalent:

1. There are functions

```text
  B → has-decidable-equality(A)
  A → has-decidable-equality(B).
```

2. The product `A × B` has decidable equality.

Conclude that if both `A` and `B` have decidable equality, then so does
`A × B`.

## Solution
