# Exercise 12.7 Truncated products

```agda
module exercise-12-7-truncated-products where
```

## Problem statement

Consider two types `A` and `B`.
Show that the following are equivalent:

1. There are functions

```text
  f : B → is-trunc(k + 1, A)
  g : A → is-trunc(k + 1, B).
```

2. The type `A × B` is `(k + 1)`-truncated.

Conclude with Exercise `ex:is-contr-prod` that, if both `A` and `B` come
equipped with an element, then both `A` and `B` are `k`-truncated if and only if
the product `A × B` is `k`-truncated.

## Solution
