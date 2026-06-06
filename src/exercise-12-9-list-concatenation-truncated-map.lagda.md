# Exercise 12.9 List concatenation truncated map

```agda
module exercise-12-9-list-concatenation-truncated-map where
```

## Problem statement

Consider an arbitrary type `A`.
Recall that concatenation of lists was defined in Exercise `ex:lists`.
Show that the map

```text
  f : list(A) × list(A) → list(A)
```

given by `f(x, y) := concat-list(x, y)` is `0`-truncated.

## Solution
