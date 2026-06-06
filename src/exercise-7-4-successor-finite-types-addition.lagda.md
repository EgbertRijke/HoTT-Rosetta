# Exercise 7.4 Successor on finite types as addition

```agda
module exercise-7-4-successor-finite-types-addition where
```

## Problem statement

Define `1 := [1]_(k + 1) : Fin(k + 1)`.
Show that

```text
  succ-Fin_(k + 1)(x) = x + 1
```

for any `x : Fin(k + 1)`.

## Solution
