# Exercise 7.6 Predecessor on finite types

```agda
module exercise-7-6-predecessor-finite-types where
```

## Problem statement

The predecessor function `pred-Fin_k : Fin(k) → Fin(k)` is defined in three
steps, just as in the definition of the successor function on `Fin(k)`.

1. We define the element `neg-two-Fin_k : Fin(k + 1)` by

```text
  neg-two-Fin_0       := ⋆
  neg-two-Fin_(k + 1) := i(⋆).
```

2. We define the function `skip-neg-two-Fin_k : Fin(k) → Fin(k + 1)`
recursively by

```text
  skip-neg-two-Fin_(k + 1)(i(x)) := i(i(x))
  skip-neg-two-Fin_(k + 1)(⋆)    := ⋆.
```

3. Finally, we define the **predecessor function**
`pred-Fin_k : Fin(k) → Fin(k)` recursively by

```text
  pred-Fin_(k + 1)(i(x)) := skip-neg-two-Fin_k(pred-Fin_k(x))
  pred-Fin_(k + 1)(⋆)    := neg-two-Fin_k.
```

Show that `pred-Fin_k` is an inverse to `succ-Fin_k`, i.e., construct
identifications

```text
  succ-Fin_k(pred-Fin_k(x)) = x
  pred-Fin_k(succ-Fin_k(x)) = x
```

for each `x : Fin(k)`.

## Solution
