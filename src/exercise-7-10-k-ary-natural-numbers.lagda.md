# Exercise 7.10 k-ary natural numbers

```agda
module exercise-7-10-k-ary-natural-numbers where
```

## Problem statement

The type `ℕ_k` of **k-ary natural numbers** is an inductive type with the
following constructors:

```text
  constant-ℕ_k : Fin(k) → ℕ_k
  unary-op-ℕ_k : Fin(k) → (ℕ_k → ℕ_k).
```

A `k`-ary natural number can be converted back into an ordinary natural number
via the function `convert-ℕ_k : ℕ_k → ℕ`, which is defined recursively by

```text
  convert-ℕ_k(constant-ℕ_k(x))    := nat-Fin(x)
  convert-ℕ_k(unary-op-ℕ_k(x, n)) :=
    k(convert-ℕ_k(n) + 1) + nat-Fin(x).
```

Show that the type `ℕ_0` is empty.

## Solution

## Problem statement

Show that the function `convert-ℕ_k : ℕ_k → ℕ` is injective.

## Solution

## Problem statement

Show that the function `convert-ℕ_(k + 1) : ℕ_(k + 1) → ℕ` has an inverse, i.e.,
construct a function

```text
  g_k : ℕ → ℕ_(k + 1)
```

equipped with identifications

```text
  convert-ℕ_(k + 1)(g_k(n)) = n
  g_k(convert-ℕ_(k + 1)(x)) = x
```

for each `n : ℕ` and each `x : ℕ_(k + 1)`.

## Solution
