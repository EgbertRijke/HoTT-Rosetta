# Exercise 7.5 Observational equality of finite types

```agda
module exercise-7-5-observational-equality-finite-types where
```

## Problem statement

The observational equality on `Fin(k)` is a binary relation

```text
  Eq-Fin_k : Fin(k) → (Fin(k) → 𝕌₀)
```

defined recursively by

```text
  Eq-Fin_(k + 1)(i(x), i(y)) := Eq-Fin_k(x, y)
  Eq-Fin_(k + 1)(i(x), ⋆)    := ∅
  Eq-Fin_(k + 1)(⋆, i(y))    := ∅
  Eq-Fin_(k + 1)(⋆, ⋆)       := 𝟙.
```

Show that

```text
  (x = y) ↔ Eq-Fin_k(x, y)
```

for any two elements `x, y : Fin(k)`.

## Solution

## Problem statement

Show that the function `i : Fin(k) → Fin(k + 1)` is injective, for each
`k : ℕ`.

## Solution

## Problem statement

Show that

```text
  succ-Fin_(k + 1)(i(x)) ≠ 0
```

for any `x : Fin(k)`.

## Solution

## Problem statement

Show that the function `succ-Fin_k : Fin(k) → Fin(k)` is injective, for each
`k : ℕ`.

## Solution
