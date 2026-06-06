# Exercise 7.7 Classical finite types

```agda
module exercise-7-7-classical-finite-types where
```

## Problem statement

Recall that

```text
  classical-Fin_k := Σ(x : ℕ) x < k.
```

Show that

```text
  (x = y) ↔ (pr1(x) = pr1(y))
```

for each `x, y : classical-Fin_k`.

## Solution

## Problem statement

By Lemma 7.3.5 it follows that the map `nat-Fin : Fin(k) → ℕ` induces a map
`nat-Fin : Fin(k) → classical-Fin_k`.
Construct a map

```text
  α_k : classical-Fin_k → Fin(k)
```

for each `k : ℕ`, and show that

```text
  α_k(nat-Fin(x)) = x
  nat-Fin(α_k(y)) = y
```

for each `x : Fin(k)` and each `y : classical-Fin_k`.

## Solution
