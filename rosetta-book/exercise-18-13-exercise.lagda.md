# Exercise 18.13

```agda
module exercise-18-13-exercise where

```

## Problem statement

Consider two types `A` and `B`.
The **Stirling type of the second kind** is the type
```text
Stirling(A, B) := Σ(X : 𝒰_B) A ↠ X.
```

### Exercise 18.13(a)

Show that if `B` is a `k`-type, then the type `Stirling(A, B)` is also a `k`-type.

### Exercise 18.13(b)

Suppose that `B` has decidable equality.
Construct an equivalence
```text
Stirling(A + unit, B + unit) ≃ (B + unit) × Stirling(A, B + unit) + Stirling(A, B)
```

### Exercise 18.13(c)

Suppose that `A` and `B` are finite types of cardinality `n` and `k`.
Show that the Stirling type `Stirling(A, B)` of the second kind is a finite type of cardinality `Stirling(n, k)`, where `Stirling(n, k)` is the **Stirling number of the second kind**.

## Solution

BENCHMARK PROBLEM
