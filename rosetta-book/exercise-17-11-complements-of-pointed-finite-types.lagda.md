# Exercise 17.11

```agda
module exercise-17-11-complements-of-pointed-finite-types where

```

## Problem statement

### Exercise 17.11(a)

For any type `A`, construct an equivalence
```text
𝒰_A ≃ Σ(X : 𝒰_{A + unit}) binom(X, unit).
```

### Exercise 17.11(b)

For any `k : ℕ`, construct an equivalence
```text
(Σ(X : BSₖ₊₁) X) ≃ BSₖ.
```
In other words, show that the type of `(k + 1)`-element types equipped with a point is equivalent to the type of `k`-element types.
Conclude that the type of pointed finite types is equivalent to the type of finite types, i.e., conclude that we have an equivalence
```text
(Σ(X : 𝔽) X) ≃ 𝔽.
```

## Solution

BENCHMARK PROBLEM
