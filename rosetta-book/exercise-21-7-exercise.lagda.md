# Exercise 21.7

```agda
module exercise-21-7-exercise where

```

## Problem statement

Consider a multiplicative operation

```text
μ : S¹ → (S¹ → S¹)
```

equipped with a two-sided unit `e : S¹`, i.e., with identifications

```text
left-unit_μ : Π(y : S¹) μ(e,y) = y
right-unit_μ : Π(x : S¹) μ(x,e) = x.
```

Show that

```text
μ(x,y) = mul_{S¹}(x,mul_{S¹}(ē,y))
```

for every `x,y : S¹`, where `ē ≔ inv(e)` is the complex conjugation of `e` on `S¹`.

## Solution

BENCHMARK PROBLEM
