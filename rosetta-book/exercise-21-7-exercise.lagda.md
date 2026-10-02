# Exercise 21.7

```agda
module exercise-21-7-exercise where

```

## Problem statement

Show that for any multiplicative operation
```text
μ : S¹ → (S¹ → S¹)
```
that satisfies the condition that `μ(x,_)` and `μ(_,x)` are equivalences for any `x : S¹`, there is an element `e : S¹` such that
```text
μ(x,y) = mul_(S¹)(x,mul_(S¹)(ē,y))
```
for every `x,y : S¹`, where `ē ≔ inv(e)` is the complex conjugation of `e` on `S¹`.

## Solution

BENCHMARK PROBLEM
