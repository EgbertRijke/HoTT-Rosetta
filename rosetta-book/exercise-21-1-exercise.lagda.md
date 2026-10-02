# Exercise 21.1

```agda
module exercise-21-1-exercise where

```

## Problem statement

Show that for any type `X` and any `x : X`, the map
```text
ind-S¹(x,refl) : S¹ → X
```
is homotopic to the constant map `const_x`.

Show that
```text
ind-S¹(base,loop) : S¹ → S¹
```
is homotopic to the identity function.

Consider a map `f : X → Y` and a free loop `(x,l)` in `X`.
Construct a homotopy
```text
ind-S¹(f(x),ap_{f}(l)) ~ f ∘ ind-S¹(x,l).
```

## Solution

BENCHMARK PROBLEM
