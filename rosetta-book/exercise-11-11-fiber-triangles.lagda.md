# Exercise 11.11

```agda
module exercise-11-11-fiber-triangles where

```

## Problem statement

Consider a triangle

```text
         h
    A ------> B
     \       /
    f \     / g
       \   /
        v v
         X
```
with a homotopy `H : f ~ g ∘ h` witnessing that the triangle commutes.

### Exercise 11.11(a)

Construct a family of maps
```text
fib-triangle(h,H) : Π(x : X) fib(f, x) → fib(g, x),
```
for which the square

```text
                        tot(fib-triangle(h,H))
  Σ(x : X) fib(f, x) ---------------------------> Σ(x : X) fib(g, x)
           |                                               |
           |                                               |
           v                                               v
           A ---------------------h----------------------> B
```
commutes, where the vertical maps are as constructed in Exercise 10.8.

### Exercise 11.11(b)

Show that `h` is an equivalence if and only if `fib-triangle(h,H)` is a family of equivalences.

## Solution

BENCHMARK PROBLEM
