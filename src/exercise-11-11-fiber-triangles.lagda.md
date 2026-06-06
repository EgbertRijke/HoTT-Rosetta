# Exercise 11.11 Fiber triangles

```agda
module exercise-11-11-fiber-triangles where
```

## Problem statement

Consider a triangle

```text
      h
  A ----> B
   \    /
  f \  / g
     X
```

with a homotopy `H : f ~ g ∘ h` witnessing that the triangle commutes.
Construct a family of maps

```text
  fib-triangle(h, H) : Π(x : X) fib_f(x) → fib_g(x),
```

for which the square

```text
  Σ(x : X) fib_f(x) --tot(fib-triangle(h, H))--> Σ(x : X) fib_g(x)
          |                                                   |
          v                                                   v
          A -----------------------h------------------------> B
```

commutes, where the vertical maps are as constructed in Exercise 10.8.

## Solution

## Problem statement

Show that `h` is an equivalence if and only if `fib-triangle(h, H)` is a family
of equivalences.

## Solution
