# Exercise 5.3 Lifting identifications

```agda
module exercise-5-3-lift where
```

## Problem statement

Let `B` be a type family over `A`, and consider an identification `p : a = x` in
`A`.
Construct for any `b : B(a)` an identification

```text
  lift_B(p,b) : (a, b) = (x, tr_B(p, b)).
```

In other words, an identification `p : x = y` in the *base type* `A` *lifts* to
an identification in `Σ(x : A) B(x)` for every element in `B(x)`, analogous to
the path lifting property for fibrations in homotopy theory.


## Solution
