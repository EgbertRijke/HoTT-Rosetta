# Exercise 18.10

```agda
module exercise-18-10-exercise where

```

## Problem statement

A map `f : A → B` is called **weakly path-constant** if it comes equipped with an element of type
```text
is-weakly-path-constant(f) : Π(x,y : A) Π(p,q : x = y) ap_f(p) = ap_f(q).
```
In other words, `f` is weakly path-constant if for each `x,y : A` the map `ap{f} : (x = y) → (f(x) = f(y))` is weakly constant in the sense of Definition 14.4.3.

### Exercise 18.10(a)

Show that every map `‖A‖₀ → B` is weakly path-constant.
Use this to obtain a map
```text
α : (‖A‖₀ → B) → (Σ(f : A → B) is-weakly-path-constant(f)).
```

### Exercise 18.10(b)

Show that if `B` is a `1`-type, then the map `α` is an equivalence.
In other words, show that every weakly path-constant map `f : A → B` into a `1`-type `B` has a unique extension

```text
            A
           / \
        η /   \ f
         /     \
        /       \
       /         \
      ∨           ∨
    ‖A‖₀ - - - -> B
```

## Solution

BENCHMARK PROBLEM
