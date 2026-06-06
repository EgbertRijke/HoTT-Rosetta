# Exercise 10.8 Fiber replacement

```agda
module exercise-10-8-fiber-replacement where
```

## Problem statement

Construct for any map `f : A → B` an equivalence

```text
  e : A ≃ Σ(y : B) fib_f(y)
```

and a homotopy `H : f ~ pr1 ∘ e` witnessing that the triangle

```text
      e
  A ----> Σ(y : B) fib_f(y)
   \           /
  f \         / pr1
     \       /
        B
```

commutes.
The projection `pr1 : (Σ(y : B) fib_f(y)) → B` is sometimes also called the
**fibrant replacement** of `f`, because first projection maps are fibrations in
the homotopy interpretation of type theory.

## Solution
