# Exercise 17.2 Not all negated products

```agda
module exercise-17-2-not-all-negated-products where
```

## Problem statement

Give an example of a type family `B` over a type `A` for which the implication

```text
  ¬(Π(x : A) B(x)) → Σ(x : A) ¬ B(x)
```

is false.

## Solution
