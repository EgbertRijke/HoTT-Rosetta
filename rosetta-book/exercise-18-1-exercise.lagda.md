# Exercise 18.1

```agda
module exercise-18-1-exercise where

```

## Problem statement

Consider a proposition `P`, and define the relation `~_P` on `bool` by
```text
(true ~_P true) ≔ unit (true ~_P false) ≔ P
(false ~_P true) ≔ P (false ~_P false) ≔ unit
```

### Exercise 18.1(a)

Show that `~_P` is an equivalence relation.

### Exercise 18.1(b)

Consider a universe `𝒰` containing the proposition `P`.
Construct an embedding `{bool / {~}_P} ↪ Prop_𝒰`.

### Exercise 18.1(c)

Use the quotient `bool / ~_P` to show that the axiom of choice implies the law of excluded middle.

## Solution

BENCHMARK PROBLEM
