# Exercise 18.1

```agda
module exercise-18-1-exercise where

```

## Problem statement

Consider a proposition `P`, and define the relation `~_P` on `bool` by
```text
(true~_Ptrue) ≔ unit (true~_Pfalse) ≔ P
(false~_Ptrue) ≔ P (false~_Pfalse) ≔ unit
```

<div class="subexenum">

Show that `~_P` is an equivalence relation.

Consider a universe `𝒰` containing the proposition `P`.
Construct an embedding `{bool/{~}_P}↪Prop_𝒰`.

Use the quotient `bool/~_P` to show that the axiom of choice implies the law of excluded middle.

</div>

## Solution

No formalization has been curated yet.
