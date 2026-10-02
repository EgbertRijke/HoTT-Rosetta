# Exercise 21.2

```agda
module exercise-21-2-exercise where

```

## Problem statement

Show that the circle is connected.

Let `P : S¹ → Prop` be a family of propositions over the circle.
Show that
```text
P(base) → Π(x : S¹) P(x).
```

Show that any embedding `m : S¹ → S¹` is an equivalence.

Show that for any embedding `m : X → S¹`, there is a proposition `P` and an equivalence `e : X ≃ S¹ × P` for which the triangle

```text
 [X]  ----e----> [S¹× P]
    \             /
    m \         / pr1
        V     V
         [S¹]
```
commutes.
In other words, all the embeddings into the circle are of the form `S¹ × P → S¹`.

## Solution

BENCHMARK PROBLEM
