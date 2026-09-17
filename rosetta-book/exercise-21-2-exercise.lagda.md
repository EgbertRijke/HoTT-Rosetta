# Exercise 21.2

```agda
module exercise-21-2-exercise where

```

## Problem statement

<div class="subexenum">

Show that the circle is connected.

Let `P:S^1→Prop` be a family of propositions over the circle.
Show that
```text
P(base)→Π(x:S^1) P(x).
```

Show that any embedding `m:S^1→S^1` is an equivalence.

Show that for any embedding `m:X→S^1`, there is a proposition `P` and an equivalence `e:X ≃ S^1× P` for which the triangle
<!-- rosetta-diagram: 949a7d544e5b; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [X]                [S^1× P]

          [S^1]

Arrows:
- X --m--> S^1
- X --e--> S^1× P
- S^1× P --pr 1--> S^1
```
commutes.
In other words, all the embeddings into the circle are of the form `S^1× P→ S^1`.

</div>

## Solution

No formalization has been curated yet.
