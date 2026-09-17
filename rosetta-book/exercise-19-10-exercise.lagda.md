# Exercise 19.10

```agda
module exercise-19-10-exercise where

```

## Problem statement

For any type `A`, we define the type of **commutative binary operations** on `A` to be
```text
(Σ(X:BS_2) A^X)→ A.
```
If `A` is a set, show that the map
```text
((Σ(X:BS_2) A^X)→ A)→(Σ(f:A→ (A→ A)) Π(x,y:A) f(x,y)=f(y,x))
```
given by `h↦ λ x. λ y. h(Fin{2},(x,y))` is an equivalence.
In other words, show that every commutative operation `f:A→(A→ A)` extends uniquely along the map `f↦(Fin{2},f)` as in the diagram
<!-- rosetta-diagram: bfdf777c4de4; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
  [A^{Fin{2}}]
       |
[Σ(X:BS_2) A^X]----> [A]

Arrows:
- A^{Fin{2}} --μ--> A
- A^{Fin{2}} --f↦{(Fin{2},f)}--> Σ(X:BS_2) A^X
- Σ(X:BS_2) A^X --unlabeled--> A
```
Give an informal explanation of this fact in terms fixed points of the concrete `ℤ/2`-action on the set of binary operations `A→ (A→ A)`.

## Solution

No formalization has been curated yet.
