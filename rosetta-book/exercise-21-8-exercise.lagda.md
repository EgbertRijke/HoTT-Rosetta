# Exercise 21.8

```agda
module exercise-21-8-exercise where

```

## Problem statement

Consider a pointed type `(A,pt)` equipped with a **noncoherent H-space structure** `(μ,H,K)` consisting of a binary operation `μ:A→ (A→ A)` and homotopies
```text
H : Π(y:A) μ(pt,y)=y
K : Π(x:A) μ(x,pt)=x.
```
Show that the homotopy `K` can be adjusted to a new homotopy `K':Π(x:A) μ(x,pt)=x` in such a way that
```text
H(pt)=K'(pt)
```
holds.
In other words, any noncoherent H-space structure can be improved to an H-space structure with the same underlying binary operation.
Hint: Take some inspiration from Lemma 10.4.5, where one of the homotopies of the invertibility of a map was adjusted to obtain coherent invertibility.

## Solution

No formalization has been curated yet.
