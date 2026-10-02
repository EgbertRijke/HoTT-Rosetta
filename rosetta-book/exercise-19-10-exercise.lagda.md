# Exercise 19.10

```agda
module exercise-19-10-exercise where

```

## Problem statement

For any type `A`, we define the type of **commutative binary operations** on `A` to be

```text
(Σ(X : BS_2) A^X) → A.
```

If `A` is a set, show that the map

```text
((Σ(X : BS_2) A^X) → A) → (Σ(f : A → (A → A)) Π(x,y : A) f(x,y) = f(y,x))
```

given by `h ↦ λ x. λ y. h(Fin{2},(x,y))` is an equivalence.
In other words, show that every commutative operation `f : A → (A → A)` extends uniquely along the map `f ↦ (Fin{2},f)` as in the diagram

```text
                 [A^{Fin{2}}]
                  |           \
                  |            \ μ
  f ↦ (Fin{2},f)  |             \
                  |              \
                  V               V
          [Σ(X : BS_2) A^X] - - -> [A]
```

Give an informal explanation of this fact in terms of fixed points of the concrete `ℤ/2`-action on the set of binary operations `A → (A → A)`.

## Solution

BENCHMARK PROBLEM
