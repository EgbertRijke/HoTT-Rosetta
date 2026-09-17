# Exercise 20.5

```agda
module exercise-20-5-exercise where

```

## Problem statement

For each `x:W(A,B)`, let `{x <(_)}:W(A,B)→𝒰` be the type family generated inductively by the following constructors:
```text
i : Π(y:W(A,B)) (x∈ y) → (x < y)
j : Π(y,z:W(A,B)) (y∈ z) → ((x<y) → (x<z)).
```

Show that the type-valued relation `<` is transitive and irreflexive.

Suppose that the type `W(A,B)` is inhabited and suppose that there exists an element `a:A` for which `B(a)` is inhabited.
Show that the following are equivalent:

1. The type `x<y` is a proposition for all `x,y:W(A,B)`.

2. The type `x∈ y` is a proposition for all `x,y:W(A,B)`.

3. The type `A` is a set and the type `B(a)` is a proposition for all `a:A`.

Thus, in general it is not the case that `<` is a relation valued in propositions.

Show that `W(A,B)` satisfies the following **strong induction principle**: For any type family `P` over `W(A,B)`, if there is a function
```text
h:Π(x:W(A,B)) (Π(y:W(A,B)) (y<x)→ P(y))→ P(x),
```
then there is a function `f:Π(x:W(A,B)) P(x)` equipped with an identification
```text
f(x)=h(x,λ y. λ p. f(y))
```
for all `x:W(A,B)`.

Show that there can be no sequence of elements `x:ℕ→W(A,B)` such that `x_{n+1}< x_n` for all `n:ℕ`.

## Solution

No formalization has been curated yet.
