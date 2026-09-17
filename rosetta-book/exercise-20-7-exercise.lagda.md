# Exercise 20.7

```agda
module exercise-20-7-exercise where

```

## Problem statement

Consider the **rank comparison relation** `{\preceq} : W(A,B)→ (W(A,B)→Prop_𝒰)` defined recursively by
```text
(tree(a,α)\preceqtree(b,β)) ≔ ∀_{(x:B(a))}∃_{(y:B(b))} α(x)\preceq β(y).
```
If `x\preceq y` holds, we say that `x` has **lower rank** than `y`.
Furthermore, we define the **strict rank comparison relation** `{\prec}` on `W(A,B)` by
```text
(x\prec y)≔ ∃_{(z∈ y)}x\preceq z.
```
If `x\prec y` holds, we say that `x` has **strictly lower rank** than `y`.

Show that the rank comparison relation defines a preordering on `W(A,B)`, i.e., show that `\preceq` is reflexive and transitve.
Furthermore, prove the following properties, in which `<` is the strict ordering on `W(A,B)` defined in Exercise 20.5:

1. `(x \preceq y) ↔ ∀_{(x'<x)}∃_{(y'<y)} x'\preceq y'`

2. `(x < y)→ (x\preceq y)`

3. `(x < y) → (y \npreceq x)`

4. `is-constant_W(x)↔ ∀_{(y:W(A,B))} x \preceq y`.

Show that the relation `\prec` on `W(A,B)` is a strict ordering on `W(A,B)`, i.e., show that it is irreflexive and transitive.
Furthermore, prove the following properties:

1. `(x < y)→ (x\prec y)`

2. `(x \prec y)→ (x\preceq y)`

3. `∀_{(y\preceq y')}∀_{(x'\preceq x)}(x\prec y)→ (x'\prec y')`.

Since `\preceq` defines a preordering on `W(A,B)`, it follows that the preorder `(W(A,B),\preceq)` has a poset reflection, in the sense of Exercise 18.6.
We will write
```text
η : (W(A,B),\preceq)→(\rank(A,B),\preceq)
```
for the poset reflection of `(W(A,B),\preceq)` and its quotient map.
We will call the poset `(R(A,B),\preceq)` the **rank poset** of the W-type `W(A,B)`.

Show that if each `B(x)` is finite, then the rank poset `(\rank(A,B),\preceq)` is either the empty poset, the poset with one element, or it is isomorphic to the poset `(ℕ,≤)`.

Show that the strict ordering `\prec` extends to a relation `\prec` on `\rank(A,B)` with the following properties:

1. We have `(x\prec y)↔ (η(x)\precη(y))` for every `x,y:W(A,B)`.

2. We have `(x\prec y)→ (x\preceq y)` for every `x,y:\rank(A,B)`.

3. The relation `\prec` is transitive and irreflexive on `\rank(A,B)`.

We will call the strictly ordered set `(R(A,B),\prec)` the **(strict) rank** of the W-type `W(A,B)`.

A **strictly ordered set** `(X,<)`, i.e., a set `X` equipped with a transitive, irreflexive relation `<` valued in the propositions, is said to be **well-founded** if for any family `P` of propositions over `X`, the implication
```text
(∀_{(x:X)}(∀_{(y<x)}P(y))→ P(x))→ ∀_{(x:X)}P(x).
```
holds.
Show that the rank `(\rank(A,B),\prec)` of `W(A,B)` is well-founded.

A strictly ordered set `(X,<)` is said to be **extensional** if the logical equivalence
```text
(x=y)↔∀_{(z:X)} (z<x)↔(z<y)
```
holds for any `x,y:X`.
Show that the rank `(\rank(A,B),\prec)` of `W(A,B)` is extensional.

## Solution

No formalization has been curated yet.
