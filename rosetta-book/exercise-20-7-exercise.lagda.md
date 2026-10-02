# Exercise 20.7

```agda
module exercise-20-7-exercise where

```

## Problem statement

Consider the **rank comparison relation** `≼ : W(A,B) → (W(A,B) → Prop_𝒰)` defined recursively by

```text
(tree(a,α) ≼ (b,β)) ≔ ∀_{(x:B(a))}∃_{(y:B(b))} α(x) ≼ β(y).
```

If `x ≼ y` holds, we say that `x` has **lower rank** than `y`.
Furthermore, we define the **strict rank comparison relation** `{≺}` on `W(A,B)` by

```text
(x ≺ y)≔ ∃_{(z ∈ y)}x ≼ z.
```

If `x ≺ y` holds, we say that `x` has **strictly lower rank** than `y`.

### Exercise 20.7(a)

Show that the rank comparison relation defines a preordering on `W(A,B)`, i.e., show that `≼` is reflexive and transitve.
Furthermore, prove the following properties, in which `<` is the strict ordering on `W(A,B)` defined in Exercise 20.5:

1. `(x ≼ y) ↔ ∀_{(x' < x)}∃_{(y' < y)} x' ≼ y'`

2. `(x < y)→ (x ≼ y)`

3. `(x < y) → ¬(y ≼ x)`

4. `is-constant_W(x) ↔ ∀_{(y:W(A,B))} x ≼ y`.

### Exercise 20.7(b)

Show that the relation `≺` on `W(A,B)` is a strict ordering on `W(A,B)`, i.e., show that it is irreflexive and transitive.
Furthermore, prove the following properties:

1. `(x < y) → (x ≺ y)`

2. `(x ≺ y) → (x ≼ y)`

3. `∀_{(y ≼ y')}∀_{(x' ≼ x)}(x ≺ y) → (x' ≺ y')`.

Since `≼` defines a preordering on `W(A,B)`, it follows that the preorder `(W(A,B),≼)` has a poset reflection, in the sense of Exercise 18.6.
We will write

```text
η : (W(A,B),≼) → (rank(A,B),≼)
```

for the poset reflection of `(W(A,B),≼)` and its quotient map.
We will call the poset `(R(A,B),≼)` the **rank poset** of the W-type `W(A,B)`.

### Exercise 20.7(c)

Show that if each `B(x)` is finite, then the rank poset `(rank(A,B),≼)` is either the empty poset, the poset with one element, or it is isomorphic to the poset `(ℕ,≤)`.

### Exercise 20.7(d)

Show that the strict ordering `≺` extends to a relation `≺` on `rank(A,B)` with the following properties:

1. We have `(x ≺ y) ↔ (η(x) ≺ η(y))` for every `x,y : W(A,B)`.

2. We have `(x ≺ y) → (x ≼ y)` for every `x,y : rank(A,B)`.

3. The relation `≺` is transitive and irreflexive on `rank(A,B)`.

We will call the strictly ordered set `(R(A,B),≺)` the **(strict) rank** of the W-type `W(A,B)`.

### Exercise 20.7(e)

A **strictly ordered set** `(X,<)`, i.e., a set `X` equipped with a transitive, irreflexive relation `<` valued in the propositions, is said to be **well-founded** if for any family `P` of propositions over `X`, the implication

```text
(∀_{(x : X)}(∀_{(y < x)}P(y)) → P(x)) → ∀_{(x : X)}P(x).
```

holds.
Show that the rank `(rank(A,B),≺)` of `W(A,B)` is well-founded.

### Exercise 20.7(f)

A strictly ordered set `(X,<)` is said to be **extensional** if the logical equivalence

```text
(x = y) ↔ ∀_{(z:X)} (z < x) ↔ (z < y)
```

holds for any `x,y : X`.
Show that the rank `(rank(A,B),≺)` of `W(A,B)` is extensional.

## Solution

BENCHMARK PROBLEM
