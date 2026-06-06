# Section 7.2 The congruence relations on natural numbers

```agda
module section-7-2-the-congruence-relations-on-natural-numbers where
```

Relations in the Curry-Howard interpretation of logic into type theory are also
type valued.
More specifically, a binary relation on a type `A` is a family of types
`R(x, y)` indexed by `x, y : A`.
Such relations are sometimes called *typal*.

## Definition 7.2.1

Consider a type `A`.
A **(typal) binary relation** on `A` is defined to be a family of types
`R(x, y)` indexed by `x, y : A`.
Given a binary relation `R` on `A`, we say that `R` is **reflexive** if it comes
equipped with

```text
  ρ : Π(x : A) R(x, x),
```

we say that `R` is **symmetric** if it comes equipped with

```text
  σ : Π(x y : A) R(x, y) → R(y, x),
```

and we say that `R` is **transitive** if it comes equipped with

```text
  τ : Π(x y z : A) R(x, y) → (R(y, z) → R(x, z)).
```

A **(typal) equivalence relation** on `A` is a reflexive, symmetric, and
transitive binary typal relation on `A`.

To define the congruence relation modulo `k` in type theory using the
Curry-Howard interpretation, we will define for any three natural numbers `x`,
`y`, and `k`, a *type*

```text
  x ≡ y mod k
```

consisting of the proofs that `x` is congruent to `y` modulo `k`.
We will define this type by directly interpreting Gauss' definition of the
congruence relations in his *Disquisitiones Arithmeticae*: two numbers `x` and
`y` are congruent modulo `k` if `k` divides the symmetric difference
`dist-ℕ(x, y)` between `x` and `y`.
Recall that `dist-ℕ(x, y)` was defined in Exercise 6.5 recursively by

```text
  dist-ℕ(0, 0)       := 0       dist-ℕ(0, y + 1)       := y + 1
  dist-ℕ(x + 1, 0)   := x + 1   dist-ℕ(x + 1, y + 1)   := dist-ℕ(x, y).
```

## Definition 7.2.2

Consider three natural numbers `k, x, y : ℕ`.
We say that `x` is **congruent to `y` modulo `k`** if it comes equipped with an
element of type

```text
  x ≡ y mod k := k | dist-ℕ(x, y).
```

## Example 7.2.3

For example, `k ≡ 0 mod k`.
To see this, we have to show that `k | dist-ℕ(k, 0)`.
Since `dist-ℕ(k, 0) = k` it suffices to show that `k | k`.
That is, we have to construct a natural number `l` equipped with an
identification `p : kl = k`.
Of course, we choose `l := 1`, and the equation `k1 = k` holds by the right unit
law for multiplication on `ℕ`, which was shown in Exercise 5.5.

## Proposition 7.2.4

For each `k : ℕ`, the congruence relation modulo `k` is an equivalence
relation.

## Proof

Reflexivity follows from the fact that `dist-ℕ(x, x) = 0`, and any number
divides `0`.
Symmetry follows from the fact that `dist-ℕ(x, y) = dist-ℕ(y, x)` for any two
natural numbers `x` and `y`.

The non-trivial part of the claim is therefore transitivity.
Here we use the fact that for any three natural numbers `x`, `y`, and `z`, at
least one of the equalities

```text
  dist-ℕ(x, y) + dist-ℕ(y, z) = dist-ℕ(x, z)
  dist-ℕ(y, z) + dist-ℕ(x, z) = dist-ℕ(x, y)
  dist-ℕ(x, z) + dist-ℕ(x, y) = dist-ℕ(y, z)
```

holds.
A formal proof of this fact is given by case analysis on the six possible ways
in which `x`, `y`, and `z` can be ordered:

```text
  x ≤ y and y ≤ z,    x ≤ z and z ≤ y,
  y ≤ z and z ≤ x,    y ≤ x and x ≤ z,
  z ≤ x and x ≤ y,    z ≤ y and y ≤ x.
```

Therefore it follows by the triangle-equality characterization for `dist-ℕ` and
Proposition 7.1.5 that `k | dist-ℕ(x, z)` if `k | dist-ℕ(x, y)` and
`k | dist-ℕ(y, z)`.
