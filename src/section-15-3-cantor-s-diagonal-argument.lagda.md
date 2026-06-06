# Section 15.3 Cantor's diagonal argument

```agda
module section-15-3-cantor-s-diagonal-argument where
```

Now that we have introduced surjective maps, we are in position to give
Cantor's famous diagonal argument, which he used to show that there are
infinite sets of different cardinality.
The diagonal argument gives a proof that there is no surjective map from `X` to
its power set `𝒫(X)`.
The power set of a type `X` is of course defined with respect to a universe
`𝒰`, as the type of families of propositions in `𝒰` indexed by `X`.

## Definition 15.3.1

Consider a type `X`, and a universe `𝒰`.
We define the **𝒰-power set** of `X` to be

```text
  𝒫_𝒰(X) := X → Prop_𝒰.
```

## Theorem 15.3.2

For any type `X` and any universe `𝒰`, there is no surjective function

```text
  f : X → 𝒫_𝒰(X).
```

## Proof

Consider a function `f : X → (X → Prop_𝒰)`, and suppose that `f` is
surjective.
Following Cantor's diagonalization argument, we define the subset
`P : X → Prop_𝒰` by

```text
  P(x) := ¬(f(x, x)).
```

Our goal is to reach a contradiction and `f` is assumed to be surjective.
Therefore, it suffices to show that

```text
  ∥ Σ(x : X) f(x) = P ∥ → empty.
```

The empty type is a proposition, so by the universal property of the
propositional truncation it is equivalent to show that

```text
  (Σ(x : X) f(x) = P) → empty.
```

Consider an element `x : X` equipped with an identification `f(x) = P`.
Our goal is to construct an element of the empty type, i.e., to reach a
contradiction.
By the identification `f(x) = P` it follows that

```text
  f(x, y) ↔ P(y)
```

for all `y : X`.
In particular, it follows that `f(x, x) ↔ P(x)`.
However, since `P(x)` is defined as `¬(f(x, x))`, we obtain that
`f(x, x) ↔ ¬(f(x, x))`.
By Exercise `ex:no-fixed-points-neg` this gives us the desired contradiction.
