# Section 6.3 Observational equality of the natural numbers

```agda
module section-6-3-observational-equality-of-the-natural-numbers where
```

Using universes, we can define many relations on the natural numbers.
We give here the example of *observational equality* of `ℕ`.
The idea of observational equality is that, if we want to prove that `m` and
`n` are observationally equal, we may do so by looking at `m` and `n`:

1. If both `m` and `n` are `0`, then they are observationally equal.
2. If one of them is `0` and the other is a successor, then they are not
observationally equal.
3. If both `m` and `n` are successors, say `m ≐ succ(m')` and
`n ≐ succ(n')`, then `m` and `n` are observationally equal if and only if their
predecessors `m'` and `n'` are observationally equal.

Thus, observational equality is an inductively defined relation, which gives us
an algorithm for checking equality on `ℕ`.
Indeed, it can be used to show that equality of natural numbers is *decidable*,
i.e., there is a program that decides for any two natural numbers `m` and `n`
whether they are equal or not.

## Definition 6.3.1

We define the **observational equality** of `ℕ` as binary relation
`EqN : ℕ → (ℕ → 𝕌₀)` satisfying

```text
  EqN(0, 0)             ≐ 𝟙      EqN(succ(n), 0)       ≐ ∅
  EqN(0, succ(n))       ≐ ∅      EqN(succ(n), succ(m)) ≐ EqN(n, m).
```

## Construction

We define `EqN` by double induction on `ℕ`.
By the first application of induction it suffices to provide

```text
  E₀ : ℕ → 𝕌₀
  Eₛ : ℕ → ((ℕ → 𝕌₀) → (ℕ → 𝕌₀)).
```

We define `E₀` by induction, taking `E₀₀ := 𝟙` and
`E₀ₛ(n, X, m) := ∅`.
The resulting family `E₀` satisfies

```text
  E₀(0)       ≐ 𝟙
  E₀(succ(n)) ≐ ∅.
```

We define `Eₛ` by induction, taking `Eₛ₀ := ∅` and
`Eₛₛ(n, X, m) := X(m)`.
The resulting family `Eₛ` satisfies

```text
  Eₛ(n, X, 0)       ≐ ∅
  Eₛ(n, X, succ(m)) ≐ X(m).
```

Therefore we have by the computation rule for the first induction that the
judgmental equality

```text
  EqN(0, m)       ≐ E₀(m)
  EqN(succ(n), m) ≐ Eₛ(n, EqN(n), m)
```

holds, from which the judgmental equalities in the statement of the definition
follow.

The observational equality of the natural numbers is important because it can be
used to prove equalities and negations of equalities.
The following proposition enables us to do so.

## Lemma 6.3.2

Observational equality of `ℕ` is a reflexive relation, i.e., we have

```text
  refl-EqN : Π(n : ℕ) EqN(n, n).
```

## Proof

The function `refl-EqN` is defined by induction on `n`, taking

```text
  refl-EqN(0)       := ⋆
  refl-EqN(succ(n)) := refl-EqN(n).
```

## Proposition 6.3.3

For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ EqN(m, n).
```

## Proof

The function `(m = n) → EqN(m, n)` is defined by the induction principle of
identity types, using the reflexivity of `EqN`.

The converse `EqN(m, n) → (m = n)` is defined by induction on `m` and `n`.
If both `m` and `n` are zero, we have `refl(0) : 0 = 0`.
If one of `m` and `n` is zero and the other is a successor, then `EqN(m, n)` is
empty and we have a function `∅ → (m = n)` by the induction principle of the
empty type.
In the inductive step, suppose we have a function `f : EqN(m, n) → (m = n)`.
Then we can define a function

```text
  EqN(succ(m), succ(n)) → (succ(m) = succ(n))
```

as the composite

```text
  EqN(succ(m), succ(n)) → EqN(m, n) → (m = n) →
  (succ(m) = succ(n)).
```

Note that the map on the left is the identity function, because we have the
judgmental equality `EqN(succ(m), succ(n)) ≐ EqN(m, n)` by definition of
`EqN`.
