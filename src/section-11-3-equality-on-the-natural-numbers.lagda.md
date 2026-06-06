# Section 11.3 Equality on the natural numbers

```agda
module section-11-3-equality-on-the-natural-numbers where
```

As a first application of the fundamental theorem of identity types, we
characterize the identity type of the natural numbers.
We will use the observational equality `EqN` on `ℕ`.
Recall from Definition 6.3.1 that `EqN` is defined by

```text
  EqN(0, 0)          := 𝟙      EqN(0, n + 1)          := ∅
  EqN(m + 1, 0)      := ∅      EqN(m + 1, n + 1)      := EqN(m, n).
```

This relation is an equivalence relation.
In particular, the reflexivity term `refl-EqN(m) : EqN(m, m)` is defined
inductively by

```text
  refl-EqN(0)     := ⋆
  refl-EqN(m + 1) := refl-EqN(m).
```

Using the reflexivity term, we obtain a canonical map

```text
  (m = n) → EqN(m, n)
```

for every `m, n : ℕ`.

## Theorem 11.3.1

For each `m, n : ℕ`, the canonical map

```text
  (m = n) → EqN(m, n)
```

is an equivalence.

## Proof

By Theorem 11.2.2 it suffices to show that the type

```text
  Σ(n : ℕ) EqN(m, n)
```

is contractible, for each `m : ℕ`.
The center of contraction is defined to be `(m, refl-EqN(m))`.

The contraction

```text
  γ(m) : Π(n : ℕ) Π(e : EqN(m, n)) (m, refl-EqN(m)) = (n, e)
```

is defined for each `m` by induction on `m, n : ℕ`.
In the base case we define

```text
  γ(0, 0, ⋆) := refl.
```

If one of `m` and `n` is zero and the other is a successor, then the type
`EqN(m, n)` is empty, so the desired path can be obtained via the induction
principle of the empty type.

The inductive step remains, in which we have to define the identification

```text
  γ(m + 1, n + 1, e) :
    (m + 1, refl-EqN(m + 1)) = (n + 1, e)
```

for each `m, n : ℕ` equipped with `e : EqN(m, n)`.
We first observe that there is a map

```text
  Σ(n : ℕ) EqN(m, n) → Σ(n : ℕ) EqN(m + 1, n)
```

given by `(n, e) ↦ (n + 1, e)`.
With this definition of `f` we have

```text
  f(m, refl-EqN(m)) ≐ (m + 1, refl-EqN(m + 1)).
```

Therefore we can define

```text
  γ(m + 1, n + 1, e) := ap f (γ(m, n, e)).
```
