# Section 8.3 The well-ordering principle of natural numbers

```agda
module section-8-3-the-well-ordering-principle-of-natural-numbers where
```

The well-ordering principle of the natural numbers in classical mathematics
asserts that any nonempty subset of `ℕ` has a least element.
To formulate the well-ordering principle in type theory, we will use type
families over `ℕ` instead of subsets of `ℕ`.
Moreover, the classical well-ordering principle tacitly assumes that subsets are
decidable.
The type theoretic well-ordering principle of `ℕ` is therefore formulated using
*decidable* families over `ℕ`.

## Definition 8.3.1

Let `P` be a family over `ℕ`, not necessarily decidable.

1. We say that a natural number `n` is a **lower bound** for `P` if it comes
equipped with an element of type

```text
  is-lower-bound_P(n) := Π(x : ℕ) P(x) → (n ≤ x).
```

2. We say that a natural number `n` is an **upper bound** for `P` if it comes
equipped with an element of type

```text
  is-upper-bound_P(n) := Π(x : ℕ) P(x) → (x ≤ n).
```

A minimal element of `P` is therefore a natural number `n` for which `P(n)`
holds, and which is also a lower bound for `P`.
The well-ordering principle of `ℕ` asserts that such an element exists for any
decidable family `P`, as soon as `P(n)` holds for some `n`.

## Theorem 8.3.2

Let `P` be a decidable family over `ℕ`, where `d` witnesses that `P` is
decidable.
Then there is a function

```text
  well-ordering-principle(P, d) :
    (Σ(n : ℕ) P(n)) → (Σ(m : ℕ) P(m) × is-lower-bound_P(m)).
```

## Proof

By the assumption that there are enough universes, there is a universe `𝕌` that
contains `P`.
Instead of proving the claim for the given type family `P`, we will show by
induction on `n : ℕ` that there is a function

```text
  Q(n) → (Σ(m : ℕ) Q(m) × is-lower-bound_Q(m))        (*)
```

for every decidable family `Q : ℕ → 𝕌`.
Note that we are now also quantifying over the decidable families `Q : ℕ → 𝕌`.
This slightly strengthens the inductive hypothesis, which we will be able to
exploit.

The base case is trivial, since `0` is a lower bound of every type family over
`ℕ`.
For the inductive step, assume that `(*)` holds for every decidable type family
`Q : ℕ → 𝕌`.
Furthermore, let `Q : ℕ → 𝕌` be a decidable type family equipped with an element
`q : Q(succ(n))`.
Our goal is to construct an element of type

```text
  Σ(m : ℕ) Q(m) × is-lower-bound_Q(m).
```

Since `Q(0)` is assumed to be decidable, it suffices to construct a function

```text
  (Q(0) + ¬ Q(0)) → Σ(m : ℕ) Q(m) × is-lower-bound_Q(m).
```

Therefore we can proceed by case analysis on `Q(0) + ¬ Q(0)`.
In the case where we have an element of type `Q(0)`, it follows immediately that
`0` must be minimal.
In the case where `¬ Q(0)`, we consider the decidable subset `Q'` of `ℕ` given
by

```text
  Q'(n) := Q(succ(n)).
```

Since we have `q : Q'(n)`, we obtain a minimal element in `Q'` by the inductive
hypothesis.
Of course, by the assumption that `Q(0)` doesn't hold, the minimal element of
`Q'` is also the minimal element of `Q`.
