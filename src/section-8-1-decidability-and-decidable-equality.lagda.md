# Section 8.1 Decidability and decidable equality

```agda
module section-8-1-decidability-and-decidable-equality where
```

## Definition 8.1.1

A type `A` is said to be **decidable** if it comes equipped with an element of
type

```text
  is-decidable(A) := A + ¬ A.
```

A family `P` over a type `A` is said to be **decidable** if `P(x)` is decidable
for every `x : A`.

## Example 8.1.2

The principal way to show that a type `A` is decidable is to either construct an
element `a : A`, or to construct a function `A → ∅`.
For example, the types `𝟙` and `∅` are decidable.
Indeed, we have

```text
  inl(⋆)      : is-decidable(𝟙)
  inr(idfunc) : is-decidable(∅).
```

Furthermore, any type `A` equipped with an element `a : A` is decidable because
we have `inl(a) : is-decidable(A)` for such `A`.

## Example 8.1.3

The principal way to use a hypothesis that `A` is decidable is to proceed by the
induction principle of coproducts, i.e., to proceed by case analysis.

For example, if `A` and `B` are decidable types, then the types `A + B`,
`A × B`, and `A → B` are also decidable.
This is straightforward to prove directly by pattern-matching on the variables
of type `is-decidable(A)` and `is-decidable(B)`.
When we go through these proofs, the familiar truth table emerges:

| `A` | `B` | `A + B` | `A × B` | `A → B` |
| --- | --- | --- | --- | --- |
| `inl(a)` | `inl(b)` | `inl(inl(a))` | `inl(a, b)` | `inl(λ x. b)` |
| `inl(a)` | `inr(g)` | `inl(inl(a))` | `inr(g ∘ pr2)` | `inr(λ h. g(h(a)))` |
| `inr(f)` | `inl(b)` | `inl(inr(b))` | `inr(f ∘ pr1)` | `inl(ex-falso ∘ f)` |
| `inr(f)` | `inr(g)` | `inr[f, g]` | `inr(f ∘ pr1)` | `inl(ex-falso ∘ f)` |

Since `A → B` is decidable whenever both `A` and `B` are decidable, it also
follows that the negation `¬ A` of any decidable type `A` is decidable.

## Example 8.1.4

Since the empty type and the unit type are both decidable types, it also follows
that the types `EqN(m, n)`, `m ≤ n` and `m < n` are decidable for each
`m, n : ℕ`.
The proofs in each of the three cases is by induction on `m` and `n`.

For instance, to show that `EqN(m, n)` is decidable for each `m, n : ℕ`, we
simply note that the types

```text
  EqN(0, 0)          ≐ 𝟙
  EqN(0, succ(n))    ≐ ∅
  EqN(succ(m), 0)    ≐ ∅
```

are all decidable, and that the type
`EqN(succ(m), succ(n)) ≐ EqN(m, n)` is decidable by the inductive hypothesis.

The fact that `ℕ` has decidable observational equality also implies that
equality itself is decidable on `ℕ`.
This leads to the general concept of decidable equality, which is important in
many results about decidability.

## Definition 8.1.5

We say that a type `A` has **decidable equality** if the identity type `x = y` is
decidable for every `x, y : A`.
We will write

```text
  has-decidable-equality(A) := Π(x y : A) is-decidable(x = y).
```

Before we show that `ℕ` has decidable equality, let us show that if `A ↔ B` and
`A` is decidable, then `B` must be decidable.

## Lemma 8.1.6

Consider two types `A` and `B`, and suppose that `A ↔ B`.
Then `A` is decidable if and only if `B` is decidable.

## Proof

Since we have functions `f : A → B` and `g : B → A` by assumption, we obtain by
contravariance of negation the functions

```text
  f̃ : ¬ B → ¬ A
  g̃ : ¬ A → ¬ B.
```

By functoriality of coproducts we therefore have the functions

```text
  f + g̃ : (A + ¬ A) → (B + ¬ B)
  g + f̃ : (B + ¬ B) → (A + ¬ A).
```

## Proposition 8.1.7

Equality on the natural numbers is decidable.

## Proof

Recall from Proposition 6.3.3 that we have

```text
  (m = n) ↔ EqN(m, n).
```

The claim therefore follows by Lemma 8.1.6, since we have observed in
Example 8.1.4 that `EqN(m, n)` is decidable for every `m, n : ℕ`.

It is certainly not provable with the given rules of type theory that every type
has decidable equality.
In fact, we will show later that if a type has decidable equality, then it is a
*set*.
However, it is also not provable that every set has decidable equality unless
one assumes the *law of excluded middle*.
We will discuss this principle in the later section on logic in type theory.
For now, it is important to remember that in order to use decidability, we must
first *prove that it holds*, and many familiar types do indeed have decidable
equality.

## Proposition 8.1.8

The standard finite type `Fin(k)` has decidable equality for each `k : ℕ`.

## Proof

Recall from Exercise 7.5 that we constructed an observational equality relation
`Eq-Fin_k` on `Fin(k)` for each `k : ℕ`, which satisfies

```text
  (x = y) ↔ Eq-Fin_k(x, y).
```

The type `Eq-Fin_k(x, y)` is decidable, since it is recursively defined using
the decidable types `∅` and `𝟙`.

We can use the fact that the finite types `Fin(k)` have decidable equality to
show that the divisibility relation on `ℕ` is decidable.

## Theorem 8.1.9

For any `d, x : ℕ`, the type `d | x` is decidable.

## Proof

Note that `0 | x` is decidable because `0 | x` if and only if `x = 0`, which is
decidable by Proposition 8.1.7.
Therefore it suffices to show that `d + 1 | x` is decidable.

By Theorem 7.4.7 it follows that `d + 1 | x` holds if and only if we have an
identification `[x]_(d + 1) = 0` in `Fin(d + 1)`.
Therefore the claim follows from the fact that `Fin(d + 1)` has decidable
equality.
