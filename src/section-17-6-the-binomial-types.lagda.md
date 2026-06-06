# Section 17.6 The binomial types

```agda
module section-17-6-the-binomial-types where
```

To wrap up this section on univalence, we will use the univalence axiom to
construct for any two types `A` and `B` a type `binom(A, B)` that has
properties similar to the binomial coefficients.
Indeed, we will show that if `A` is an `n`-element type and `B` is a
`k`-element type, then `binom(A, B)` is a `binom(n, k)`-element type.
The binomial types are defined using decidable embeddings.

## Definition 17.6.1

A map `f : A → B` is said to be **decidable** if it comes equipped with an
element of type

```text
  is-decidable(f) := Π(b : B) is-decidable(fib(f, b)).
```

We will write `A ↪ᵈ B` for the type of **decidable embeddings** from `A` to
`B`, i.e., for the type of embeddings that are also decidable maps.

## Definition 17.6.2

Consider a type `A` and a universe `𝒰`.
We define the **connected component** of `𝒰` at `A` by

```text
  𝒰_A := Σ(X : 𝒰) ∥ A ≃ X ∥.
```

## Example 17.6.3

Note that type `𝒰_{Fin(n)}` is the type `BS_n` of all `n`-element types.
Note also that if `A ≃ B`, then `𝒰_A ≃ 𝒰_B`.

## Definition 17.6.4

Consider two types `A` and `B` and a universe `𝒰` containing both `A` and `B`.
We define the **binomial type** `binom_𝒰(A, B)` by

```text
  binom_𝒰(A, B) := Σ(X : 𝒰_B) X ↪ᵈ A.
```

## Remark 17.6.5

We define the binomial types using decidable embeddings because the usual
properties of binomial coefficients generalize most naturally under the extra
assumption of decidability.
In particular the binomial theorem for types, which is stated as
Exercise `ex:binomial-theorem` and generalized in Exercise
`ex:distributive-pi-coprod`, rely on the use of decidable embeddings.

## Proposition 17.6.6

Consider two types `A` and `B`, and a universe `𝒰` containing both `A` and `B`.
Then we have an equivalence

```text
  binom_𝒰(A, B) ≃
  Σ(P : A → decidable-Prop_𝒰) ∥ B ≃ Σ(a : A) P(a) ∥
```

from the binomial type `binom_𝒰(A, B)` to the type of decidable subtypes of `A`
that are merely equivalent to `B`.

## Proof

This equivalence follows from Theorem 17.4.2, by which we have

```text
  (Σ(X : 𝒰) X ↪ᵈ A) ≃ (A → decidable-Prop_𝒰).
```

## Remark 17.6.7

Combining Corollary 17.2.4 and Proposition 17.6.6, we obtain an equivalence

```text
  binom_𝒰(A, B) ≃
  Σ(f : A → bool) ∥ B ≃ Σ(a : A) f(a) = true ∥
```

for any universe `𝒰` that contains both `A` and `B`.
This equivalence is important, because the right hand side does not depend on
the universe `𝒰`.
Therefore we will simply write `binom(A, B)` for `binom_𝒰(A, B)`, if the
universe `𝒰` contains both `A` and `B`.

## Lemma 17.6.8

For any two types `A` and `B`, we have equivalences

```text
  binom(empty, empty)       ≃ unit
  binom(A + unit, empty)   ≃ unit
  binom(empty, B + unit)   ≃ empty
  binom(A + unit, B + unit) ≃ binom(A, B) + binom(A, B + unit).
```

## Proof

For the first two equivalences, we prove that `binom(X, empty)` is contractible
for any type `X`.
To see this, we first note that the type `𝒰_empty` is contractible.
Indeed, at the center of contraction we have the empty type, and any two types
that are merely equivalent to the empty type are empty and hence equivalent.
Therefore it follows that

```text
  binom(X, empty) ≃ empty ↪ᵈ X.
```

The type of decidable embeddings `empty ↪ᵈ X` is contractible, because the type
`empty → X` is contractible with the map `ex-falso : empty → X` at the center
of contraction, which is of course a decidable embedding.

Next, the fact that the binomial type `binom(empty, B + unit)` is empty follows
from the fact that the type of maps `X → empty` is empty for any type `X`
merely equivalent to `B + unit`.

For the last equivalence we use Proposition 17.6.6.
Using the universal property of `A + unit`, we see that

```text
  binom(A + unit, B + unit) ≃
  Σ(P : A → decidable-Prop_𝒰) Σ(Q : decidable-Prop_𝒰)
    ∥ (B + unit) ≃ (Σ(a : A) P(a) + Q) ∥.
```

Using the fact that `decidable-Prop_𝒰 ≃ Fin(2)`, observe that we have an
equivalence

```text
  Σ(Q : decidable-Prop_𝒰) ∥ (B + unit) ≃ (Σ(a : A) P(a) + Q) ∥
    ≃ ∥ (B + unit) ≃ (Σ(a : A) P(a) + unit) ∥
      + ∥ (B + unit) ≃ Σ(a : A) P(a) ∥.
```

Furthermore, it follows from Proposition 16.2.1 that

```text
  ∥ (B + unit) ≃ (Σ(a : A) P(a) + unit) ∥ ≃
  ∥ B ≃ Σ(a : A) P(a) ∥.
```

Thus we see that

```text
  binom(A + unit, B + unit) ≃
  (Σ(P : A → decidable-Prop_𝒰) ∥ B ≃ Σ(a : A) P(a) ∥) +
  (Σ(P : A → decidable-Prop_𝒰) ∥ (B + unit) ≃ Σ(a : A) P(a) ∥).
```

## Theorem 17.6.9

If `A` and `B` are finite types of cardinality `n` and `k`, respectively, then
the type `binom(A, B)` is finite of cardinality `binom(n, k)`.

## Proof

The claim that the type `binom(A, B)` is finite of cardinality `binom(n, k)` is
a proposition, so we may assume `e : Fin(n) ≃ A` and `f : Fin(k) ≃ B`.
The claim now follows by induction on `n` and `k`, using Lemma 17.6.8.

## Remark 17.6.10

It is perhaps remarkable that the type `Σ(X : 𝒰_B) X ↪ᵈ A` is a good
generalisation of the binomial coefficients to types.
Note that when `A` and `B` are finite types of cardinality `n` and `k`,
respectively, then the type `B ↪ᵈ A` has a factor `k!` too many elements.
When we seemingly enlarge it by the type `𝒰_B` of all types merely equivalent
to `B`, it turns out that we obtain the correct generalisation of the binomial
coefficients.

One reason why it works is that the identity type of `Σ(X : 𝒰_B) X ↪ᵈ A` is
characterized, via the univalence axiom, by

```text
  ((X, f) = (Y, g)) ≃ Σ(e : X ≃ Y) f ~ g ∘ e.
```

Therefore it follows that for any two decidable embeddings `f g : B ↪ᵈ A`, if
`f` and `g` are the same up to a permutation on `B`, then we get an
identification `(B, f) = (B, g)` in the type `Σ(X : 𝒰_B) X ↪ᵈ A`.

From a group theoretic perspective we may observe that the automorphism group
`B ≃ B` acts freely on the set of decidable embeddings `B ↪ᵈ A`, and the type
`Σ(X : 𝒰_B) X ↪ A` can be viewed as the type of orbits of that action.
Since this action of `Aut(B)` on `B ↪ᵈ A` is free, we see that the number of
orbits is `1 / k!` times the number of elements in `B ↪ᵈ A`.
