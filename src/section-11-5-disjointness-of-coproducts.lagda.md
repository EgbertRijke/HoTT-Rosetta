# Section 11.5 Disjointness of coproducts

```agda
module section-11-5-disjointness-of-coproducts where
```

In our third application of the fundamental theorem of identity types, we
characterize the identity types of coproducts.
Our goal in this section is to prove the following theorem.

## Theorem 11.5.1

Let `A` and `B` be types.
Then there are equivalences

```text
  (inl(x) = inl(x')) ≃ (x = x')
  (inl(x) = inr(y')) ≃ ∅
  (inr(y) = inl(x')) ≃ ∅
  (inr(y) = inr(y')) ≃ (y = y')
```

for any `x, x' : A` and `y, y' : B`.

In order to prove Theorem 11.5.1, we first define a binary relation
`Eq-coprod_(A,B)` on the coproduct `A + B`.

## Definition 11.5.2

Let `A` and `B` be types.
We define

```text
  Eq-coprod_(A,B) : (A + B) → (A + B) → 𝕌
```

by double induction on the coproduct, postulating

```text
  Eq-coprod_(A,B)(inl(x), inl(x')) := x = x'
  Eq-coprod_(A,B)(inl(x), inr(y')) := ∅
  Eq-coprod_(A,B)(inr(y), inl(x')) := ∅
  Eq-coprod_(A,B)(inr(y), inr(y')) := y = y'.
```

The relation `Eq-coprod_(A,B)` is also called the **observational equality of
coproducts**.

## Lemma 11.5.3

The observational equality relation `Eq-coprod_(A,B)` on `A + B` is reflexive,
and therefore there is a map

```text
  Eq-coprod-eq :
    Π(s t : A + B) (s = t) → Eq-coprod_(A,B)(s, t).
```

## Construction

The reflexivity term `ρ` is constructed by induction on `t : A + B`, using

```text
  ρ(inl(x)) := refl(x) : Eq-coprod_(A,B)(inl(x), inl(x))
  ρ(inr(y)) := refl(y) : Eq-coprod_(A,B)(inr(y), inr(y)).
```

To show that `Eq-coprod-eq` is a family of equivalences, we will use the
fundamental theorem of identity types.
Therefore, we need to prove the following proposition.

## Proposition 11.5.4

For any `s : A + B` the total space

```text
  Σ(t : A + B) Eq-coprod_(A,B)(s, t)
```

is contractible.

## Proof

For convenience, let us write `E := Eq-coprod_(A,B)`.
By induction on `s`, it suffices to show that the total spaces

```text
  Σ(t : A + B) E(inl(x), t)
  Σ(t : A + B) E(inr(y), t)
```

are contractible.
The two proofs are similar, so we only prove that the type on the left is
contractible.
By the laws of coproducts and `Σ`-types, we compute

```text
  Σ(t : A + B) E(inl(x), t)
    ≃ (Σ(x' : A) E(inl(x), inl(x'))) +
      (Σ(y' : B) E(inl(x), inr(y')))
    ≃ (Σ(x' : A) x = x') + (Σ(y' : B) ∅)
    ≃ Σ(x' : A) x = x'.
```

The last type in this computation is contractible by Theorem 10.1.4, so we
conclude that the total space of `E(inl(x))` is contractible.

## Proof of Theorem 11.5.1

The proof is concluded with an application of Theorem 11.2.2, using
Proposition 11.5.4.
