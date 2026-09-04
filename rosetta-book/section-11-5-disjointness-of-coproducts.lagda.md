# Section 11.5 Disjointness of coproducts

```agda
module section-11-5-disjointness-of-coproducts where
```

<!-- rosetta-item: section-11.5 -->

In our third application of the fundamental theorem of identity types, we characterize the identity types of coproducts.
Our goal in this section is to prove the following theorem.

## Theorem 11.5.1

<!-- rosetta-item: theorem-11.5.1; latex-label: thm:id-coprod-compute -->

Let `A` and `B` be types.
Then there are equivalences
```text
(inl(x)=inl(x')) ≃ (x = x')
(inl(x)=inr(y')) ≃ empty
(inr(y)=inl(x')) ≃ empty
(inr(y)=inr(y')) ≃ (y=y')
```
for any `x,x':A` and `y,y':B`.

<!-- rosetta-item-end: theorem-11.5.1 -->

In order to prove Theorem 11.5.1, we first define a binary relation `Eq-coproduct_{A,B}` on the coproduct `A+B`.

## Definition 11.5.2

<!-- rosetta-item: definition-11.5.2 -->

Let `A` and `B` be types.
We define
```text
Eq-coproduct_{A,B} : (A+B)→ (A+B)→𝒰
```
by double induction on the coproduct, postulating
```text
Eq-coproduct_{A,B}(inl(x),inl(x')) ≔ (x=x')
Eq-coproduct_{A,B}(inl(x),inr(y')) ≔ empty
Eq-coproduct_{A,B}(inr(y),inl(x')) ≔ empty
Eq-coproduct_{A,B}(inr(y),inr(y')) ≔ (y=y').
```
The relation `Eq-coproduct_{A,B}` is also called the **observational equality of coproducts**.

<!-- rosetta-item-end: definition-11.5.2 -->

## Lemma 11.5.3

<!-- rosetta-item: lemma-11.5.3 -->

The observational equality relation `Eq-coproduct_{A,B}` on `A+B` is reflexive, and therefore there is a map
```text
Eq-coproduct-eq:Π(s,t:A+B) (s=t)→ Eq-coproduct_{A,B}(s,t).
```

### Construction

<!-- rosetta-item: subheading-11.5-construction -->

The reflexivity term `ρ` is constructed by induction on `t:A+B`, using
```text
ρ(inl(x))≔ refl : Eq-coproduct_{A,B}(inl(x),inl(x))
ρ(inr(y))≔ refl : Eq-coproduct_{A,B}(inr(y),inr(y)).
```

<!-- rosetta-item-end: lemma-11.5.3 -->

To show that `Eq-coproduct-eq` is a family of equivalences, we will use the fundamental theorem of identity types, Theorem 11.2.2.
Therefore, we need to prove the following proposition.

## Proposition 11.5.4

<!-- rosetta-item: proposition-11.5.4; latex-label: lem:is-contr-total-eq-coprod -->

For any `s:A+B` the total space
```text
Σ(t:A+B) Eq-coproduct_{A,B}(s,t)
```
is contractible.

### Proof

<!-- rosetta-item: subheading-11.5-proof -->

*Proof.* For convenience, let us write `E≔ Eq-coproduct_{A,B}`.
By induction on `s`, it suffices to show that the total spaces
```text
Σ(t:A+B) E(inl(x),t) and Σ(t:A+B) E(inr(y),t)
```
are contractible.
The two proofs are similar, so we only prove that the type on the left is contractible.
By the laws of coproducts and `Σ`-types given in Examples 9.2.9 and 9.2.10, we simply compute

```text
Σ(t:A+B) E(inl(x),t)
≃ (Σ(x':A) E(inl(x),inl(x')))+(Σ(y':B) E(inl(x),inr(y')))
≃ (Σ(x':A) x=x')+(Σ(y':B) empty)
≃ Σ(x':A) x=x'.
```

The last type in this computation is contractible by Theorem 10.1.4, so we conclude that the total space of `E(inl(x))` is contractible. ◻

<!-- rosetta-item-end: proposition-11.5.4 -->

### Proof

<!-- rosetta-item: subheading-11.5-proof-2 -->

*Proof of Theorem 11.5.1.* The proof is now concluded with an application of Theorem 11.2.2, using Proposition 11.5.4. ◻
