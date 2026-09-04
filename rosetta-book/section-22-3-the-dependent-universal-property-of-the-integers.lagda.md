# Section 22.3 The (dependent) universal property of the integers

```agda
module section-22-3-the-dependent-universal-property-of-the-integers where
```

<!-- rosetta-item: section-22.3 -->

The dependent universal property precisely characterizes sections of families over the integers, for those families `A(k)` indexed by `k:ℤ` that come equipped with families of equivalences `A(k)≃ A(k+1)` for all `k:ℤ`.

## Lemma 22.3.1

<!-- rosetta-item: lemma-22.3.1; latex-label: lem:elim-Z -->

Let `B` be a family over `ℤ`, equipped with an element `b_0:B(0)`, and an equivalence
```text
e_k : B(k)≃ B(succ-ℤ(k))
```
for each `k:ℤ`.
Then there is a dependent function `f:Π(k:ℤ) B(k)` equipped with identifications `f(0)=b_0` and
```text
f(succ-ℤ(k))=e_k(f(k))
```
for any `k:ℤ`.

### Proof

<!-- rosetta-item: subheading-22.3-proof -->

*Proof.* The map is defined using the induction principle for the integers, stated in Remark 4.5.2.
First we take
```text
f(-1) ≔ e_{-1}^{-1}(b_0)
f(0) ≔ b_0
f(1) ≔ e_0(b_0).
```
For the induction step on the negative integers we use
```text
λ n. e_{in-neg(succ-ℕ(n))}^{-1} : Π(n:ℕ) B(in-neg(n))→ B(in-neg(succ-ℕ(n)))
```
For the induction step on the positive integers we use
```text
λ n. e_{in-pos(n)} : Π(n:ℕ) B(in-pos(n))→ B(in-pos(succ-ℕ(n))).
```
The computation rules follow in a straightforward way from the computation rules of `ℤ`-induction and the fact that `e^{-1}` is an inverse of `e`. ◻

<!-- rosetta-item-end: lemma-22.3.1 -->

## Example 22.3.2

<!-- rosetta-item: example-22.3.2 -->

For any type `A`, we obtain a map `f:ℤ→ A` from any `x:A` and any equivalence `e:A ≃ A`, such that `f(0)=x` and the square
<!-- rosetta-diagram: 60bbb0d8b9e0; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [ℤ] ----> [A]
  |         |
 [ℤ] ----> [A]

Arrows:
- ℤ --succ-ℤ--> ℤ
- ℤ --f--> A
- A --e--> A
- ℤ --f--> A
```
commutes.
In particular, if we take `A≔ (x=x)` for some `x:X`, then for any `p:x=x` we have the equivalence `λ q. p ∙ q:(x=x)→ (x=x)`.
This equivalence induces a map
```text
k↦ p^k : ℤ → (x=x),
```
for any `p:x=x`.
This induces the **degree `k` map** on the circle
```text
deg(k) : S^1→S^1,
```
for any `k:ℤ`, see Exercise 22.2.

<!-- rosetta-item-end: example-22.3.2 -->

In the following proposition we show that the dependent function constructed in Lemma 22.3.1 is unique.
This is the **dependent universal property of the integers**.

## Proposition 22.3.3

<!-- rosetta-item: proposition-22.3.3; latex-label: prp:unique-elim-Z -->

Consider a type family `B:ℤ→𝒰` equipped with `b:B(0)` and a family of equivalences
```text
e:Π(k:ℤ) B(k) ≃ B(succ-ℤ (k)).
```
Then the type
```text
Σ(f:Π(k:ℤ) B(k)) (f(0)=b)×Π(k:ℤ) f(succ-ℤ (k))=e_k(f(k))
```
is contractible.

### Proof

<!-- rosetta-item: subheading-22.3-proof-2 -->

*Proof.* In Lemma 22.3.1 we have already constructed an element of the asserted type.
Therefore it suffices to show that any two elements of this type can be identified.
Note that the type `(f,p,H)=(f',p',H')` is equivalent to the type of triples `(K,α,β)` consisting of
```text
K : f~ f'
α : K(0)=p ∙ (p')^{-1}
β : Π(k:ℤ) K(succ-ℤ (k))=(H(k) ∙ ap_{e_k}(K(k))) ∙ H'(k)^{-1}.
```
We obtain such a triple by applying Lemma 22.3.1 to the family `C` over `ℤ` given by `C(k)≔ f(k)=f'(k)`, which comes equipped with the base point
```text
p ∙ (p')^{-1} : C(0),
```
and the family of equivalences
```text
Π(k:ℤ) C(k) ≃ C(succ-ℤ (k))
```
given by `r↦ (H(k) ∙ ap_{e_k}(r)) ∙ H'(k)^{-1}`. ◻

<!-- rosetta-item-end: proposition-22.3.3 -->

The **universal property of the integers** is a simple corollary of the dependent universal property.
One way of phrasing it is that `ℤ` is the *initial type equipped with a point and an automorphism*.

## Corollary 22.3.4

<!-- rosetta-item: corollary-22.3.4 -->

For any type `X` equipped with a base point `x_0:X` and an automorphism `e:X ≃ X`, the type
```text
Σ(f:ℤ→ X) (f(0)=x_0)× ((f ∘ succ-ℤ )~(e∘ f))
```
is contractible.

<!-- rosetta-item-end: corollary-22.3.4 -->

Using the fact that equivalences are contractible maps, we can reformulate the dependent universal property of the integers as follows.

## Theorem 22.3.5

<!-- rosetta-item: theorem-22.3.5 -->

For any type family `A` over `ℤ` equipped with a family of equivalences
```text
e:Π(k:ℤ) A(k)≃ A(succ-ℤ(k)),
```
the map
```text
ev_0:(Σ(f:Π(k:ℤ) A(k)) Π(k:ℤ) f(succ-ℤ(k))=e_k(f(k)))→ A(0)
```
given by `(f,H)↦ f(0)` is an equivalence.

### Proof

<!-- rosetta-item: subheading-22.3-proof-3 -->

*Proof.* Note that the fibers of `ev_0` are equivalent to the types that are shown to be contractible in Proposition 22.3.3. ◻

<!-- rosetta-item-end: theorem-22.3.5 -->

The following corollary will be used to prove that the fundamental cover of the circle is equivalent to the identity type based at `base:S^1`.

## Corollary 22.3.6

<!-- rosetta-item: corollary-22.3.6; latex-label: cor:universal-property-Z -->

For any type `X` equipped with an equivalence `e:X≃ X`, the map
```text
(Σ(f:ℤ→ X) f∘ succ-ℤ ~ e∘ f)→ X
```
given by `(f,H)↦ f(0)` is an equivalence.

<!-- rosetta-item-end: corollary-22.3.6 -->
