# Section 22.4 The fundamental group of the circle

```agda
module section-22-4-the-fundamental-group-of-the-circle where
```

<!-- rosetta-item: section-22.4 -->

We have two goals remaining in this book.
The first goal is to prove that the universal cover of the circle is an identity system at `base:S^1`, in the sense of Definition 11.2.1.
Since the universal cover is a family of sets over the circle, this implies that the circle is a `1`-type.

## Theorem 22.4.1

<!-- rosetta-item: theorem-22.4.1; latex-label: thm:eq-circle -->

The universal cover of the circle is an identity system at `base:S^1`.

### Proof

<!-- rosetta-item: subheading-22.4-proof -->

*Proof.* By Exercise 13.9 it suffices to show that the map
```text
f↦ f(0_{E}) : (Π(t:S^1) E_(S^1)(t)→ A(t))→ A(base)
```
is an equivalence for every type family `A` over the circle.
Note that we have a commuting triangle
<!-- rosetta-diagram: db32b26a0bf5; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
      [(Π(t:S^1) E_(S^1)(t)→ A(t))]
                    |
[Σ(h:ℤ→ A(base)) h∘succ-ℤ~ tr_A(loop)∘ h]---->[A(base)]

Arrows:
- (Π(t:S^1) E_(S^1)(t)→ A(t)) --unlabeled--> Σ(h:ℤ→ A(base)) h∘succ-ℤ~ tr_A(loop)∘ h
- (Π(t:S^1) E_(S^1)(t)→ A(t)) --f↦ f(0_{E})--> A(base)
- Σ(h:ℤ→ A(base)) h∘succ-ℤ~ tr_A(loop)∘ h --{(h,H)↦ h(0)}--> A(base)
```
in which the left map is the equivalence obtained in Corollary 22.2.4 and the bottom map is an equivalence by Corollary 22.3.6. ◻

<!-- rosetta-item-end: theorem-22.4.1 -->

## Corollary 22.4.2

<!-- rosetta-item: corollary-22.4.2 -->

The circle is a `1`-type and not a `0`-type.

### Proof

<!-- rosetta-item: subheading-22.4-proof-2 -->

*Proof.* To see that the circle is a `1`-type we have to show that `s=t` is a `0`-type for every `s,t:S^1`.
By Exercise 21.2 it suffices to show that the loop space of the circle is a `0`-type.
This is indeed the case, because `ℤ` is a `0`-type, and we have an equivalence `(base=base)≃ ℤ`.

Furthermore, since `ℤ` is a `0`-type and not a `(-1)`-type, it follows that the circle is a `1`-type and not a `0`-type. ◻

<!-- rosetta-item-end: corollary-22.4.2 -->

Our second goal is to construct a group isomorphism
```text
π_1(S^1)≅ ℤ.
```
However, Theorem 22.4.1 doesn’t immediately show that the fundamental group of the circle is `ℤ`.
It only gives us an equivalence
```text
Ω(S^1)≃ ℤ.
```
In order to compute the fundamental group of the circle we augment the fundamental theorem of identity types with the following proposition.

## Proposition 22.4.3

<!-- rosetta-item: proposition-22.4.3; latex-label: prp:fundamental-theorem-id-with-operation -->

Consider a type `A` equipped with a point `a:A`, and consider an identity system `B` on `A` at `a` equipped with `b:B(a)`.
Furthermore, suppose that there is a binary operation
```text
μ:B(a)→ (B(x)→ B(x))
```
for every `x:A`, equipped with a homotopy `μ(_,b)~ id`.
Then we have
```text
f(p ∙ q)=μ(f(p),f(q))
```
for the unique family of maps
```text
f:Π(x:A) (a=x)→ B(x)
```
such that `f(refl)=b`, and for every `p:a=a` and `q:a=x`.

### Proof

<!-- rosetta-item: subheading-22.4-proof-3 -->

*Proof.* Consider a family of maps `f:(a=x)→ B(x)` indexed by `x:A` such that `f(refl)=b`, and let `p:a=a` and `q:a=x`.
By induction on `q` it suffices to show that
```text
f(p)=μ(f(p),f(refl))
```
This follows, since `f(refl)=b` and `μ(f(p),b)=f(p)`. ◻

<!-- rosetta-item-end: proposition-22.4.3 -->

We are now ready to prove that the fundamental group of the circle is `ℤ`.
Recall from Definition 22.1.2 that we write `y↦ y_ℤ` for the inverse of the equivalence
```text
x↦ x_{E}:ℤ≃E_(S^1)(base).
```

## Theorem 22.4.4

<!-- rosetta-item: theorem-22.4.4; latex-label: thm:fundamental-group-circle -->

There is a group isomorphism
```text
π_1(S^1)≅ ℤ.
```

### Proof

<!-- rosetta-item: subheading-22.4-proof-4 -->

*Proof.* First we observe that, since the circle is a `1`-type, we have an isomorphism of groups `π_1(S^1)≅Ω(S^1)`.
In order to show that the group `Ω(S^1)` is isomorphic to `ℤ`, we prove that the family of equivalences
```text
α:Π(t:S^1) (base=t)→ E_(S^1)(t)
```
given by `α(refl)≔ 0_{E}` satisfies
```text
α(p ∙ q)_ℤ=α(p)_ℤ+α(q)_ℤ
```
for every `p,q:Ω(S^1)`.

To see that the claim holds, note that by Proposition 22.4.3 it suffices to construct a binary operation
```text
μ : E_(S^1)(base)→(E_(S^1)(x)→E_(S^1)(x))
```
equipped with a homotopy `μ(_,0_{E})~id`, such that
```text
μ(k_{E},l_{E})=(k+l)_{E}
```
holds for every `k,l:ℤ`.
Equivalently, it suffices to construct for each `k:ℤ` a function
```text
μ(k_{E}):E_(S^1)(x)→E_(S^1)(x)
```
indexed by `x:S^1` equipped with an identification `μ(k_{E},l_{E})=(k+l)_{E}` for each `k,l:ℤ`.
Since we have
```text
k+(l+1)=(k+l)+1
```
for all `k,l:ℤ`, such a function is obtained at once from Corollary 22.2.4. ◻

<!-- rosetta-item-end: theorem-22.4.4 -->

In order to prove that the fundamental group of the circle is `ℤ`, we first had to use the univalence axiom to construct the universal cover of the circle.
This proof was originally discovered by Mike Shulman in 2011, and later published in .
Its importance of this proof to the field of homotopy type theory is hard to overestimate.
The proof led to the discovery of the *encode-decode method*, which we presented in this book as the fundamental theorem of identity types, and it was the start of the field that is now sometimes called *synthetic homotopy theory*, where the induction principle for identity types and the univalence axiom are used along with methods from algebraic topology in order to compute algebraic invariants of types.
