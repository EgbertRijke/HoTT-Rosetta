# Section 18.2 The universal property of set quotients

```agda
module section-18-2-the-universal-property-of-set-quotients where
```

<!-- rosetta-item: section-18.2 -->

The quotient `A/R` is constructed as the image of `R`, so we obtain a commuting triangle
<!-- rosetta-diagram: d1f85deb09a0; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                     [A/R]

          [Prop_𝒰^A]

Arrows:
- A --q_R--> A/R
- A --R--> Prop_𝒰^A
- A/R --i_R--> Prop_𝒰^A
```
and the embedding `i_R:A/R→Prop_𝒰^A` satisfies the universal property of the image of `R`.
This universal property is, however, not the usual universal property of the quotient.

## Definition 18.2.1

<!-- rosetta-item: definition-18.2.1 -->

Consider a map `q:A→ B` into a set `B` satisfying the property that
```text
R(x,y)→ (q(x)=q(y))
```
for all `x,y:A`.
We say that `q:A→ B` **is a set quotient** of `R`, or that `q` satisfies the **universal property of the set quotient by `R`**, if for every map `f:A→ X` into a set `X` such that `f(x)=f(y)` whenever `R(x,y)` holds, there is a unique extension
<!-- rosetta-diagram: 9f23c3a8d7a4; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
 [B] ----> [X]

Arrows:
- A --q--> B
- A --f--> X
- B --unlabeled--> X
```

<!-- rosetta-item-end: definition-18.2.1 -->

## Remark 18.2.2

<!-- rosetta-item: remark-18.2.2 -->

Formally, we express the universal property of the quotient by `R` as follows.
Consider a map `q:A→ B` that satisfies the property that
```text
H:Π(x,y:A) R(x,y)→ (f(x)=f(y)).
```
Then there is for any set `X` a map
```text
q^⋆:(B→ X) → (Σ(f:A→ X) Π(x,y:A) R(x,y)→ (f(x)=f(y))).
```
This map takes a function `h:B→ X` to the pair
```text
q^⋆(h)≔(h∘ q,λ x. λ y. λ r. ap_{h}(H_{x,y}(r))).
```
The universal property of the set quotient of `R` asserts that the map `q^⋆` is an equivalence for every set `X`.
It is important to note that the universal property of set quotients is formulated with respect to sets.

<!-- rosetta-item-end: remark-18.2.2 -->

## Theorem 18.2.3

<!-- rosetta-item: theorem-18.2.3; latex-label: thm:quotient_up -->

Consider a type `A` and a universe `𝒰` containing `A`.
Furthermore, let `R:A→ (A→ Prop_𝒰)` be an equivalence relation, and consider a map `q:A→ B` into a set `B`, not necessarily in `𝒰`.
Then the following are equivalent.

1.  The map `q` satisfies the property that
```text
q(x)=q(y)
```
    for every `x,y:A` for which `R(x,y)` holds, and moreover `q` satisfies the universal property of the set quotient of `R`.

2.  The map `q` is surjective and **effective**, which means that for each `x,y:A` we have an equivalence
```text
(q(x)=q(y))≃ R(x,y).
```

3.  The map `R:A→ (A→ Prop_𝒰)` extends along `q` to an embedding
<!-- rosetta-diagram: 797f891ee8ed; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                      [B]

          [Prop_𝒰^A]

Arrows:
- A --q--> B
- A --R--> Prop_𝒰^A
- B --i--> Prop_𝒰^A
```
    and the embedding `i` satisfies the universal property of the image inclusion of `R`.

<!-- rosetta-item-end: theorem-18.2.3 -->

In Theorem 18.2.3 we don’t assume that `B` is in the same universe as `A` and `R`, because we want to apply it to `B≔im(R)`.
As we will see below, this extra generality only affects the proof that (2) implies (3).

### Proof

<!-- rosetta-item: subheading-18.2-proof -->

*Proof.* We first show that (2) is equivalent to (3), since this is the easiest part.
After that, we will show that (1) is equivalent to (2).

Assume that (3) holds.
Then `q` is surjective by Theorem 15.2.5.
Moreover, we have
```text
R(x,y) ≃ R(x)=R(y)
≃ i(q(x))=i(q(y))
≃ q(x)=q(y)
```
In this calculation, the first equivalence holds by Corollary 18.1.4; the second equivalence holds since we have a homotopy `R~ i∘ q`; and the third equivalence holds since `i` is an embedding.
This completes the proof that (3) implies (2).

Next, we show that (2) implies (3).
First, we want to define a map
```text
i:B→Prop_𝒰^A.
```
We would like to define `i(b,a):=(b=q(a))`.
This direct definition does not go through, however, because the type `B` is not assumed to be in `𝒰`.
Nevertheless, observe that by the assumption that `q` is surjective and effective, the type `B` is locally `𝒰`-small.
To see this, first note that `is-small_U(X)` is a proposition for any type `X` by Proposition 17.1.5.
Using the assumption that `q` is surjective, it follows from Proposition 15.2.3 that it suffices to show that `q(a)=q(a')` is `𝒰`-small for each `a,a':A`.
This follows by the assumption that `q` is effective.
In particular, the identity type `b=q(a)` is a `𝒰`-small proposition, for every `b:B` and `a:A`.
Let us write `s(b,a)` for the element of type `is-small_𝒰(b=q(a))`.

Now consider a universe `𝒱` containing `B`.
Then we can define a map
```text
j:B→(A→Σ(P:Prop_𝒱) is-small_𝒰(P))
```
by `j(b,a):=(b=q(a),s(b,a))`, and now we obtain `i` from `j` by defining
```text
i(b,a):=pr 1(s(b,a)).
```
Note that we have an equivalence `i(b,a)≃ (b=q(a))` for every `b:B` and `a:A`.
Then the triangle
<!-- rosetta-diagram: 8e0efc997c73; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                      [B]

          [Prop_𝒰^A]

Arrows:
- A --q--> B
- A --R--> Prop_𝒰^A
- B --i--> Prop_𝒰^A
```
commutes, since we have an equivalence
```text
i(q(a),a') ≃ (q(a)=q(a')) ≃ R(a,a')
```
for each `a,a':A`.
To show that `i` is an embedding, recall from Exercise 12.3 that it suffices to show that `i` is injective, i.e., that
```text
Π(b,b':B) (i(b)=i(b'))→ (b=b'),
```
since the codomain of `i` is a set by Theorem 17.2.3.
Note that injectivity of a map into a set is a property, and that `q` is assumed to be surjective.
Hence by Proposition 15.2.3 it is sufficient to show that
```text
Π(a,a':A) (i(q(a))=i(q(a')))→ (q(a)=q(a')).
```
Since `R~ i∘ q`, and `q(a)=q(a')` is assumed to be equivalent to `R(a,a')`, it suffices to show that
```text
Π(a,a':A) (R(a)=R(a'))→ R(a,a'),
```
which follows directly from Corollary 18.1.4.
Thus we have shown that the factorization `R~ i∘ q` factors `R` as a surjective map followed by an embedding.
We conclude by Theorem 15.2.5 that the embedding `i` satisfies the universal property of the image factorization of `R`, which finishes the proof that (2) implies (3).

Now we show that (1) implies (2).
To see that `q` is surjective if it satisfies the assumptions in (1), consider the image factorization
<!-- rosetta-diagram: c9146daeb855; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                [im(q)]

           [B]

Arrows:
- A --q--> B
- A --q_q--> im(q)
- im(q) --i_q--> B
```
We claim that the map `i_q` has a section.
To see this, we first note that we have
```text
q_q(x)=q_q(y)
```
for any `x,y:A` satisfying `R(x,y)`, because if `R(x,y)` holds, then `q(x)=q(y)` and hence `i_q(q_q(x))=i_q(q_q(y))` holds and `i_q` is an embedding.
Since `im(q)` is a set, we may apply the universal property of `q` and we obtain a unique extension of `q_q` along `q`
<!-- rosetta-diagram: 0eaefd3b448e; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
 [B] ---->[im(q)]

Arrows:
- A --q--> B
- A --q_q--> im(q)
- B --h--> im(q)
```
Now we observe that the composite `i_q∘ h` is an extension of `q` along `q`, so it must be the identity function by uniqueness.
Thus we have established that `h` is a section of `i_q`.
Since `i_q` is an embedding with a section, it follows that `i_q` is an equivalence.
We conclude that `q` is surjective, because `q` is the composite `i_q∘ q_q` of a surjective map followed by an equivalence.

Now we have to show that the map `q` is effective, i.e., that `q(x)=q(y)` is equivalent to `R(x,y)` for every `x,y:A`.
We first apply the universal property of `q` to obtain for each `x:A` an extension of `R(x)` along `q`
<!-- rosetta-diagram: 2127350a0b33; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
 [B] ---->[Prop_𝒰]

Arrows:
- A --q--> B
- A --R(x)--> Prop_𝒰
- B --R̃(x)--> Prop_𝒰
```
Since the triangle commutes, we have an equivalence `R̃(x,q(x'))≃ R(x,x')` for each `x':A`.
Now we apply Theorem 11.2.2 to see that the canonical family of maps
```text
Π(y:B) (q(x)=y)→ R̃(x,y)
```
is a family of equivalences.
Thus, we need to show that the type `Σ(y:B) R̃(x,y)` is contractible.
For the center of contraction, note that we have `q(x):B`, and the type `R̃(x,q(x))` is equivalent to the type `R(x,x)`, which is inhabited by reflexivity of `R`.
To construct the contraction, it suffices to show that
```text
Π(y:B) R̃(x,y)→ (q(x)=y).
```
Since this is a property, and since we have already shown that `q` is a surjective map, we may apply Proposition 15.2.3, by which it suffices to show that
```text
Π(x':A) R̃(x,q(x'))→ (q(x)=q(x')).
```
Since `R̃(x,q(x'))≃ R(x,x')`, this is immediate from our assumption on `q`.
Thus we obtain the contraction, and we conclude that we have an equivalence `R̃(x,y)≃ (q(x)=y)` for each `y:B`.
It follows that we have an equivalence
```text
R(x,y)≃ (q(x)=q(y))
```
for each `x,y:A`, which completes the proof that (1) implies (2).

It remains to show that (2) implies (1).
Assume (2), and let `f:A→ X` be a map into a set `X`, satisfying the property that
```text
Π(a,a':A) R(a,a')→ (f(a)=f(a')).
```
Our goal is to show that the type of extensions of `f` along `q` is contractible.
By Exercise 17.5 it follows that there is at most one such an extension, so it suffices to construct one.

In order to construct an extension, we will construct for every `b:B` a term `x:X` satisfying the property
```text
P(x)≔ ∃_{(a:A)}(f(a)=x)∧ (q(a)=b).
```
Before we make this construction, we first observe that there is at most one such `x`, i.e., that the type of `x:X` satisfying `P(x)` is in fact a proposition.
To see this, we need to show that `x=x'` for any `x,x':X` satisfying `P(x)` and `P(x')`.
Since `X` is assumed to be a set, our goal of showing that `x=x'` is a property.
Therefore we may assume that we have `a,a':A` satisfying
```text
f(a) = x q(a) = b
f(a') = x' q(a') = b.
```
It follows from these assumptions that `q(a)=q(a')`, and hence that `R(a,a')` holds.
This in turn implies that `f(a)=f(a')`, and hence that `x=x'`.

Now let `b:B`.
Our goal is to construct an `x:X` that satisfies the property
```text
∃_{(a:A)}(f(a)=x)∧ (q(a)=b).
```
Since `q` is assumed to be surjective, we have `‖fib(q, b)‖`.
Moreover, since we have shown that at most one `x:X` exists with the asserted property, we get to assume that we have `a:A` satisfying `q(a)=b`.
Now we see that `x≔ f(a)` satisfies the desired property.

Thus, we obtain a function `h:B→ X` satisfying the property that for all `b:B` there exists an `a:A` such that
```text
f(a)=h(b) and q(a)=b.
```
In particular, it follows that `h(q(a))=f(a)` for all `a:A`, which completes the proof that (2) implies (1). ◻

## Corollary 18.2.4

<!-- rosetta-item: corollary-18.2.4 -->

Consider an equivalence relation `R` over a type `A`.
Then the quotient map
```text
q:A→ A/R
```
is surjective and effective, and it satisfies the universal property of the set quotient.

<!-- rosetta-item-end: corollary-18.2.4 -->

Theorem 18.2.3 can be used to show that the type of equivalence relations is equivalent to the type of sets `X` equipped with a surjective map `A↠ X`.
This may seem remarkable if you haven’t tried Exercise 17.18 yet, because at first glance one might think that the type of sets `X` equipped with a surjective map `A↠ X` is a `1`-type, while the type of equivalence relations on `A` is a set.

## Theorem 18.2.5

<!-- rosetta-item: theorem-18.2.5; latex-label: thm:eqrel-surj -->

For any type `A` and any universe `𝒰` containing `A`, we have an equivalence
```text
Eq-Rel_𝒰(A)≃Σ(X:Set_𝒰) A↠ X.
```

### Proof

<!-- rosetta-item: subheading-18.2-proof-2 -->

*Proof.* Given an equivalence relation `R:A→(A→Prop_𝒰)` on `A` we first use the replacement axiom, by which the set quotient `A/R` is `𝒰`-small, to obtain a set `Q(R):Set_𝒰`, an equivalence `e:Q(R)≃ A/R`, and a surjective map `f:A→ Q(R)` such that the triangle
<!-- rosetta-diagram: 8b841b2da315; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
            [A]

[Q(R)]               [A/R]

Arrows:
- A --f--> Q(R)
- A --q--> A/R
- Q(R) --e--> A/R
```
commutes.
This defines a map
```text
Q_A:Eq-Rel_𝒰(A)→Σ(X:Set_𝒰) A↠ X.
```
The map `K_A:(Σ(X:Set_𝒰) A↠ X)→Eq-Rel_𝒰(A)` is given by
```text
K_A(X,f,x,y)≔ K_f(x,y) ≔ (f(x)=f(y)).
```
Note that `K_f` is valued in propositions because `X` is assumed to be a set, and obviously it is an equivalence relation.

To see that `K_A(Q_A(R))=R` note that by function extensionality and propositional extensionality it follows that two equivalence relations `R` and `S` on `A` are equal if and only if `R(x,y)↔ S(x,y)` for all `x,y:A`.
Note that `K_A(Q_A(R))(x,y)↔ R(x,y)` holds for all `x,y:A` if and only if `(q_R(x)=q_R(y))↔ R(x,y)` holds for all `x,y:A`.
This follows from Corollary 18.1.4.

It remains to show that `Q_A(K_A(X,f))=(X,f)`.
Note that the type of identifications `(Y,g)=(X,f)` is by the univalence axiom equivalent to the type
```text
Σ(e:Y≃ X) e∘ g~ f.
```
Therefore it suffices to construct a commuting triangle
<!-- rosetta-diagram: d0898d6829c9; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
             [A]

[A/K_f]                [X]

Arrows:
- A --q_{K_f}--> A/K_f
- A --f--> X
- A/K_f --unlabeled--> X
```
We obtain such an equivalence by combining Theorem 18.2.3 and Theorem 15.1.8. ◻

<!-- rosetta-item-end: theorem-18.2.5 -->
