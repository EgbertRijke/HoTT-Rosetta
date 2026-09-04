# Section 22.1 The universal cover of the circle

```agda
module section-22-1-the-universal-cover-of-the-circle where
```

<!-- rosetta-item: section-22.1 -->

The type of small families over `S^1` is just the function type `S^1→𝒰`.
Therefore, we may use the universal property of the circle to construct type families over the circle.

By the universal property, `𝒰`-small type families over `S^1` are equivalently described as pairs `(X,p)` consisting of a type `X:𝒰` and an identification `p:X=X`.
The univalence axiom implies that the map
```text
eq-equiv_{X,X}:(X ≃ X)→ (X=X)
```
is an equivalence.
Therefore, type families over the circle are equivalently described as pairs `(X,e)`, consisting of a type `X` and an equivalence `e:X ≃ X`.
The type `Σ(X:𝒰) X ≃ X` is also called the type of **descent data** for the circle.

## Definition 22.1.1

<!-- rosetta-item: definition-22.1.1; latex-label: defn:circle_descent -->

Consider a type `X` and an equivalence `e:X ≃ X`.
We will construct a dependent type `D(X,e):S^1→𝒰` equipped with an equivalence `x↦ x_{D}:X ≃ D(X,e,base)` for which the square
<!-- rosetta-diagram: a78002d01419; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[D(X,e,base)]
  |             |
 [X] ---->[D(X,e,base)]

Arrows:
- X --≃--> D(X,e,base)
- X --e--> X
- D(X,e,base) --tr_{D(X,e)}(loop)--> D(X,e,base)
- X --≃--> D(X,e,base)
```
commutes.
We will write `d↦ d_{X}` for the inverse of this equivalence, so that the relations

```text
(x_{D})_X =x (e(x)_{D}) = tr_{D(X,e)}(loop,x_{D})
(d_X)_{D} =d (tr_{D(X,e)}(d))_X = e(d_X)
```

hold.

### Construction

<!-- rosetta-item: subheading-22.1-construction -->

An easy path induction argument reveals that
```text
equiv-eq(ap_{P}(loop))=tr_P(loop)
```
for each dependent type `P:S^1→𝒰`.
Therefore we see that the triangle
<!-- rosetta-diagram: c05da5733c3e; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
                 [(S^1→ 𝒰)]

[Σ(X:𝒰) X=X]                    [Σ(X:𝒰) X ≃ X]

Arrows:
- (S^1→ 𝒰) --gen_{S^1}--> Σ(X:𝒰) X=X
- (S^1→ 𝒰) --desc_{S^1}--> Σ(X:𝒰) X ≃ X
- Σ(X:𝒰) X=X --tot(λ X. equiv-eq_{X,X})--> Σ(X:𝒰) X ≃ X
```
commutes, where the map `desc_{S^1}` is given by `P↦(P(base),tr_P(loop))` and the bottom map is an equivalence by the univalence axiom and Theorem 11.1.3.
Now it follows by the 3-for-2 property that `desc_{S^1}` is an equivalence, since `gen_{S^1}` is an equivalence by Theorem 21.2.3.
This means that for every type `X` and every `e:X ≃ X` there is a type family `D(X,e):S^1→𝒰` equipped with an identification
```text
(D(X,e,base),tr_{D(X,e)}(loop))=(X,e).
```
For convenience, we invert this identification.
Now we observe that the type of identifications in `Σ(X:𝒰) X ≃ X` can be characterized by
```text
((X,e)=(X',e'))≃ Σ(α:X≃ X') e'∘ α~ α∘ e'.
```
This implies that we obtain an equivalence `x↦ x_{D}:X≃ D(X,e,base)` such that the square
<!-- rosetta-diagram: 0f20998e3346; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[D(X,e,base)]
  |             |
 [X] ---->[D(X,e,base)]

Arrows:
- X --e--> X
- X --x↦ x_{D}--> D(X,e,base)
- D(X,e,base) --tr_{D(X,e)}(loop)--> D(X,e,base)
- X --x↦ x_{D}--> D(X,e,base)
```
commutes.

<!-- rosetta-item-end: definition-22.1.1 -->

Recall from Example 9.2.5 that the successor function `succ-ℤ :ℤ→ ℤ` is an equivalence.
Its inverse is the predecessor function defined in Exercise 4.1.

## Definition 22.1.2

<!-- rosetta-item: definition-22.1.2; latex-label: defn:universal-cover-circle -->

The **universal cover** of the circle is defined via Definition 22.1.1 to be the unique dependent type `E_(S^1)≔D(ℤ,succ-ℤ ):S^1→𝒰`. equipped with an equivalence `x↦ x_E:ℤ→E_(S^1)(base)` and a homotopy witnessing that the square
<!-- rosetta-diagram: 9bc0bea6637a; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [ℤ] ---->[E_(S^1)(base)]
  |              |
 [ℤ] ---->[E_(S^1)(base)]

Arrows:
- ℤ --x↦ x_E--> E_(S^1)(base)
- ℤ --succ-ℤ--> ℤ
- E_(S^1)(base) --tr_{E_(S^1)}(loop)--> E_(S^1)(base)
- ℤ --x↦ x_E--> E_(S^1)(base)
```
commutes.
We will occasionally write `y↦ y_ℤ` for the inverse of `x↦ x_{E}`.

<!-- rosetta-item-end: definition-22.1.2 -->

The picture of the universal cover is that of a helix over the circle.
This picture emerges from the path liftings of `loop` in the total space.
The segments of the helix connecting `k` to `k+1` in the total space of the helix, are constructed in the following lemma.

## Lemma 22.1.3

<!-- rosetta-item: lemma-22.1.3 -->

For any `k:ℤ`, there is an identification
```text
segment-helix_k:(base,k_{E})=(base,succ-ℤ (k)_{E})
```
in the total space `Σ(t:S^1) E(t)`.

### Proof

<!-- rosetta-item: subheading-22.1-proof -->

*Proof.* By Theorem 9.3.4 it suffices to show that
```text
Π(k:ℤ) Σ(α:base=base) tr_{E}(α,k_{E})= succ-ℤ (k)_{E}.
```
We just take `α≔loop`.
Then we have `tr_{E}(α,k_{E})= succ-ℤ (k)_{E}` by the commuting square provided in the definition of `E`. ◻

<!-- rosetta-item-end: lemma-22.1.3 -->
