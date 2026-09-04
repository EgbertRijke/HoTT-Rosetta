# Section 21.2 The (dependent) universal property of the circle

```agda
module section-21-2-the-dependent-universal-property-of-the-circle where
```

<!-- rosetta-item: section-21.2 -->

We will now use the induction principle of the circle to derive the *dependent universal property* and the *universal property* of the circle.
The universal property of the circle states that, for any type `X` the canonical map
```text
(S^1→ X)→(Σ(x:X) x=x)
```
given by `f↦(f(base),ap_{f}(loop))` is an equivalence.
The type `Σ(x:X) x=x` is also called the type of **free loops** in `X`.
In other words, the universal property of the circle states that a map `S^1→ X` is the same thing as a free loop in `X`.

The *dependent universal property* of the circle similarly states that for any type family `P` over the circle, the canonical map
```text
dgen_{S^1}:(Π(x:S^1) P(x))→(Σ(y:P(base)) tr_P(loop,y)=y)
```
given by `f↦(f(base),apd_{f}(loop))` is an equivalence.
Note that the induction principle already states that this map has a section.
The dependent universal property therefore improves on this by stating that this map also has a retraction.

## Theorem 21.2.1

<!-- rosetta-item: theorem-21.2.1; latex-label: thm:circle-dependent-universal-property -->

For any type family `P` over the circle, the map
```text
dgen_{S^1}:
(Π(x:S^1) P(x))
→
(Σ(y:P(base)) tr_P(loop,y)=y)
```
given by `f↦(f(base),apd_{f}(loop))` is an equivalence.

### Proof

<!-- rosetta-item: subheading-21.2-proof -->

*Proof.* By the induction principle of the circle we know that the map has a section, i.e., we have
```text
ind-S^1 : (Σ(y:P(base)) tr_P(loop,y)=y) → (Π(x:S^1) P(x))
comp_S^1 : dgen_{S^1}∘ind-S^1~id
```
Therefore it remains to construct a homotopy
```text
ind-S^1∘dgen_{S^1}~id.
```
Thus, for any `f:Π(x:S^1) P(x)` our task is to construct an identification
```text
ind-S^1(dgen_{S^1}(f))=f.
```
By function extensionality it suffices to construct a homotopy
```text
Π(x:S^1) ind-S^1(dgen_{S^1}(f))(x)= f(x).
```
We proceed by the induction principle of the circle using the family of types `E_{g,f}(x)≔ g(x)=f(x)` indexed by `x:S^1`, where `g` is the function
```text
g≔ind-S^1(dgen_{S^1}(f)).
```
Thus, it suffices to construct
```text
α : g(base)=f(base)
β : tr_{E_{g,f}}(loop,α)=α.
```
An argument by path induction on `p` yields that
```text
(apd_{g}(p) ∙ r=ap_{tr_P(p)}(q) ∙ apd_{f}(p))→(tr_{E_{g,f}}(p,q)=r),
```
for any `f,g:Π(x:X) P(x)` and any `p:x=x'`, `q:g(x)=f(x)` and `r:g(x')=f(x')`.
Therefore it suffices to construct an identification `α:g(base)=f(base)` equipped with an identification `β` witnessing that the square
<!-- rosetta-diagram: f0e00b3923b3; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_P(loop,g(base))]---->[tr_P(loop,f(base))]
         |                        |
     [g(base)]      ---->     [f(base)"]

Arrows:
- tr_P(loop,g(base)) --apd_{g}(loop)--> g(base)
- tr_P(loop,g(base)) --ap_{tr_P(loop)}(α)--> tr_P(loop,f(base))
- tr_P(loop,f(base)) --apd_{f}(loop)--> f(base)"
- g(base) --α--> f(base)"
```
commutes.
Notice that we get exactly such a pair `(α,β)` from the computation rule of the circle, by Remark 21.1.3. ◻

<!-- rosetta-item-end: theorem-21.2.1 -->

As a corollary we obtain the following uniqueness principle for dependent functions defined by the induction principle of the circle.

## Corollary 21.2.2

<!-- rosetta-item: corollary-21.2.2 -->

Consider a type family `P` over the circle, and let
```text
y : P(base)
p : tr_{P}(loop,y)=y.
```
Then the type of functions `f:Π(x:S^1) P(x)` equipped with an identification
```text
α: f(base)=y
```
and an identification `β` witnessing that the square
<!-- rosetta-diagram: 4f7ce2692a14; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_P(loop,f(base))]---->[tr_P(loop,y)]
         |                     |
     [f(base)]      ---->     [y]

Arrows:
- tr_P(loop,f(base)) --{apd_{f}(loop)}--> f(base)
- tr_P(loop,f(base)) --ap_{tr_P(loop)}(α)--> tr_P(loop,y)
- tr_P(loop,y) --{p}--> y
- f(base) --α--> y
```
commutes, is contractible.

<!-- rosetta-item-end: corollary-21.2.2 -->

Now we use the dependent universal property to derive the ordinary universal property of the circle.
It would be tempting to say that it is a direct corollary, but we need to address the transport that occurs in the dependent universal property.

## Theorem 21.2.3

<!-- rosetta-item: theorem-21.2.3; latex-label: thm:circle_up -->

For each type `X`, the **action on generators**
```text
gen_{S^1}:(S^1→ X)→ Σ(x:X) x=x
```
given by `f↦ (f(base),ap_{f}(loop))` is an equivalence.

### Proof

<!-- rosetta-item: subheading-21.2-proof-2 -->

*Proof.* We prove the claim by constructing a commuting triangle
<!-- rosetta-diagram: f1ff10123b43; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
                   [(S^1→ X)]

[(Σ(x:X) x=x)]                    [(Σ(x:X) tr_{const_X}(loop,x)=x)]

Arrows:
- (S^1→ X) --gen_{S^1}--> (Σ(x:X) x=x)
- (S^1→ X) --dgen_{S^1}--> (Σ(x:X) tr_{const_X}(loop,x)=x)
- (Σ(x:X) x=x) --≃--> (Σ(x:X) tr_{const_X}(loop,x)=x)
```
in which the bottom map is an equivalence.
Indeed, once we have such a triangle, we use the fact from Theorem 21.2.1 that `dgen_{S^1}` is an equivalence to conclude that `gen_{S^1}` is an equivalence.

To construct the bottom map, we first observe that for any constant type family `const_B` over a type `A`, any `p:a=a'` in `A`, and any `b:B`, there is an identification
```text
tr-const_B(p,b):tr_{const_B}(p,b)=b.
```
This identification is easily constructed by path induction on `p`.
Now we construct the bottom map as the induced map on total spaces of the family of maps
```text
l↦ tr-const_X(loop,x) ∙ l,
```
indexed by `x:X`.
Since concatenating by a path is an equivalence, it follows by Theorem 11.1.3 that the induced map on total spaces is indeed an equivalence.

To show that the triangle commutes, it suffices to construct for any `f:S^1→ X` an identification witnessing that the triangle
<!-- rosetta-diagram: a5cdcdc52c26; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[tr_{const_X}(loop,f(base))]                   [f(base)]

                                 [f(base)]

Arrows:
- tr_{const_X}(loop,f(base)) --apd_{f}(loop)--> f(base)
- tr_{const_X}(loop,f(base)) --{tr-const_X(loop,f(base))}--> f(base)
- f(base) --ap_{f}(loop)--> f(base)
```
commutes.
This again follows from general considerations: for any `f:A→ B` and any `p:a=a'` in `A`, the triangle
<!-- rosetta-diagram: e1e24116802a; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[tr_{const_B}(p,f(a))]                 [f(a)]

                           [f(a')]

Arrows:
- tr_{const_B}(p,f(a)) --apd_{f}(p)--> f(a')
- tr_{const_B}(p,f(a)) --{tr-const_B(p,f(a))}--> f(a)
- f(a) --ap_{f}(p)--> f(a')
```
commutes by path induction on `p`. ◻

<!-- rosetta-item-end: theorem-21.2.3 -->

## Corollary 21.2.4

<!-- rosetta-item: corollary-21.2.4 -->

For any loop `l:x=x` in a type `X`, the type of maps `f:S^1→ X` equipped with an identification
```text
α : f(base)=x
```
and an identification `β` witnessing that the square
<!-- rosetta-diagram: 5ae274f72d1a; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[f(base)]----> [x]
    |           |
[f(base)]----> [x]

Arrows:
- f(base) --α--> x
- f(base) --ap_{f}(loop)--> f(base)
- x --l--> x
- f(base) --α--> x
```
commutes, is contractible.

<!-- rosetta-item-end: corollary-21.2.4 -->
