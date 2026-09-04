# Section 16.2 Double counting in type theory

```agda
module section-16-2-double-counting-in-type-theory where
```

<!-- rosetta-item: section-16.2 -->

In combinatorics, counting arguments often proceed by showing that two finite sets are isomorphic—or, in the language of type theory, by showing that two finite types are equivalent.
The idea here is, of course, that when we count the elements of a type twice correctly, then both countings must result in the same number.
However, this is something that we must prove before we can use it.
In other words, we must show that
```text
(Fin{k}≃Fin{l})→ (k=l)
```
for any two natural numbers `k` and `l`.
We will prove this claim as a consequence of the following general fact.

## Proposition 16.2.1

<!-- rosetta-item: proposition-16.2.1; latex-label: prp:is-injective-maybe -->

For any two types `X` and `Y`, there is a map
```text
(X+unit≃ Y+unit)→ (X≃ Y).
```

### Proof

<!-- rosetta-item: subheading-16.2-proof -->

*Proof.* We prove the claim in four steps.
We will write `i` for `inl:X→ X+unit` and also for `inl:Y→ Y+unit`, and we will write `⋆` for `inr(⋆):X+unit` and also for `inr(⋆):Y+unit`.

1.  We first show that for any equivalence `e:X+unit≃ Y+unit` and any `x:X` equipped with an identification `p:e(i(x))=⋆`, that there is an element
```text
star-value(e,x,p):Y
```
    equipped with an identification
```text
α:i(star-value(e,x,p))=e(⋆).
```
To see this, note that the map `e` is injective.
The elements `i(x)` and `⋆` are distinct, so it follows that the elements `e(i(x))` and `e(⋆)` are distinct.
In particular, we have `e(⋆)≠⋆`.
Therefore it follows that there is an element `y:Y` equipped with an identification `i(y)=e(⋆)`.

2.  Next, we construct for every equivalence `e:X+unit≃ Y+unit` a map `f:X→ Y` equipped with identifications
```text
β : Π(y:Y) (e(i(x))=i(y))→ (f(x)=y)
γ : Π(p:e(i(x))=⋆) f(x)=star-value(e,x,p).
```
In order to construct the map `f:X→ Y`, we first construct a dependent function
```text
f':Π(x:X) Π(u:Y+unit) ((e(i(x))=u)→ Y).
```
This function is defined by pattern matching on `u`, by
```text
f'(x,i(y),p) ≔ y
f'(x,⋆,p) ≔ star-value(e,x,p)
```
Then we define `f(x):=f'(x,e(i(x)),refl)`.
By the definition of `f'` it then follows that we have an identification
```text
f(x) ≐ f'(x,e(i(x)),refl)
= f'(x,i(y),p)
≐ y
```
    for any `y:Y` and `p:e(i(x))=i(y)`, and that we have an identification
```text
f(x) ≐ f'(x,e(i(x)),refl)
= f'(x,⋆,p)
≐ star-value(e,x,p)
```
    for any `p:e(i(x))=⋆`.

3.  The inverse function `g:Y→ X` is constructed in the same way as the function `f:X→ Y`, using the equivalence `e^{-1}:Y+unit≃ X+unit`.
This function comes equipped with
```text
\delta : Π(x:X) (e^{-1}(i(y))=i(x))→ (g(y)=x)
ε : Π(p:e^{-1}(i(y))=⋆) g(y)=star-value(e^{-1},y,p).
```

4.  It remains to show that `f` and `g` are inverse to each other.
The proof that `g` is a retraction of `f` is similar to the proof that `g` is a section of `f`, so we will only prove the latter.
In other words, we will construct an identification
```text
f(g(y))=y
```
    for any `y:Y`. The proof is by case analysis on `(e^{-1}(i(y))=⋆)+(e^{-1}(i(y))≠ ⋆)`. In the case where `p:e^{-1}(i(y))=⋆`, we have the identification
```text
ε(p):g(y)=star-value(e^{-1},y,p).
```
    Furthermore, we have the identification
```text
γ(q) : f(g(y)) = star-value(e,g(y),q),
```
    where `q:e(i(g(y)))=⋆` is the composite of the identifications
```text
e(i(g(y))) = e(i(star-value(e^{-1},y,p)))
= e(e^{-1}(⋆))
=⋆.
```
Using the identification `γ(q)`, we obtain
```text
i(f(g(y))) = i(star-value(e,g(y),q))
= e(⋆)
= e(e^{-1}(i(y)))
= i(y).
```
Since `i:Y→ Y+unit` is injective, it follows that `f(g(y))=y`.

 ◻

<!-- rosetta-item-end: proposition-16.2.1 -->

## Theorem 16.2.2

<!-- rosetta-item: theorem-16.2.2; latex-label: thm:is-injective-Fin -->

For any two natural numbers `k` and `l`, there is a map
```text
(Fin{k}≃Fin{l})→ (k=l).
```

### Proof

<!-- rosetta-item: subheading-16.2-proof-2 -->

*Proof.* The proof is by induction on `k` and `l`.
In the base case, where both `k` and `l` are zero, the claim is obvious.
If `k` is zero and `l` is a successor, then we have `0:Fin{l}`.
Any equivalence `e:Fin{k}≃ Fin{l}` now gives us the element
```text
e^{-1}(0):empty,
```
which is of course absurd.
Similarly, if `k` is a successor and `l` is zero, we obtain `e(0):empty`, which is again absurd.
If both `k` and `l` are a successor, then we have by Proposition 16.2.1 the composite
<!-- rosetta-diagram: 78052f0defcc; review: pending -->

*Linear diagram (automatic draft).*

```text
[(Fin{k+1}≃Fin{l+1})]---->[(Fin{k}≃Fin{l})]---->[(k=l)]---->[(k+1=l+1)]

Arrows:
- (Fin{k+1}≃Fin{l+1}) --unlabeled--> (Fin{k}≃Fin{l})
- (Fin{k}≃Fin{l}) --unlabeled--> (k=l)
- (k=l) --unlabeled--> (k+1=l+1)
```
 ◻

<!-- rosetta-item-end: theorem-16.2.2 -->
