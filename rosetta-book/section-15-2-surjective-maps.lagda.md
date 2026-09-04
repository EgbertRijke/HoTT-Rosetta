# Section 15.2 Surjective maps

```agda
module section-15-2-surjective-maps where
```

<!-- rosetta-item: section-15.2 -->

A map `f:A→ B` is surjective if for every `b:B` there is an *unspecified* element `a:A` that maps to `b`.
We define this property using the propositional truncation.

## Definition 15.2.1

<!-- rosetta-item: definition-15.2.1 -->

A map `f:A→ B` is said to be **surjective** if there is an element of type
```text
is-surj(f)≔ Π(b:B) ‖fib(f, b)‖.
```

<!-- rosetta-item-end: definition-15.2.1 -->

## Example 15.2.2

<!-- rosetta-item: example-15.2.2 -->

Any equivalence is a surjective map, since its fibers are contractible.
More generally, any map that has a section is surjective.
Those are sometimes called **split epimorphisms**.
Note that having a section is stronger than surjectivity, since in general we don’t have a function `‖fib(f, b)‖→fib(f, b)`.

<!-- rosetta-item-end: example-15.2.2 -->

In Exercise 14.4 we showed the dependent universal property of the propositional truncation: a map `f:A→ B` into a proposition `B` satisfies the universal property of the propositional truncation if and only if for every family of propositions `P` over `B`, the precomposition map
```text
_∘ f : (Π(b:B) P(b))→(Π(a:A) P(f(a)))
```
is an equivalence.
In the following proposition we show that, if we omit the condition that `B` is a proposition, then `f` satisfies this dependent universal property if and only if `f` is surjective.

## Proposition 15.2.3

<!-- rosetta-item: proposition-15.2.3; latex-label: prp:surjective -->

Consider a map `f:A→ B`.
Then the following are equivalent:

1.  The map `f:A→ B` is surjective.

2.  The map `f:A→ B` satisfies the **dependent universal property of a surjective map**: For any family `P` of propositions over `B`, the precomposition map
```text
_∘ f : (Π(y:B) P(y))→(Π(x:A) P(f(x)))
```
    is an equivalence. In other words, any subtype of `B` that contains all the elements of the form `f(x)` contains all the elements of `B`.

3.  For any `k≥-2`, and for any family `P` of `(k+1)`-truncated types over `B`, the precomposition map
```text
_∘ f : (Π(y:B) P(y))→(Π(x:A) P(f(x)))
```
    is a `k`-truncated map.

### Proof

<!-- rosetta-item: subheading-15.2-proof -->

*Proof.* To prove that (i) implies (ii), suppose first that `f` is surjective, and consider the commuting square
<!-- rosetta-diagram: a2c952277a82; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
      [(Π(y:B) P(y))]       ---->    [(Π(x:A) P(f(x)))]
             |                               |
[(Π(y:B) ‖fib(f, y)‖→ P(y))]---->[(Π(y:B) fib(f, y)→ P(y))]

Arrows:
- (Π(y:B) P(y)) --_∘ f--> (Π(x:A) P(f(x)))
- (Π(y:B) P(y)) --h↦λ y. const_{h(y)}--> (Π(y:B) ‖fib(f, y)‖→ P(y))
- (Π(y:B) ‖fib(f, y)‖→ P(y)) --h↦ h(_)∘η--> (Π(y:B) fib(f, y)→ P(y))
- (Π(y:B) fib(f, y)→ P(y)) --{h↦λ x. h(f(x),(x,refl))}--> (Π(x:A) P(f(x)))
```
In this square, the bottom map is an equivalence by Exercise 13.12 and by the universal property of the propositional truncation of `fib(f, y)`.
The map on the right is an equivalence by Exercise 13.15.
Furthermore, the map on the left is an equivalence by Exercises 13.12 and 13.7, because the type `‖fib(f, y)‖` is contractible by the assumption that `f` is surjective.
Therefore it follows that the top map is an equivalence, which completes the proof that (i) implies (ii).

The proof that (ii) implies (iii) is by induction on `k`.
The base case holds by assumption.
For the inductive step, it suffices by Theorem 12.4.7 to show that `ap{_∘ f}` is `k`-truncated for any `g,h:Π(y:B) P(y)`.
Notice that we have a commuting square
<!-- rosetta-diagram: af756fdb03d4; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
     [(g=h)]      ---->    [(g∘ f = h∘ f)]
        |                         |
[Π(y:B) g(y)=h(y)]---->[Π(x:A) g(f(x))=h(f(x))]

Arrows:
- (g=h) --ap{_∘ f}--> (g∘ f = h∘ f)
- (g=h) --htpy-eq--> Π(y:B) g(y)=h(y)
- (g∘ f = h∘ f) --htpy-eq--> Π(x:A) g(f(x))=h(f(x))
- Π(y:B) g(y)=h(y) --_∘ f--> Π(x:A) g(f(x))=h(f(x))
```
The vertical maps on the left and right are equivalences by function extensionality, and the bottom map is `k`-truncated by the inductive hypothesis.
This implies that `ap{_∘ f}` is `k`-truncated.

To prove that (iii) implies (i), note that the assumption in (iii) implies that the precomposition function
```text
_∘ f : (Π(y:B) ‖fib(f, y)‖)→(Π(x:A) ‖fib(f, f(x))‖)
```
is an equivalence.
Hence it suffices to construct an element of type `‖fib(f, f(x))‖` for each `x:A`.
This is easy, because we have
```text
η(x,refl):‖fib(f, f(x))‖.
```
 ◻

<!-- rosetta-item-end: proposition-15.2.3 -->

As a corollary we obtain that any surjective map into a proposition satisfies the universal property of the propositional truncation.

## Corollary 15.2.4

<!-- rosetta-item: corollary-15.2.4 -->

For any map `f:A→ P` into a proposition `P`, the following are equivalent:

1.  The map `f` satisfies the universal property of the propositional truncation of `A`.

2.  The map `f` is surjective.

<!-- rosetta-item-end: corollary-15.2.4 -->

Using the characterization of surjective maps of Proposition 15.2.3, we can also give a new characterization of the image of a map.

## Theorem 15.2.5

<!-- rosetta-item: theorem-15.2.5; latex-label: thm:surjective -->

Consider a commuting triangle
<!-- rosetta-diagram: 5b022cc117de; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                 [B]

           [X]

Arrows:
- A --q--> B
- A --f--> X
- B --m--> X
```
in which `m` is an embedding.
Then the following are equivalent:

1.  The embedding `m` satisfies the universal property of the image inclusion of `f`.

2.  The map `q` is surjective.

### Proof

<!-- rosetta-item: subheading-15.2-proof-2 -->

*Proof.* First assume that `m` satisfies the universal property of the image inclusion of `f`, and consider the composite function
<!-- rosetta-diagram: a64061e4998b; review: pending -->

*Linear diagram (automatic draft).*

```text
[(Σ(y:B) ‖fib(q, y)‖)]----> [B] ----> [X]

Arrows:
- (Σ(y:B) ‖fib(q, y)‖) --pr 1--> B
- B --m--> X
```
Note that `m∘pr 1` is a composition of embeddings, so it is an embedding.
By the universal property of `m` there is a unique map `h` for which the triangle
<!-- rosetta-diagram: e8908c0e3dba; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [B]                [Σ(y:B) ‖fib(q, y)‖]

           [X]

Arrows:
- B --m--> X
- B --h--> Σ(y:B) ‖fib(q, y)‖
- Σ(y:B) ‖fib(q, y)‖ --m∘pr 1--> X
```
commutes.
Now note that `pr 1∘ h` is a map such that `m∘ (pr 1∘ h)~ m`.
The identity function is another map for which we have `m∘id~ m`, so it follows by uniqueness that `pr 1∘ h~ id`.
In other words, the map `h` is a section of the projection map.
Therefore we obtain by Corollary 13.2.3 a dependent function
```text
Π(b:B) ‖fib(q, b)‖,
```
showing that `q` is surjective.

For the converse, suppose that `q` is surjective.
To prove that `m` satisfies the universal property of the image factorization of `f`, it suffices to construct a map
```text
hom-slice_X(f,m')→hom-slice_X(m,m'),
```
for any embedding `m':B'→ X`.
To see that there is such an equivalence, we make the following calculation
```text
hom-slice_X(m,m') ≃ Π(b:B) fib(m', m(b)) (By \cref{ex:triangle_fib})
≃ Π(a:A) fib(m', m(q(a))) (By \cref{prp:surjective})
≃ Π(a:A) fib(m', f(a)) (By $f~ m∘ q$)
≃ hom-slice_X(f,m').(By \cref{ex:triangle_fib})
```
 ◻

<!-- rosetta-item-end: theorem-15.2.5 -->

## Corollary 15.2.6

<!-- rosetta-item: corollary-15.2.6 -->

Every map factors uniquely as a surjective map followed by an embedding.

### Proof

<!-- rosetta-item: subheading-15.2-proof-3 -->

*Proof.* Consider a map `f:A→ X`, and two factorizations
<!-- rosetta-diagram: 5854a016bb76; review: pending -->

*2-by-6 diagram (automatic draft).*

```text
 [A]                 [B]      [[3em] A]                [B']

           [X]                               [X]

Arrows:
- A --q--> B
- A --f--> X
- B --i--> X
- [3em] A --{q'}--> B'
- [3em] A --f--> X
- B' --{i'}--> X
```
of `f` where `m` and `m'` are embeddings, and `q` and `q'` are surjective.
Then both `m` and `m'` satisfy the universal property of the image factorization of `f` by Theorem 15.2.5.
Now it follows by Theorem 15.1.8 that the type of `(e,H):hom-slice_X(i,i')` in which `e` is an equivalence, equipped with an identification
```text
(e,H)∘(q,I)=(q',I')
```
in `hom-slice_X(f,i')`, is contractible. ◻

<!-- rosetta-item-end: corollary-15.2.6 -->
