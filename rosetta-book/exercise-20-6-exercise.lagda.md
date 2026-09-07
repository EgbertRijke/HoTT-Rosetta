# Exercise 20.6

```agda
module exercise-20-6-exercise where

```

## Problem statement

(Awodey, Gambino, Sojakova \[citation: `AwodeyGambinoSojakova`\]) For any type family `B` over `A`, the **polynomial endofunctor** `P_{A,B}` acts on types by
```text
P_{A,B}(X) ≔ Σ(x:A) X^{B(x)},
```
and it takes a map `h:X→ Y` to the map
```text
P_{A,B}(h) : P_{A,B}(X)→ P_{A,B}(Y)
```
defined by `P_{A,B}(h,(x,α)) ≔ (x,h∘ α)`.
Furthermore, there is a canonical map
```text
(h~ h') → (P_{A,B}(h)~ P_{A,B}(h'))
```
taking a homotopy `H:h~ h'` to a homotopy `P_{A,B}(H):P_{A,B}(h)~ P_{A,B}(h')`.

A type `X` is said to be equipped with the **structure of an algebra** for the polynomial endofunctor `P_{A,B}` if `X` comes equipped with a map
```text
μ: P_{A,B}(X)→ X.
```
Thus, **algebras** for the polynomial endofunctor `P_{A,B}` are pairs `(X,μ)` where `X` is a type and `μ:P_{A,B}(X)→ X`.
Note that `W(A,B)` comes equipped with the structure of an algebra for `P_{A,B}` by Proposition 20.2.1.

Given two algebras `X` and `Y` for the polynomial endofunctor `P_{A,B}`, we say that a map `h:X→ Y` is equipped with the **structure of a homomorphism** of algebras if it comes equipped with a homotopy witnessing that the square
<!-- rosetta-diagram: aff24b08f0d2; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[P_{A,B}(X)]---->[P_{A,B}(Y)]
     |                |
    [X]     ---->    [Y]

Arrows:
- P_{A,B}(X) --μ_X--> X
- P_{A,B}(X) --P_{A,B}(h)--> P_{A,B}(Y)
- P_{A,B}(Y) --μ_Y--> Y
- X --h--> Y
```
commutes.
The type `hom((X,μ_X),(Y,μ_Y))` of homomorphisms of algebras for `P_{A,B}` is therefore defined as
```text
hom((X,μ_X),(Y,μ_Y))≔ Σ(h:X→ Y) h∘μ_X~ μ_Y∘ P_{A,B}(h).
```

<div class="subexenum">

For any `(x,α),(y,β):P_{A,B}(X)`, construct an equivalence
```text
((x,α)=(y,β)) ≃ Σ(p:x=y) α~ β∘tr_B(p).
```

For any two morphisms `(f,K),(g,L):hom((X,μ_X),(Y,μ_Y))` of algebras for `P_{A,B}`, construct an equivalence
```text
((f,K)=(g,L))≃ Σ(H:f~ g) K ∙ (μ_Y· P_{A,B}(H))~ (H· μ_X) ∙ L.
```

Show that the W-type `W(A,B)` equipped with the canonical structure `ε` of a `P_{A,B}`-algebra, constructed in Proposition 20.2.1, is a in the sense that the type
```text
hom((W(A,B),ε),(X,μ))
```
is contractible, for each `P_{A,B}`-algebra `(X,μ)`.

</div>

## Solution

<!-- rosetta-item: exercise-20-6 -->

No formalization has been curated yet.
