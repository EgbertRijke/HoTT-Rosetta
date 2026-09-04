# Section 22.2 Working with descent data

```agda
module section-22-2-working-with-descent-data where
```

<!-- rosetta-item: section-22.2 -->

The equivalence
```text
(S^1→𝒰)≃ Σ(X:𝒰) X≃ X
```
yields that for any type family `A` over the circle the type of descent data `(X,e)` equipped with an equivalence `α:X≃ A(base)` and a homotopy `H` witnessing that the square
<!-- rosetta-diagram: 53928bc65cb5; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[A(base)]
  |           |
 [X] ---->[A(base)]

Arrows:
- X --α--> A(base)
- X --e--> X
- A(base) --tr_A(loop)--> A(base)
- X --α--> A(base)
```
commutes is contractible.
In the remainder of this section we study arbitrary type families over the circle equipped with such descent data, which will put us in a good position to prove things about the universal cover of the circle.

## Proposition 22.2.1

<!-- rosetta-item: proposition-22.2.1 -->

Consider a type family `A` over the circle and consider descent data `(X,e)` equipped with an equivalence `α:X≃ A(base)` and a homotopy witnessing that the square
<!-- rosetta-diagram: 53928bc65cb5; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[A(base)]
  |           |
 [X] ---->[A(base)]

Arrows:
- X --α--> A(base)
- X --e--> X
- A(base) --tr_A(loop)--> A(base)
- X --α--> A(base)
```
commutes.
Furthermore, consider two elements `x,y:X`.
Then we have an equivalence
```text
ᾱ:(e(x)=y)≃ (tr_{A}(loop,α(x))=α(y)).
```

### Proof

<!-- rosetta-item: subheading-22.2-proof -->

*Proof.* Note that the commutativity of the square implies that
```text
tr_A(loop,α(x))=α(e(x)).
```
By Theorem 11.2.2 it therefore suffices to prove that the total space
```text
Σ(y:X) tr_A(loop,α(x))=α(y)
```
is contractible.
This type is equivalent to `fib(α, tr_A(loop,α(x)))`, which is contractible because `α` is an equivalence. ◻

<!-- rosetta-item-end: proposition-22.2.1 -->

In the following proposition we show that sections of a type family `A` equipped with descent data `(X,e)` are equivalently described as fixed points for `e:X≃ X`.

## Proposition 22.2.2

<!-- rosetta-item: proposition-22.2.2 -->

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α:X≃ A(base)` and a homotopy witnessing that the square
<!-- rosetta-diagram: 53928bc65cb5; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[A(base)]
  |           |
 [X] ---->[A(base)]

Arrows:
- X --α--> A(base)
- X --e--> X
- A(base) --tr_A(loop)--> A(base)
- X --α--> A(base)
```
commutes.
Then there is a commuting square
<!-- rosetta-diagram: 10fe03d1fb11; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[Π(t:S^1) A(t)]---->[Σ(x:X) e(x)=x]
       |                   |
   [A(base)]   ---->      [X]

Arrows:
- Π(t:S^1) A(t) --ev_base--> A(base)
- Π(t:S^1) A(t) --unlabeled--> Σ(x:X) e(x)=x
- Σ(x:X) e(x)=x --pr 1--> X
- A(base) --α^{-1}--> X
```
in which the top map is an equivalence.

### Proof

<!-- rosetta-item: subheading-22.2-proof-2 -->

*Proof.* By the dependent universal property of the circle we have an equivalence
```text
(Π(t:S^1) A(t))≃ Σ(x:A(base)) tr_A(loop,x)=x.
```
This equivalence fits in a commuting triangle
<!-- rosetta-diagram: a1c2e648c9d6; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
                    [Π(t:S^1) A(t)]

[Σ(x:X) e(x)=x]                         [Σ(x:A(base)) tr_A(loop,x)=x]

Arrows:
- Π(t:S^1) A(t) --unlabeled--> Σ(x:X) e(x)=x
- Π(t:S^1) A(t) --dgen_{S^1}--> Σ(x:A(base)) tr_A(loop,x)=x
- Σ(x:X) e(x)=x --{tot([α]{ᾱ}}--> Σ(x:A(base)) tr_A(loop,x)=x
```
where the map on the left is given by `s↦(α^{-1}(s(base)),ᾱ^{-1}(apd_{s}(loop)))`.
The bottom map and the map on the right are equivalences, so it follows by the 3-for-2 property of equivalences that the map on the left is an equivalence. ◻

<!-- rosetta-item-end: proposition-22.2.2 -->

The following corollary can be used to compare type families over the circle.
In particular, we will use it to compare the identity type of the circle with the universal cover.

## Corollary 22.2.3

<!-- rosetta-item: corollary-22.2.3 -->

Consider two type families `A` and `B` over the circle equipped with descent data `(X,e)` and `(Y,f)`, equivalences `α:X≃ A(base)` and `β:Y≃ B(base)`, and homotopies `H` and `K` witnessing that the squares
<!-- rosetta-diagram: 9d6c06d93fe0; review: pending -->

*2-by-4 diagram (automatic draft).*

```text
 [X] ---->[A(base)]      [Y] ---->[B(base)]
  |           |           |           |
 [X] ---->[A(base)]      [Y] ---->[B(base)]

Arrows:
- X --α--> A(base)
- X --e--> X
- A(base) --tr_A(loop)--> A(base)
- Y --β--> B(base)
- Y --f--> Y
- B(base) --tr_B(loop)--> B(base)
- X --α--> A(base)
- Y --β--> B(base)
```
commute, respectively.
Then there is a commuting square
<!-- rosetta-diagram: 29428d404125; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[(Π(t:S^1) A(t)→ B(t))]---->[Σ(h:X→ Y) h∘ e~ f∘ h]
           |                          |
  [(A(base)→ B(base))] ---->       [(X→ Y)]

Arrows:
- (Π(t:S^1) A(t)→ B(t)) --unlabeled--> Σ(h:X→ Y) h∘ e~ f∘ h
- (Π(t:S^1) A(t)→ B(t)) --ev_base--> (A(base)→ B(base))
- Σ(h:X→ Y) h∘ e~ f∘ h --pr 1--> (X→ Y)
- (A(base)→ B(base)) --h↦ β^{-1}∘ h∘ α--> (X→ Y)
```
in which the top map is an equivalence.

### Proof

<!-- rosetta-item: subheading-22.2-proof-3 -->

*Proof.* The claim follows once we observe that `(Y^X,λ h. f∘ h∘ e^{-1})` is descent data for the family of types `(A(t)→ B(t))` indexed by `t:S^1`.
Indeed, we have the equivalence `h↦ β∘ h∘α^{-1} : Y^X≃ B(base)^{A(base)}` for which the square
<!-- rosetta-diagram: 91cf401e21b7; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[Y^X]---->[B(base)^{A(base)}]
  |                |
[Y^X]---->[B(base)^{A(base)}]

Arrows:
- Y^X --h↦β∘ h∘α^{-1}--> B(base)^{A(base)}
- Y^X --h↦ f∘ h∘ e^{-1}--> Y^X
- B(base)^{A(base)} --tr_{t↦ A(t)→ B(t)}(loop)--> B(base)^{A(base)}
- Y^X --h↦β∘ h∘α^{-1}--> B(base)^{A(base)}
```
commutes. ◻

<!-- rosetta-item-end: corollary-22.2.3 -->

## Corollary 22.2.4

<!-- rosetta-item: corollary-22.2.4; latex-label: cor:compute-families-of-maps-universal-cover -->

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α:X≃ A(base)` and a homotopy witnessing that the square
<!-- rosetta-diagram: 53928bc65cb5; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [X] ---->[A(base)]
  |           |
 [X] ---->[A(base)]

Arrows:
- X --α--> A(base)
- X --e--> X
- A(base) --tr_A(loop)--> A(base)
- X --α--> A(base)
```
commutes.
Then there is a commuting square
<!-- rosetta-diagram: 5009058dedc0; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[(Π(t:S^1) E_(S^1)(t)→ A(t))]---->[Σ(h:ℤ → X) h∘ succ-ℤ ~ e∘ h]
              |                                 |
  [(E_(S^1)(base)→ A(base))] ---->          [(ℤ → X)]

Arrows:
- (Π(t:S^1) E_(S^1)(t)→ A(t)) --unlabeled--> Σ(h:ℤ → X) h∘ succ-ℤ ~ e∘ h
- (Π(t:S^1) E_(S^1)(t)→ A(t)) --ev_base--> (E_(S^1)(base)→ A(base))
- Σ(h:ℤ → X) h∘ succ-ℤ ~ e∘ h --pr 1--> (ℤ → X)
- (E_(S^1)(base)→ A(base)) --h↦ α^{-1}∘ h∘ (k↦ k_{E})--> (ℤ → X)
```
in which the top map is an equivalence.

<!-- rosetta-item-end: corollary-22.2.4 -->

In other words, a family of maps `E_(S^1)(t)→ A(t)` indexed by `t:S^1` is equivalently described as a map `h:ℤ→ X` for which the square
<!-- rosetta-diagram: 84d63923e835; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [ℤ] ----> [X]
  |         |
 [ℤ] ----> [X]

Arrows:
- ℤ --h--> X
- ℤ --succ-ℤ--> ℤ
- X --e--> X
- ℤ --h--> X
```
commutes.
It is now time to prove the universal property of the integers.
