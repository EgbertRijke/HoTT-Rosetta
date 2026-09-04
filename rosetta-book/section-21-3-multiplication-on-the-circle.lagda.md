# Section 21.3 Multiplication on the circle

```agda
module section-21-3-multiplication-on-the-circle where
```

<!-- rosetta-item: section-21.3 -->

One way the circle arises classically, is as the set of complex numbers at distance `1` from the origin.
It is an elementary fact that `|xy|=|x||y|` for any two complex numbers `x,y∈ℂ`, so it follows that when we multiply two complex numbers that both lie on the unit circle, then the result lies again on the unit circle.
This operation puts a group structure on the classical circle.

This suggests that it should also be possible to construct a multiplication on the higher inductive type `S^1`.
More precisely, we will equip `S^1` with an *H-space structure*, and in the exercises you will be asked to show that this multiplicative structure is associative, commutative, and has inverses.

## Definition 21.3.1

<!-- rosetta-item: definition-21.3.1 -->

Consider a pointed type `A` with a base point `pt`.
An **H-space structure** on `(A,pt)` consists of a binary operation `μ:A→ (A→ A)` satisfying the following **coherent unit laws**:
```text
left-unit_μ(y) : μ(pt,y)= y
right-unit_μ(x) : μ(x,pt)= x
coh-unit_μ : left-unit_μ(pt)=right-unit_μ(pt).
```
An **H-space** is a pointed type equipped with an H-space structure.

<!-- rosetta-item-end: definition-21.3.1 -->

## Remark 21.3.2

<!-- rosetta-item: remark-21.3.2; latex-label: rmk:hspace -->

The data of an H-space structure is equivalently described by a family of base point preserving maps
```text
μ : Π(x:A) Σ(f:A→ A) f(pt)=x
```
equipped with an identification `μ_pt=(id,refl)`.
The data `μ(a,pt)=a` corresponds to the right unit law for `μ`, whereas the data `μ_pt=(id,refl)` combines the left unit law and the coherence in one single identification.

Note that for any identification `α:x=y` in `A` and two base-point preserving functions `(f,p):Σ(f:A→ A) f(pt)=x` and `(g,q):Σ(f:A→ A) f(pt)=y`, we have
```text
τ:(Σ(H:f~ g) p ∙ α=H(pt) ∙ q) → tr(α,(f,p))=(g,q)
```
This function is easily constructed by identification elimination on `α`.
We will be using this in our construction of the H-space structure on the circle.

<!-- rosetta-item-end: remark-21.3.2 -->

## Theorem 21.3.3

<!-- rosetta-item: theorem-21.3.3; latex-label: defn:hspace-circle -->

There is an H-space structure
```text
mul_(S^1) : S^1→(S^1→S^1)
left-unit_{S^1} : Π(y:S^1) mul_(S^1)(base,y)=y
right-unit_{S^1} : Π(x:S^1) mul_(S^1)(x,base)=x
coh-unit_{S^1} : left-unit_{S^1}(base)=right-unit_{S^1}(base).
```
on the circle.

### Proof

<!-- rosetta-item: subheading-21.3-proof -->

*Construction.* By Remark 21.3.2 it suffices to construct a dependent function
```text
μ:Π(x:S^1) Σ(f:S^1→S^1) f(base)=x
```
such that `μ(base)=(id,refl)`.
This provides us with a useful shortcut, because the identification will follow from the computation rule of the induction principle of the circle.

Let `P` be the family of types given by `P(x):=Σ(f:S^1→S^1) f(base)=x`.
By the dependent universal property of the circle there is a unique
```text
μ :Π(x:S^1) Σ(f:S^1→S^1) f(base)=x
```
equipped with an identification `α:μ(base)=(id,refl)` and an identification witnessing that the square
<!-- rosetta-diagram: 70d5face1c4b; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_P(loop,μ(base))]---->[tr_P(loop,(id,refl))]
         |                         |
     [μ(base)]      ---->     [(id,refl)]

Arrows:
- tr_P(loop,μ(base)) --apd_{μ}(loop)--> μ(base)
- tr_P(loop,μ(base)) --ap_{tr_P(loop)}(α)--> tr_P(loop,(id,refl))
- tr_P(loop,(id,refl)) --{τ(H,r)}--> (id,refl)
- μ(base) --α--> (id,refl)
```
commutes.
In this square, `τ` is the function from Remark 21.3.2, and the homotopy `H:id~id` equipped with an identification `r:loop = H(base) ∙ refl` remain to be defined.

We use the dependent universal property of the circle with respect to the family `E_{id,id}` given by
```text
E_{id,id}(x) ≔ (x=x),
```
to define `H` as the unique homotopy equipped with an identification
```text
α : H(base)=loop
```
and an identification `β` witnessing that the square
<!-- rosetta-diagram: 31a91ca91b38; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_{E_{id,id}}(loop,H(base))]---->[tr_{E_{id,id}}(loop,loop)]
              |                                 |
          [H(base)]           ---->           [loop]

Arrows:
- tr_{E_{id,id}}(loop,H(base)) --ap_{tr_{E_{id,id}}(loop)}(α)--> tr_{E_{id,id}}(loop,loop)
- tr_{E_{id,id}}(loop,H(base)) --apd_{H}(loop)--> H(base)
- tr_{E_{id,id}}(loop,loop) --γ--> loop
- H(base) --α--> loop
```
commutes.
Now it remains to define the path `γ:tr_{E_{id,id}}(loop,loop)=loop` in the above square.
To proceed, we first observe that a simple path induction argument yields a function
```text
(p ∙ r=q ∙ p)→(tr_{E_{id,id}}(p,q)=r),
```
for any `p:base=x`, `q:base=base` and `r:x=x`.
In particular, we have a function
```text
(loop ∙ loop=loop ∙ loop)→(tr_{E_{id,id}}(loop,loop)=loop).
```
Now we apply this function to `refl` to obtain the desired identification
```text
γ:tr_{E_{id,id}}(loop,loop)=loop.
```
 ◻

<!-- rosetta-item-end: theorem-21.3.3 -->

## Remark 21.3.4

<!-- rosetta-item: remark-21.3.4 -->

For some of the exercises below it may be useful to know that the binary operation `mul_(S^1)` is the unique map `S^1→(S^1→S^1)` equipped with an identification
```text
base-mul_(S^1) :mul_(S^1)(base)=id
```
and an identification `loop-mul_(S^1)` witnessing that the square
<!-- rosetta-diagram: 6f4f22a0dd3c; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[mul_(S^1)(base)]----> [id]
        |               |
[mul_(S^1)(base)]----> [id]

Arrows:
- mul_(S^1)(base) --base-mul_(S^1)--> id
- mul_(S^1)(base) --ap_{mul_(S^1)}(loop)--> mul_(S^1)(base)
- id --eq-htpy(H)--> id
- mul_(S^1)(base) --base-mul_(S^1)--> id
```
commutes, where the homotopy `H:id~id` is the one constructed in Theorem 21.3.3.

<!-- rosetta-item-end: remark-21.3.4 -->
