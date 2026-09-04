# Section 19.5 The Eckmann-Hilton argument

```agda
module section-19-5-the-eckmann-hilton-argument where
```

<!-- rosetta-item: section-19.5 -->

The Eckmann-Hilton argument is used to show that `π_n(A)` is an abelian group for all `n≥ 2`.
This is achieved by constructing an identification
```text
p ∙ q=q ∙ p
```
for all `p,q:Ω^2(A)`.
Note that identification elimination is not immediately applicable here, since both `p` and `q` are identifications of type `refl=refl` with neither endpoint free.
Therefore, we must come up with something else.

## Definition 19.5.1

<!-- rosetta-item: definition-19.5.1 -->

Consider a binary operation `f:A→(B→ C)`.
The **binary action on paths** of `f` is the family of functions
```text
ap-binary_f:(x=x')→ ((y=y') → (f(x,y)=f(x',y'))
```
indexed by `x,x':A` and `y,y':B` given by `ap-binary_f(refl,refl)≔refl`.

<!-- rosetta-item-end: definition-19.5.1 -->

## Lemma 19.5.2

<!-- rosetta-item: lemma-19.5.2; latex-label: lem:laws-ap-binary -->

The binary action on paths of `f:A→(B→ C)` satisfies the following laws:
```text
ap-binary_f(refl,q) = ap_{f(x)}(q)
ap-binary_f(p,refl) = ap_{f(_,y)}(p)
```
and moreover both triangles in the following diagram commute:
<!-- rosetta-diagram: 111901edb741; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [f(x,y)]---->[f(x',y)]
    |             |
[f(x,y')]---->[f(x',y')]

Arrows:
- f(x,y) --{ap_{f(_,y)}(p)}--> f(x',y)
- f(x,y) --{ap_{f(x,_)}(q)}--> f(x,y')
- f(x,y) --{ap-binary_f(p,q)}--> f(x',y')
- f(x',y) --{ap_{f(x',_)}(q)}--> f(x',y')
- f(x,y') --{ap_{f(_,y')}(p)}--> f(x',y')
```

### Proof

<!-- rosetta-item: subheading-19.5-proof -->

*Proof.* The proof is immediate by identification elimination on `p` and `q`, where applicable. ◻

<!-- rosetta-item-end: lemma-19.5.2 -->

## Example 19.5.3

<!-- rosetta-item: example-19.5.3 -->

One particular binary operation to which we can apply the binary action on paths is concatenation of identifications
```text
_ ∙ _:(x=y)→((y=z)→ (x=z))
```
This results in the **horizontal concatenation** operation
```text
∙[h]{_}{_} : (p=p')→ ((q=q') → (p ∙ q=p' ∙ q')).
```
In other words, for any two identifications `r:p=p'` and `s:q=q'` as in the diagram
<!-- rosetta-diagram: 65612ce01e63; review: pending -->

*Linear diagram (automatic draft).*

```text
 [x] ----> [y] ----> [z]

Arrows:
- x --p--> y
- x --{p'}--> y
- x --r⇓--> custom target
- y --q--> z
- y --{q'}--> z
- y --s⇓--> custom target
```
we obtain `∙[h]{r}{s}≔ap-binary_{_ ∙ _}(r,s):p ∙ q=p' ∙ q'`.
The **vertical concatenation** operation, which concatenates `r:p=p'` and `r':p'=p''` as in the diagram
<!-- rosetta-diagram: b5cd52ee9c57; review: pending -->

*Linear diagram (automatic draft).*

```text
 [x] ----> [y]

Arrows:
- x --p--> y
- x --{p'}--> y
- x --{p''}--> y
- x --r⇓--> custom target
- x --{r'⇓}--> custom target
```
is given by ordinary concatenation of identifications.

<!-- rosetta-item-end: example-19.5.3 -->

## Lemma 19.5.4

<!-- rosetta-item: lemma-19.5.4; latex-label: lem:unit-laws-horizontal-concat -->

Horizontal concatenation satisfies the following left and right unit laws:
```text
∙[h]{refl{refl}}{s} = s
∙[h]{r}{refl{refl}} = r.
```

### Proof

<!-- rosetta-item: subheading-19.5-proof-2 -->

*Proof.* This follows by identification elimination on `r` and `s`, or alternatively via Lemma 19.5.2. ◻

<!-- rosetta-item-end: lemma-19.5.4 -->

In the following lemma we establish the **interchange law** for horizontal and vertical concatenation.

## Lemma 19.5.5

<!-- rosetta-item: lemma-19.5.5; latex-label: lem:interchange-law -->

Consider a diagram of the form
<!-- rosetta-diagram: 75f5350fa18c; review: pending -->

*Linear diagram (automatic draft).*

```text
 [x] ----> [y] ----> [z]

Arrows:
- x --p--> y
- x --unlabeled--> y
- x --{p''}--> y
- x --r⇓--> custom target
- x --{r'⇓}--> custom target
- y --q--> z
- y --unlabeled--> z
- y --{q''}--> z
- y --s⇓--> custom target
- y --{s'⇓}--> custom target
```
Then there is an identification
```text
∙[h]{(∙{r}{r'})}{(∙{s}{s'})}=∙{(∙[h]{r}{s})}{(∙[h]{r'}{s'})}.
```

### Proof

<!-- rosetta-item: subheading-19.5-proof-3 -->

*Proof.* We use path induction on both `r` and `s`.
Then it suffices to show that
```text
∙[h]{(∙{refl}{r'})}{(∙{refl}{s'})}=∙{(∙[h]{refl}{refl})}{(∙[h]{r'}{s'})}
```
Using the unit laws for ordinary concatenation, we see that both sides reduce to `∙[h]{r'}{s'}`. ◻

<!-- rosetta-item-end: lemma-19.5.5 -->

## Theorem 19.5.6

<!-- rosetta-item: theorem-19.5.6 -->

Consider a pointed type `A`, and let `r,s:Ω^2(A)`.
Then there is an identification
```text
r ∙ s=s ∙ r
```

### Proof

<!-- rosetta-item: subheading-19.5-proof-4 -->

*Proof.* First we observe that `∙{r}{s}=∙[h]{r}{s}` by the following calculation using the unit laws from Lemma 19.5.4 and the interchange law from Lemma 19.5.5:
```text
∙{r}{s} = ∙{(∙[h]{r}{refl{refl}})}{(∙[h]{refl{refl}}{s})}
= ∙[h]{(∙{r}{refl{refl}})}{(∙{refl{refl}}{s})}
= ∙[h]{r}{s}
```
Similarly, we observe that `∙[h]{r}{s}=s ∙ r` by the following calculation:
```text
∙[h]{r}{s} = ∙[h]{(∙{refl{refl}}{r})}{(∙{s}{refl{refl}})}
= ∙{(∙[h]{refl{refl}}{s})}{(∙[h]{r}{refl{refl}})}
= s ∙ r.
```
These two calculations combined prove the claim. ◻

<!-- rosetta-item-end: theorem-19.5.6 -->

## Corollary 19.5.7

<!-- rosetta-item: corollary-19.5.7 -->

For `n≥ 2`, the `n`-th homotopy group of any pointed type is abelian.

### Proof

<!-- rosetta-item: subheading-19.5-proof-5 -->

*Proof.* By Proposition 19.4.6 it follows that `π_n(A)` is isomorphic to the second homotopy group of some pointed type, for every `n≥ 2`.
Therefore it suffices to prove the claim for `π_2(A)` for every pointed type `A`.

Our goal is to show that
```text
Π(r,s:π_2(A)) rs=sr.
```
Since we are constructing an identification in a set, we can use the dependent universal property of `0`-truncation on both `r` and `s`, stated in Theorem 18.5.2.
Therefore it suffices to show that
```text
Π(r,s:Ω^2(A)) η(r)η(s)=η(s)η(r).
```
The claim now follows, because
```text
η(r)η(s)=η(r ∙ s)=η(s ∙ r)=η(s)η(r).
```
 ◻

<!-- rosetta-item-end: corollary-19.5.7 -->
