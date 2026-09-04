# Section 9.1 Homotopies

```agda
module section-9-1-homotopies where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-2-boolean-operations
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
```

<!-- rosetta-item: section-9.1 -->

In type theory we are very limited in constructing identifications of functions.
The following example illustrates a case where type theory provides no rules to construct an identification between two maps, even though they are pointwise equal.

## Remark 9.1.1

<!-- rosetta-item: remark-9.1.1; latex-label: rmk:negnegbool -->

Consider the negation function `neg-bool : bool→bool` on the booleans, which was defined in Exercise 4.2.
Type theory does not provide any means to show that
```text
neg-bool∘neg-bool=id.
```
The best we can do is to construct an identification
```text
neg-neg-bool(b) : neg-bool(neg-bool(b))=b
```
for any `b:bool`.
Indeed, `neg-neg-bool` is defined using the induction principle of `bool`, by
```text
neg-neg-bool(true) ≔ refl
neg-neg-bool(false) ≔ refl.
```
Therefore we see that, while we cannot identify `neg-bool∘neg-bool` with `id`, we can define a *pointwise identification* between the values of `neg-bool∘neg-bool` and `id`.

<!-- rosetta-item-end: remark-9.1.1 -->

The observations in Remark 9.1.1 are an instance of a general phenomenon in type theory: it is often much easier to construct a *pointwise identification* between the values of two maps, than it is to construct an identification between those two maps.
In fact, the prevalent notion of sameness of maps is the notion of pointwise identification.
Since they are so important, we will give them a name and call them *homotopies*.

## Definition 9.1.2

<!-- rosetta-item: definition-9.1.2 -->

Let `f,g:Π(x:A) B(x)` be two dependent functions.
The type of **homotopies** from `f` to `g` is defined as the type of pointwise identifications, i.e., we define
```text
f~ g ≔ Π(x:A) f(x)=g(x).
```

<!-- rosetta-agda-block: definition-9.1.2-homotopies -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  infix 6 _~_
  _~_ : (f g : (x : A) → B x) → Type (l1 ⊔ l2)
  f ~ g = (x : A) → f x ＝ g x
```
<!-- rosetta-item-end: definition-9.1.2 -->

## Example 9.1.3

<!-- rosetta-item: example-9.1.3 -->

By Remark 9.1.1 we have a homotopy
```text
neg-neg-bool : neg-bool∘neg-bool~id.
```

<!-- rosetta-agda-block: remark-9.1.1-negation-involution -->

```agda
neg-neg-bool : (neg-bool ∘ neg-bool) ~ id
neg-neg-bool true = refl
neg-neg-bool false = refl
```

<!-- rosetta-agda-block: remark-9.2.6-involutions -->

```agda
module _
  {l : Level} {A : Type l}
  where

  is-involution : (A → A) → Type l
  is-involution f = (f ∘ f) ~ id
```
<!-- rosetta-item-end: example-9.1.3 -->

## Remark 9.1.4

<!-- rosetta-item: remark-9.1.4; latex-label: rmk:commuting-diagrams -->

We will use homotopies, for example, to express the commutativity of diagrams.
For example, we say that a triangle
<!-- rosetta-diagram: 962a48c2124b; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                 [B]

           [X]

Arrows:
- A --h--> B
- A --f--> X
- B --g--> X
```
**commutes** if it comes equipped with a homotopy `H:f~ g∘ h`.
Similarly, we say that a square
<!-- rosetta-diagram: f5ddaf96d5be; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [A] ----> [A']
  |         |
 [B] ----> [B']

Arrows:
- A --g--> A'
- A --f--> B
- A' --{f'}--> B'
- B --h--> B'
```
commutes if it comes equipped with a homotopy `h ∘ f~ f'∘ g`.

<!-- rosetta-item-end: remark-9.1.4 -->

Note that the type of homotopies `f~ g` is defined for dependent functions, and moreover the type of homotopies is itself a dependent function type.
The definition of homotopies is therefore set up in such a way that we may also consider homotopies *between* homotopies, and even further homotopies between those higher homotopies.
More concretely, if `H,K:f~ g` are two homotopies, then the type of homotopies `H~ K` between them is just the type
```text
Π(x:A) H(x)=K(x).
```

Since homotopies are pointwise identifications, we can use the groupoidal structure of identity types to also define the groupoidal structure of homotopies.
In this case, however, we state the groupoid laws as *homotopies* and *homotopies between homotopies* rather than as identifications.

## Definition 9.1.5

<!-- rosetta-item: definition-9.1.5; latex-label: defn:htpy_groupoid -->

For any type family `B` over `A` we define the operations on homotopies
```text
refl-htpy : Π(f:Π(x:A) B(x)) f~ f
inv-htpy : Π(f,g:Π(x:A) B(x)) (f~ g)→(g~ f)
concat-htpy : Π(f,g,h:Π(x:A) B(x)) (f~ g)→ ((g~ h)→ (f~ h))
```
pointwise by
```text
refl-htpy(f) ≔ λ x. refl
inv-htpy(H) ≔ λ x. H(x)^{-1}
concat-htpy(H,K) ≔ λ x. H(x) ∙ K(x).
```
We will often write `H^{-1}` for `inv-htpy(H)`, and `H ∙ K` for `concat-htpy(H,K)`.

<!-- rosetta-agda-block: definition-9.1.5-reflexive-homotopy -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  refl-htpy : {f : (x : A) → B x} → f ~ f
  refl-htpy x = refl

  refl-htpy' : (f : (x : A) → B x) → f ~ f
  refl-htpy' f = refl-htpy
```

<!-- rosetta-agda-block: definition-9.1.5-inverse-homotopy-code -->

```agda
  inv-htpy : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv-htpy H x = inv (H x)
```

<!-- rosetta-agda-block: definition-9.1.5-concatenation-homotopy-code -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  infixl 15 _∙h_
  _∙h_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  (H ∙h K) x = (H x) ∙ (K x)

  concat-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
  concat-htpy H h K x = concat (H x) (h x) (K x)

  concat-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ g → f ~ h
  concat-htpy' f K H = H ∙h K
```
<!-- rosetta-item-end: definition-9.1.5 -->

## Proposition 9.1.6

<!-- rosetta-item: proposition-9.1.6 -->

Homotopies satisfy the groupoid laws:

1.  Concatenation of homotopies is associative up to homotopy, i.e., there is a homotopy
```text
assoc-htpy(H,K,L) : (H ∙ K) ∙ L~H ∙ (K ∙ L)
```
    for any homotopies `H:f~ g`, `K:g~ h` and `L:h~ i`.

2.  Homotopies satisfy the left and right unit laws up to homotopy, i.e., there are homotopies
```text
left-unit-htpy(H) : refl-htpy_f ∙ H~ H
right-unit-htpy(H) : H ∙ refl-htpy_g~ H
```
    for any homotopy `H`.

3.  Homotopies satisfy the left and right inverse laws up to homotopy, i.e., there are homotopies
```text
left-inv-htpy(H) : H^{-1} ∙ H ~ refl-htpy_g
right-inv-htpy(H) : H ∙ H^{-1} ~ refl-htpy_f
```
    for any homotopy `H`.

### Proof

<!-- rosetta-item: subheading-9.1-proof -->

*Proof.* The homotopy `assoc-htpy(H,K,L)` is defined pointwise by
```text
assoc-htpy(H,K,L,x) ≔ assoc(H(x),K(x),L(x)).
```
The other homotopies are similarly defined pointwise. ◻

<!-- rosetta-agda-block: proposition-9.1.6-associativity -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k)
  where

  assoc-htpy : (H ∙h K) ∙h L ~ H ∙h (K ∙h L)
  assoc-htpy x = assoc (H x) (K x) (L x)

  inv-htpy-assoc-htpy : H ∙h (K ∙h L) ~ (H ∙h K) ∙h L
  inv-htpy-assoc-htpy = inv-htpy assoc-htpy
```

<!-- rosetta-agda-block: proposition-9.1.6-unit-laws -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  {f g : (x : A) → B x} {H : f ~ g}
  where

  left-unit-htpy : refl-htpy ∙h H ~ H
  left-unit-htpy x = left-unit

  inv-htpy-left-unit-htpy : H ~ refl-htpy ∙h H
  inv-htpy-left-unit-htpy = inv-htpy left-unit-htpy

  right-unit-htpy : H ∙h refl-htpy ~ H
  right-unit-htpy x = right-unit

  inv-htpy-right-unit-htpy : H ~ H ∙h refl-htpy
  inv-htpy-right-unit-htpy = inv-htpy right-unit-htpy
```

<!-- rosetta-agda-block: proposition-9.1.6-inverse-laws -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  {f g : (x : A) → B x} (H : f ~ g)
  where

  left-inv-htpy : inv-htpy H ∙h H ~ refl-htpy
  left-inv-htpy = left-inv ∘ H

  inv-htpy-left-inv-htpy : refl-htpy ~ inv-htpy H ∙h H
  inv-htpy-left-inv-htpy = inv-htpy left-inv-htpy

  right-inv-htpy : H ∙h inv-htpy H ~ refl-htpy
  right-inv-htpy = right-inv ∘ H

  inv-htpy-right-inv-htpy : refl-htpy ~ H ∙h inv-htpy H
  inv-htpy-right-inv-htpy = inv-htpy right-inv-htpy
```
<!-- rosetta-item-end: proposition-9.1.6 -->

Apart from the groupoid operations and their laws, we will occasionally need *whiskering* operations.
Whiskering operations are operations that allow us to compose homotopies with functions.
There are two situations where we want this:
<!-- rosetta-diagram: ffc214eead5e; review: pending -->

*Linear diagram (automatic draft).*

```text
 [A] ----> [B] ----> [C]       [A] ----> [B] ----> [C]

Arrows:
- A --unlabeled--> B
- A --unlabeled--> B
- A --⇓--> custom target
- B --unlabeled--> C
- A --unlabeled--> B
- B --unlabeled--> C
- B --unlabeled--> C
- B --⇓--> custom target
```

## Definition 9.1.7

<!-- rosetta-item: definition-9.1.7 -->

We define the following **whiskering** operations on homotopies:

1.  Suppose `H:f~ g` for two functions `f,g:A→ B`, and let `h:B→ C`.
We define
```text
h· H≔ λ x. ap_{h}(H(x)):h∘ f~ h∘ g.
```

2.  Suppose `f:A→ B` and `H:g~ h` for two functions `g,h:B→ C`.
We define
```text
H· f≔λ x. H(f(x)):g∘ f~ h∘ f.
```

<!-- rosetta-agda-block: definition-9.1.7-whiskering -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3}
  where

  left-whisker-comp :
    (h : {x : A} → B x → C x)
    {f g : (x : A) → B x} → f ~ g → h ∘ f ~ h ∘ g
  left-whisker-comp h H x = ap h (H x)

  infixr 17 _·l_
  _·l_ = left-whisker-comp
```

### Right whiskering of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : (x : A) → B x → Type l3}
  where

  right-whisker-comp :
    {g h : {x : A} (y : B x) → C x y}
    (H : {x : A} → g {x} ~ h {x})
    (f : (x : A) → B x) → g ∘ f ~ h ∘ f
  right-whisker-comp H f x = H (f x)

  infixl 16 _·r_
  _·r_ = right-whisker-comp
```
<!-- rosetta-item-end: definition-9.1.7 -->
