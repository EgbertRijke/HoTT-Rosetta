# Section 9.2 Bi-invertible maps

```agda
module section-9-2-bi-invertible-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-2-boolean-operations
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-6-successor-predecessor-integers
open import exercise-5-7-group-laws-integers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import exercise-7-4-successor-finite-types-addition
open import exercise-7-6-predecessor-finite-types
open import section-9-1-homotopies
```

<!-- rosetta-item: section-9.2 -->

We use homotopies to define sections and retractions of a map `f`, and to define what it means for a map `f` to be an equivalence.

## Definition 9.2.1

<!-- rosetta-item: definition-9.2.1 -->

Let `f:A→ B` be a function.

1.  The type of **sections** of `f` is defined to be the type
```text
sec(f) ≔ Σ(g:B→ A) f∘ g~ id[B].
```
In other words, a **section** of `f` is a map `g:B→ A` equipped with a homotopy `f∘ g~ id`.

2.  The type of **retractions** of `f` is defined to be the type
```text
retr(f) ≔ Σ(h:B→ A) h∘ f~ id[A].
```
If a map `f:A → B` has a retraction, we also say that `A` is a **retract** of `B`.

3.  We say that a function `f:A→ B` is an **equivalence** if it has both a section and a retraction, i.e., if it comes equipped with an element of type
```text
is-equiv(f)≔sec(f)×retr(f).
```
We will write `A ≃ B` for the type `Σ(f:A→ B) is-equiv(f)` of all equivalences from `A` to `B`.
For any equivalence `e:A≃ B` we define `e^{-1}` to be the section of `e`.

<!-- rosetta-agda-block: definition-9.2.1-sections -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B)
  where

  is-section : (B → A) → Type l2
  is-section g = f ∘ g ~ id
```

<!-- rosetta-agda-block: remark-9.2.6-invertible-maps -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-inverse : (A → B) → (B → A) → Type (l1 ⊔ l2)
  is-inverse f g = ((f ∘ g) ~ id) × ((g ∘ f) ~ id)

  is-section-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → f ∘ g ~ id
  is-section-is-inverse = pr1

  is-retraction-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → g ∘ f ~ id
  is-retraction-is-inverse = pr2
```

### The predicate that a map `f` is invertible

```agda
is-invertible :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → Type (l1 ⊔ l2)
is-invertible {A = A} {B} f = Σ (B → A) (is-inverse f)
```

<!-- rosetta-agda-block: definition-9.2.1-section-structure -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B)
  where

  section : Type (l1 ⊔ l2)
  section = Σ (B → A) (is-section f)

  map-section : section → B → A
  map-section = pr1

  is-section-map-section : (s : section) → is-section f (map-section s)
  is-section-map-section = pr2
```

<!-- rosetta-agda-block: definition-9.2.1-retractions -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-retraction : (f : A → B) (g : B → A) → Type l1
  is-retraction f g = g ∘ f ~ id

  retraction : (f : A → B) → Type (l1 ⊔ l2)
  retraction f = Σ (B → A) (is-retraction f)

  map-retraction : (f : A → B) → retraction f → B → A
  map-retraction f = pr1

  is-retraction-map-retraction :
    (f : A → B) (r : retraction f) → map-retraction f r ∘ f ~ id
  is-retraction-map-retraction f = pr2
```

<!-- rosetta-agda-block: definition-9.2.1-is-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-equiv : (A → B) → Type (l1 ⊔ l2)
  is-equiv f = section f × retraction f
```

<!-- rosetta-agda-block: definition-9.2.1-equivalence-components -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (H : is-equiv f)
  where

  section-is-equiv : section f
  section-is-equiv = pr1 H

  retraction-is-equiv : retraction f
  retraction-is-equiv = pr2 H

  map-section-is-equiv : B → A
  map-section-is-equiv = map-section f section-is-equiv

  map-retraction-is-equiv : B → A
  map-retraction-is-equiv = map-retraction f retraction-is-equiv

  is-section-map-section-is-equiv : is-section f map-section-is-equiv
  is-section-map-section-is-equiv = is-section-map-section f section-is-equiv

  is-retraction-map-retraction-is-equiv :
    is-retraction f map-retraction-is-equiv
  is-retraction-map-retraction-is-equiv =
    is-retraction-map-retraction f retraction-is-equiv
```

<!-- rosetta-agda-block: definition-9.2.1-equivalences -->

```agda
module _
  {l1 l2 : Level} (A : Type l1) (B : Type l2)
  where

  equiv : Type (l1 ⊔ l2)
  equiv = Σ (A → B) is-equiv

infix 6 _≃_

_≃_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
A ≃ B = equiv A B
```

<!-- rosetta-agda-block: definition-9.2.1-equivalence-map-components -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (e : A ≃ B)
  where

  map-equiv : A → B
  map-equiv = pr1 e

  is-equiv-map-equiv : is-equiv map-equiv
  is-equiv-map-equiv = pr2 e

  section-map-equiv : section map-equiv
  section-map-equiv = section-is-equiv is-equiv-map-equiv

  map-section-map-equiv : B → A
  map-section-map-equiv = map-section map-equiv section-map-equiv

  is-section-map-section-map-equiv :
    is-section map-equiv map-section-map-equiv
  is-section-map-section-map-equiv =
    is-section-map-section map-equiv section-map-equiv

  retraction-map-equiv : retraction map-equiv
  retraction-map-equiv = retraction-is-equiv is-equiv-map-equiv

  map-retraction-map-equiv : B → A
  map-retraction-map-equiv = map-retraction map-equiv retraction-map-equiv

  is-retraction-map-retraction-map-equiv :
    is-retraction map-equiv map-retraction-map-equiv
  is-retraction-map-retraction-map-equiv =
    is-retraction-map-retraction map-equiv retraction-map-equiv
```

<!-- rosetta-agda-block: definition-9.2.1-invertible-implies-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-equiv-is-invertible' : is-invertible f → is-equiv f
  is-equiv-is-invertible' (g , H , K) = ((g , H) , (g , K))

  is-equiv-is-invertible :
    (g : B → A) (H : f ∘ g ~ id) (K : g ∘ f ~ id) → is-equiv f
  is-equiv-is-invertible g H K = is-equiv-is-invertible' (g , H , K)
```
<!-- rosetta-item-end: definition-9.2.1 -->

## Remark 9.2.2

<!-- rosetta-item: remark-9.2.2 -->

An equivalence, as we defined it here, can be thought of as a *bi-invertible map*, since it comes equipped with a separate left and right inverse.
Explicitly, if `f` is an equivalence, then there are
```text
g : B→ A h : B→ A
G : f∘ g ~ id[B] H : h∘ f ~ id[A].
```

<!-- rosetta-item-end: remark-9.2.2 -->

## Example 9.2.3

<!-- rosetta-item: example-9.2.3; latex-label: thm:id_equiv -->

For any type `A`, the identity function `id:A→ A` is an equivalence, since it is its own section and its own retraction

<!-- rosetta-agda-block: example-9.2.3-identity-equivalence -->

```agda
module _
  {l : Level} {A : Type l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy

  id-equiv : A ≃ A
  pr1 id-equiv = id
  pr2 id-equiv = is-equiv-id
```
<!-- rosetta-item-end: example-9.2.3 -->

## Example 9.2.4

<!-- rosetta-item: example-9.2.4; latex-label: ex:neg_equiv -->

Since we have seen in Remark 9.1.1 that the negation function `neg-bool:bool→bool` on the booleans is its own inverse, it follows that `neg-bool` is an equivalence.

<!-- rosetta-agda-block: remark-9.2.6-involutions-are-equivalences -->

```agda
is-equiv-is-involution :
  {l : Level} {A : Type l} {f : A → A} → is-involution f → is-equiv f
is-equiv-is-involution {f = f} is-involution-f =
  is-equiv-is-invertible f is-involution-f is-involution-f
```

<!-- rosetta-agda-block: example-9.2.4-boolean-negation-equivalence -->

```agda
abstract
  is-equiv-neg-bool : is-equiv neg-bool
  is-equiv-neg-bool = is-equiv-is-involution neg-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
```
<!-- rosetta-item-end: example-9.2.4 -->

## Example 9.2.5

<!-- rosetta-item: example-9.2.5; latex-label: eg:is-equiv-succ-Z -->

The successor and predecessor functions on `ℤ` are equivalences by Exercise 5.6.
Furthermore, the function
```text
x↦ x+k
```
is an equivalence from `ℤ` to `ℤ`, for each `k:ℤ`.
This follows from the group laws on `ℤ`, proven in Exercise 5.7.
Indeed, the inverse of `x↦ x+k` is the map `x↦ x+(-k)`.
Finally, it also follows from the group laws on `ℤ` that the map `x↦ -x` is an equivalence.

The same holds for the finite types: the maps `succ-Fin_{k}`, `pred-Fin_{k}`, `add-Fin_{k}(x)` and `neg-Fin_{k}` are all equivalences on `Fin{k}`.

<!-- rosetta-agda-block: example-9.2.5-successor-predecessor-integer-equivalences -->

```agda
abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  is-equiv-succ-ℤ =
    is-equiv-is-invertible pred-ℤ is-section-pred-ℤ is-retraction-pred-ℤ

equiv-succ-ℤ : ℤ ≃ ℤ
pr1 equiv-succ-ℤ = succ-ℤ
pr2 equiv-succ-ℤ = is-equiv-succ-ℤ

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  is-equiv-pred-ℤ =
    is-equiv-is-invertible succ-ℤ is-retraction-pred-ℤ is-section-pred-ℤ

equiv-pred-ℤ : ℤ ≃ ℤ
pr1 equiv-pred-ℤ = pred-ℤ
pr2 equiv-pred-ℤ = is-equiv-pred-ℤ
```

<!-- rosetta-agda-block: example-9.2.5-integer-negation-equivalence -->

```agda
abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  is-equiv-neg-ℤ = is-equiv-is-involution neg-neg-ℤ

equiv-neg-ℤ : ℤ ≃ ℤ
pr1 equiv-neg-ℤ = neg-ℤ
pr2 equiv-neg-ℤ = is-equiv-neg-ℤ
```

<!-- rosetta-agda-block: example-9.2.5-finite-successor-predecessor-equivalences -->

```agda
is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
pr1 (pr1 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr1 (is-equiv-succ-Fin k)) = is-section-pred-Fin k
pr1 (pr2 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr2 (is-equiv-succ-Fin k)) = is-retraction-pred-Fin k

equiv-succ-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-succ-Fin k) = succ-Fin k
pr2 (equiv-succ-Fin k) = is-equiv-succ-Fin k

is-equiv-pred-Fin : (k : ℕ) → is-equiv (pred-Fin k)
pr1 (pr1 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr1 (is-equiv-pred-Fin k)) = is-retraction-pred-Fin k
pr1 (pr2 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr2 (is-equiv-pred-Fin k)) = is-section-pred-Fin k

equiv-pred-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-pred-Fin k) = pred-Fin k
pr2 (equiv-pred-Fin k) = is-equiv-pred-Fin k
```
<!-- rosetta-item-end: example-9.2.5 -->

## Remark 9.2.6

<!-- rosetta-item: remark-9.2.6; latex-label: rmk:has-inverse -->

More generally, if `f` **has an inverse** in the sense that we have a function `g:B→ A` equipped with homotopies `f∘ g~id[B]` and `g∘ f~id[A]`, then `f` is an equivalence.
We write
```text
has-inverse(f)≔Σ(g:B→ A) (f∘ g~ id[B])× (g∘ f~id[A]).
```
However, we did *not* define equivalences to be functions that have inverses.
The reason is that we would like that being an equivalence is a *property*, not a non-trivial structure on the map `f`.
This fact requires the function extensionality axiom, but we can already say that if a map `f` is an equivalence, then it has up to homotopy only one section and only one retraction (see Exercise 13.4).

The type `has-inverse(f)` on the other hand, turns out to be homotopically complicated.
In Exercise 22.5 we will see that the identity function `id[S^1]:S^1→S^1` on the circle is an example of a map for which
```text
has-inverse(id[S^1])≃ ℤ.
```

<!-- rosetta-item-end: remark-9.2.6 -->

Even though `is-equiv(f)` and `has-inverse(f)` can be wildly different types, there are maps back and forth between the two.
We have already observed in Remark 9.2.6 that there is a map
```text
has-inverse(f)→is-equiv(f).
```
The following proposition gives the converse implication.

## Proposition 9.2.7

<!-- rosetta-item: proposition-9.2.7; latex-label: lem:inv_equiv -->

Any map `f:A→ B` which is an equivalence, can be given the structure of an invertible map i.e., there is a map
```text
is-equiv(f)→has-inverse(f).
```

### Proof

<!-- rosetta-item: subheading-9.2-proof -->

*Proof.* First we construct for any equivalence `f` with right inverse `g` and left inverse `h` a homotopy `K:g~ h`.
For any `y:B`, we have
<!-- rosetta-diagram: cd2afc403d22; review: pending -->

*Linear diagram (automatic draft).*

```text
[g(y)]---->[hfg(y)]---->[h(y)]

Arrows:
- g(y) --H(g(y))^{-1}--> hfg(y)
- hfg(y) --ap_{h}(G(y))--> h(y)
```
In other words, the homotopy `K:g~ h` is defined to be `(H· g)^{-1} ∙ (h· G)`.
Using the homotopy `K` we are able to show that `g` is also a left inverse of `f`.
For `x:A` we have the identification
<!-- rosetta-diagram: c4fea148de3a; review: pending -->

*Linear diagram (automatic draft).*

```text
[gf(x)]---->[hf(x)]----> [x]

Arrows:
- gf(x) --K(f(x))--> hf(x)
- hf(x) --H(x)--> x
```
 ◻

<!-- rosetta-agda-block: proposition-9.2.7-equivalence-has-inverse -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-retraction-map-section-is-equiv :
    (H : is-equiv f) → is-retraction f (map-section-is-equiv H)
  is-retraction-map-section-is-equiv H =
    ( ( inv-htpy
        ( ( is-retraction-map-retraction-is-equiv H) ·r
          ( map-section-is-equiv H ∘ f))) ∙h
      ( map-retraction-is-equiv H ·l is-section-map-section-is-equiv H ·r f)) ∙h
    ( is-retraction-map-retraction-is-equiv H)

  is-invertible-is-equiv : is-equiv f → is-invertible f
  pr1 (is-invertible-is-equiv H) = map-section-is-equiv H
  pr1 (pr2 (is-invertible-is-equiv H)) = is-section-map-section-is-equiv H
  pr2 (pr2 (is-invertible-is-equiv H)) = is-retraction-map-section-is-equiv H
```
<!-- rosetta-item-end: proposition-9.2.7 -->

## Corollary 9.2.8

<!-- rosetta-item: corollary-9.2.8 -->

The inverse of an equivalence is again an equivalence.

### Proof

<!-- rosetta-item: subheading-9.2-proof-2 -->

*Proof.* Let `f:A→ B` be an equivalence.
By Proposition 9.2.7 it follows that the section of `f` is also a retraction.
Therefore it follows that the section is itself an invertible map, with inverse `f`.
Hence it is an equivalence. ◻

<!-- rosetta-item-end: corollary-9.2.8 -->

## Example 9.2.9

<!-- rosetta-item: example-9.2.9; latex-label: eg:laws-products-coproducts -->

Types, just as sets in classical mathematics, satisfy the usual laws of coproducts and products, such as unit laws, commutativity, and associativity.
These laws are formulated as equivalences:
```text
empty+B ≃ B A+empty ≃ A
A+B ≃ B+A (A+B)+C ≃ A+(B+C)
empty× B ≃ empty A×empty ≃ empty
unit× B ≃ B A×unit ≃ A
A× B ≃ B× A (A × B) × C ≃ A × (B × C)
A× (B+C) ≃ (A× B)+(A× C) (A+B)× C ≃ (A× C)+(B× C).
```
All of these equivalences are constructed in a similar way: the maps back and forth as well as the required homotopies are constructed using induction, or, more efficiently, using pattern matching.
For example, to show that cartesian products distribute from the left over coproducts, we construct maps
```text
α : A×(B+C)→ (A× B)+(A× C)
β : (A× B)+(A× C)→ A×(B+C)
```
as follows:
```text
α(x,inl(y)) ≔ inl(x,y) β(inl(x,y)) ≔ (x,inl(y))
α(x,inr(z)) ≔ inr(x,z) β(inr(x,z)) ≔ (x,inr(z)).
```
The homotopies `G:α∘β~id` and `H:β∘α~ id` are then defined by
```text
G(inl(x,y)) ≔ refl H(x,inl(y)) ≔ refl
G(inr(x,z)) ≔ refl H(x,inr(z)) ≔ refl.
```
We encourage the reader to write out the definitions of at least a few of these equivalences.

<!-- rosetta-item-end: example-9.2.9 -->

## Example 9.2.10

<!-- rosetta-item: example-9.2.10; latex-label: eg:laws-Sigma-types -->

The laws for cartesian products can be generalized to arbitrary `Σ`-types.
The absorption laws and unit laws, for instance, are as follows:
```text
Σ(x:empty) B(x) ≃ empty Σ(x:A) empty ≃ empty
Σ(x:unit) B(x) ≃ B(⋆) Σ(x:A) unit ≃ A.
```
Note that the right absorption law and the right unit law are exactly the same as the right absorption and unit laws for cartesian products.
The left absorption and unit laws are, however, formulated with a type family `B` over `empty` and over `unit`, and therefore they are slightly more general.

Commutativity cannot be generalized to `Σ`-types.
Associativity, on the other hand, can be expressed in two ways:
```text
Σ(w:Σ(x:A) B(x)) C(w) ≃Σ(x:A) Σ(y:B) C(pair(x,y))
Σ(w:Σ(x:A) B(x)) C(pr 1(w),pr 2(w)) ≃ Σ(x:A) Σ(y:B(x)) C(x,y).
```
In the first of these equivalences associativity is stated using a type family `C` over `Σ(x:A) B(x)` while in the second it is stated using a family of types `C(x,y)` indexed by `x:A` and `y:B(x)`.

Finally, we note that `Σ` also distributes over coproducts.
In other words, there are the following two equivalences:
```text
Σ(x:A) B(x)+C(x) ≃ (Σ(x:A) B(x))+(Σ(x:A) C(x))
Σ(w:A+B) C(w) ≃ (Σ(x:A) C(inl(x)))+(Σ(y:B) C(inr(y))).
```

<!-- rosetta-item-end: example-9.2.10 -->

## Remark 9.2.11

<!-- rosetta-item: remark-9.2.11 -->

We haven’t stated any laws involving function types or dependent function types, because it requires the function extensionality principle to prove them.

<!-- rosetta-item-end: remark-9.2.11 -->
