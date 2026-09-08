# Section 14.4 Mapping propositional truncations into sets

```agda
module section-14-4-mapping-propositional-truncations-into-sets where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-8-1-decidability-and-decidable-equality
open import section-8-3-the-well-ordering-principle-of-natural-numbers
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-11-1-families-of-equivalences
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-5-the-strong-induction-principle-of-the-natural-numbers
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import exercise-6-3-order-natural-numbers
```

<!-- rosetta-item: section-14.4 -->

The universal property of the propositional truncation only applies when we want to define a map into a proposition.
However, in some situations we might want to map the propositional truncation into a type that is not a proposition.
Here we will see what we might do in such a case.

One strategy, if we want to define a map `‖A‖→ X`, is to find a type family `P` over `X` such that the type `Σ(x:X) P(x)` is a proposition.
In that case, we may use the universal property of the propositional truncation to obtain a map `‖A‖→ Σ(x:X) P(x)` from a map `A→ Σ(x:X) P(x)`, and then we simply compose with the projection map.

<!-- rosetta-agda-block: section-14.4-propositional-factorization-strategy -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {X : Type l2}
  (P : X → Type l3) (is-prop-total-P : is-prop (Σ X P))
  where

  map-trunc-Prop-via-propositional-subtype :
    (A → Σ X P) → type-trunc-Prop A → X
  map-trunc-Prop-via-propositional-subtype f =
    pr1 ∘ map-universal-property-trunc-Prop (Σ X P , is-prop-total-P) f
```


## Example 14.4.1

<!-- rosetta-item: example-14.4.1; latex-label: eg:global-choice-decidable-subtype-N -->

Consider a **decidable subtype** `P` of the natural numbers, i.e., a subtype `P:ℕ→Prop_𝒰` such that each `P(n)` is decidable.
We claim that there is a function
```text
‖Σ(x:ℕ) P(x)‖→Σ(x:ℕ) P(x).
```
Of course, we cannot directly use the universal property of the propositional truncation here.
However, there is at most one *minimal* natural number `x` in `P`.
In other words, we claim that the type
```text
Σ(x:ℕ) P(x)×is-lower-bound_P(x)(*)
```
is a proposition.
To see this, note that the type `is-lower-bound_P(x)` is a proposition.

<!-- rosetta-agda-block: example-14.4.1-lower-bounds-are-propositions -->

```agda
module _
  {l1 : Level} {P : ℕ → Type l1}
  where

  abstract
    is-prop-is-lower-bound-ℕ : (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
    is-prop-is-lower-bound-ℕ x =
      is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

  is-lower-bound-ℕ-Prop : (x : ℕ) → Prop l1
  pr1 (is-lower-bound-ℕ-Prop x) = is-lower-bound-ℕ P x
  pr2 (is-lower-bound-ℕ-Prop x) = is-prop-is-lower-bound-ℕ x
```

By the assumption that each `P(x)` is a proposition, it now follows that any two natural numbers `x,y:ℕ` that are in `P` and that are both lower bounds of `P` are equal as elements in the type of (\*) if and only if they are equal as natural numbers.

<!-- rosetta-agda-block: example-14.4.1-minimal-element-identities -->

```agda
module _
  {l : Level} (P : ℕ → Prop l)
  where

  equiv-identifications-minimal-element-ℕ :
    (s t : minimal-element-ℕ (λ n → type-Prop (P n))) →
    (s ＝ t) ≃ (pr1 s ＝ pr1 t)
  equiv-identifications-minimal-element-ℕ s t =
    equiv-ap-inclusion-subtype
      ( λ n → conjunction-Prop (P n) (is-lower-bound-ℕ-Prop n))
```

Furthermore, since both `x` and `y` are lower bounds of `P`, it follows that `x≤ y` and `y≤ x`, so indeed `x=y` holds.

<!-- rosetta-agda-block: example-14.4.1-minimal-elements-are-propositions -->

```agda
module _
  {l1 : Level} (P : ℕ → Prop l1)
  where

  abstract
    all-elements-equal-minimal-element-ℕ :
      all-elements-equal (minimal-element-ℕ (λ n → type-Prop (P n)))
    all-elements-equal-minimal-element-ℕ
      s@(pair x (pair p l)) t@(pair y (pair q k)) =
      map-section-is-equiv
        ( pr2 (equiv-identifications-minimal-element-ℕ P s t))
        ( antisymmetric-leq-ℕ x y (l y q) (k x p))

    is-prop-minimal-element-ℕ :
      is-prop (minimal-element-ℕ (λ n → type-Prop (P n)))
    is-prop-minimal-element-ℕ =
      is-prop-all-elements-equal all-elements-equal-minimal-element-ℕ

  minimal-element-ℕ-Prop : Prop l1
  pr1 minimal-element-ℕ-Prop = minimal-element-ℕ (λ n → type-Prop (P n))
  pr2 minimal-element-ℕ-Prop = is-prop-minimal-element-ℕ
```


By the observation that the type in (\*) is a proposition, we may define a map
```text
‖Σ(x:ℕ) P(x)‖→ Σ(x:ℕ) P(x)×is-lower-bound_P(x)
```
by the universal property of the propositional truncation.
A map
```text
Σ(x:ℕ) P(x)→Σ(x:ℕ) P(x)×is-lower-bound_P(x)
```
was constructed in Theorem 8.3.2 using the decidability of `P`.

<!-- rosetta-agda-block: example-14.4.1-natural-number-choice -->

```agda
abstract
  minimal-element-inhabited-decidable-subtype-ℕ :
    {l : Level} (P : ℕ → Prop l)
    (d : (n : ℕ) → is-decidable (type-Prop (P n))) →
    type-trunc-Prop (type-subtype P) →
    minimal-element-ℕ (λ n → type-Prop (P n))
  minimal-element-inhabited-decidable-subtype-ℕ P d =
    map-universal-property-trunc-Prop
      ( minimal-element-ℕ-Prop P)
      ( well-ordering-principle-ℕ (λ n → type-Prop (P n)) d)

  ε-operator-decidable-subtype-ℕ :
    {l : Level} (P : ℕ → Prop l)
    (d : (n : ℕ) → is-decidable (type-Prop (P n))) →
    type-trunc-Prop (type-subtype P) → type-subtype P
  ε-operator-decidable-subtype-ℕ P d t =
    tot (λ n → pr1) (minimal-element-inhabited-decidable-subtype-ℕ P d t)
```


As a corollary of this observation, we observe that there is also a map
```text
‖Σ(x:Fin{k}) P(x)‖→Σ(x:Fin{k}) P(x)
```
for any decidable subtype `P` over `Fin{k}`.

<!-- rosetta-agda-block: example-14.4.1-finite-type-choice -->

```agda
ε-operator-decidable-subtype-Fin :
  {l : Level} (k : ℕ) (P : Fin k → Prop l) →
  ((x : Fin k) → is-decidable (type-Prop (P x))) →
  type-trunc-Prop (type-subtype P) → type-subtype P
ε-operator-decidable-subtype-Fin zero-ℕ P d t =
  ex-falso (map-universal-property-trunc-Prop empty-Prop pr1 t)
ε-operator-decidable-subtype-Fin {l} (succ-ℕ k) P d t =
  map-Σ
    ( λ x → type-Prop (P x))
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( ε-operator-total-Q
      ( map-trunc-Prop
        ( map-Σ
          ( type-Prop ∘ Q)
          ( nat-Fin (succ-ℕ k))
          ( λ x →
            tr (λ y → type-Prop (P y)) (inv (is-section-nat-Fin k x))))
        ( t)))
  where
  Q : ℕ → Prop l
  Q n = P (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (type-Prop (Q n))
  is-decidable-Q n = d (mod-succ-ℕ k n)
  ε-operator-total-Q : type-trunc-Prop (type-subtype Q) → type-subtype Q
  ε-operator-total-Q = ε-operator-decidable-subtype-ℕ Q is-decidable-Q
```
<!-- rosetta-item-end: example-14.4.1 -->

## Remark 14.4.2

<!-- rosetta-item: remark-14.4.2; latex-label: rmk:global-choice -->

The function of type
```text
‖Σ(x:ℕ) P(x)‖→Σ(x:ℕ) P(x)
```
we constructed in Example 14.4.1 for decidable subtypes of `ℕ` is a rare case in which it is possible to obtain a function
```text
‖A‖→ A.
```
We say that the type `A` satisfies the **principle of global choice** if there is such a function `‖A‖→ A`.
Using the univalence axiom, we will see in Corollary 17.5.3 that not every type satisfies the principle of global choice.

<!-- rosetta-agda-block: remark-14.4.2-global-choice-for-a-type -->

```agda
ε-operator-Hilbert : {l : Level} → Type l → Type l
ε-operator-Hilbert A = type-trunc-Prop A → A
```
<!-- rosetta-item-end: remark-14.4.2 -->

More generally, we may wish to define a map `‖A‖→ B` where the type `B` is a set.
In this situation it is helpful to think of the propositional truncation of `A` as the quotient of the type `A` by the equivalence relation that relates every two elements of `A` with each other.
Propositional truncations can therefore also be characterized by the universal property of this quotient, which can be used to extend maps `f:A→ B` to maps `‖A‖→ B` when the type `B` is a set.
The idea is that a map `f:A→ B` into a set `B` extends to a map `‖A‖→ B` if it satisfies `f(x)=f(y)` for all `x,y:A`.

## Definition 14.4.3

<!-- rosetta-item: definition-14.4.3; latex-label: defn:weakly-constant -->

A map `f:A→ B` is said to be **weakly constant** if it comes equipped with an element of type
```text
is-weakly-constant(f) ≔ Π(x,y:A) f(x)=f(y).
```

<!-- rosetta-agda-block: definition-14.4.3-weakly-constant-maps -->

```agda
is-weakly-constant-map :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → Type (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → f x ＝ f y
```

<!-- rosetta-agda-block: definition-14.4.3-type-of-weakly-constant-maps -->

```agda
weakly-constant-map : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
weakly-constant-map A B = Σ (A → B) (is-weakly-constant-map)

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : weakly-constant-map A B)
  where

  map-weakly-constant-map : A → B
  map-weakly-constant-map = pr1 f

  is-weakly-constant-map-weakly-constant-map :
    is-weakly-constant-map map-weakly-constant-map
  is-weakly-constant-map-weakly-constant-map = pr2 f
```
<!-- rosetta-item-end: definition-14.4.3 -->

## Remark 14.4.4

<!-- rosetta-item: remark-14.4.4 -->

A constant map `A→ B` is a map of the form `const_b`.
A map `f:A→ B` is therefore constant if comes equipped with an element `b:B` and a homotopy `f~ const_b`.

<!-- rosetta-agda-block: remark-14.4.4-constant-map-predicate -->

```agda
is-constant-map :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → Type (l1 ⊔ l2)
is-constant-map {A = A} {B} f = Σ B (λ y → (x : A) → f x ＝ y)
```

This is a stronger notion than the notion of weakly constant maps, which doesn’t require there to be an element in `B`.

<!-- rosetta-agda-block: remark-14.4.4-constant-implies-weakly-constant -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-weakly-constant-map-is-constant-map :
    {f : A → B} → is-constant-map f → is-weakly-constant-map f
  is-weakly-constant-map-is-constant-map (b , H) x y = H x ∙ inv (H y)
```


One of the differences between constant maps and weakly constant maps manifests itself as follows: A type `A` is contractible if and only if the identity map on `A` is constant, while a type `A` is a proposition if and only if the identity map on `A` is weakly constant.

<!-- rosetta-agda-block: remark-14.4.4-contractibility-constant-identity -->

```agda
module _
  {l : Level} {A : Type l}
  where

  is-constant-id-is-contr : is-contr A → is-constant-map (id {A = A})
  is-constant-id-is-contr = tot (λ a → inv-htpy)

  is-contr-is-constant-id : is-constant-map (id {A = A}) → is-contr A
  is-contr-is-constant-id = tot (λ a → inv-htpy)
```

<!-- rosetta-agda-block: remark-14.4.4-propositions-weakly-constant-identity -->

```agda
module _
  {l : Level} {A : Type l}
  where

  is-weakly-constant-id-is-prop :
    is-prop A → is-weakly-constant-map (id {A = A})
  is-weakly-constant-id-is-prop = eq-is-prop'

  is-prop-is-weakly-constant-id :
    is-weakly-constant-map (id {A = A}) → is-prop A
  is-prop-is-weakly-constant-id = is-prop-all-elements-equal
```
<!-- rosetta-item-end: remark-14.4.4 -->

## Lemma 14.4.5

<!-- rosetta-item: lemma-14.4.5 -->

Consider a commuting triangle
<!-- rosetta-diagram: e3422d10b67e; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
[‖A‖]----> [B]

Arrows:
- A --η--> ‖A‖
- A --f--> B
- ‖A‖ --g--> B
```
where `B` is an arbitrary type.
Then the map `f` is weakly constant.

### Proof

<!-- rosetta-item: subheading-14.4-proof -->

*Proof.* Since `f` is assumed to be homotopic to `g∘ η`, it suffices to show that `g∘η` is weakly constant.
For any `x,y:A`, we have the identification `α(x,y):η(x)=η(y)` in `‖A‖`.
Using the action on paths of `g`, we obtain the identification
```text
ap_{g}(α(x,y)):g(η(x))=g(η(y))
```
in `B`. ◻

<!-- rosetta-agda-block: lemma-14.4.5-precomposition-is-weakly-constant -->

```agda
is-weakly-constant-map-precomp-unit-trunc-Prop :
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  (g : type-trunc-Prop A → B) →
  is-weakly-constant-map (g ∘ unit-trunc-Prop)
is-weakly-constant-map-precomp-unit-trunc-Prop g x y =
  ap g
    ( all-elements-equal-type-trunc-Prop
      ( unit-trunc-Prop x) (unit-trunc-Prop y))
```

<!-- rosetta-agda-block: lemma-14.4.5-factoring-through-truncation -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-weakly-constant-map-factors-through-trunc-Prop :
    (g : type-trunc-Prop A → B) →
    f ~ g ∘ unit-trunc-Prop → is-weakly-constant-map f
  is-weakly-constant-map-factors-through-trunc-Prop g H x y =
    H x ∙ is-weakly-constant-map-precomp-unit-trunc-Prop g x y ∙ inv (H y)
```
<!-- rosetta-item-end: lemma-14.4.5 -->

We now show, in a theorem due to Kraus \[citation: `Kraus`\], that any weakly constant map `f:A→ B` into a set `B` extends uniquely to a map `‖A‖→ B`.
We therefore conclude that, in order to define a map `‖A‖→ B` into a set `B` it suffices to define a map `f:A→ B` and show that it is weakly constant.

## Theorem 14.4.6

<!-- rosetta-item: theorem-14.4.6; latex-label: ex:weakly-constant-map -->

Let `A` be a type and let `B` be a set.
Then the map
```text
(‖A‖→ B)→ Σ(f:A→ B) Π(x,y:A) f(x)=f(y)
```
given by `g↦ (g∘η,λ x. λ y. ap_{g}(α(x,y)))` is an equivalence.

<!-- rosetta-agda-block: theorem-14.4.6-precomposition -->

```agda
precomp-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B) →
  (type-trunc-Prop A → B) → Σ (A → B) is-weakly-constant-map
pr1 (precomp-universal-property-set-quotient-trunc-Prop B is-set-B g) =
  g ∘ unit-trunc-Prop
pr2 (precomp-universal-property-set-quotient-trunc-Prop B is-set-B g) =
  is-weakly-constant-map-precomp-unit-trunc-Prop g
```


### Proof

<!-- rosetta-item: subheading-14.4-proof-2 -->

*Proof.* Consider a map `f:A→ B` equipped with `H:Π(x,y:A) f(x)=f(y)`.
We first show that `f` extends in at most one way to a map `‖A‖→ B`.
Let `g,h:‖A‖→ B` be two maps equipped with homotopies `f~ g∘η` and `f~ h∘η`.
In order to construct a homotopy `g~ h`, note that each identity type `g(x)=h(x)` is a proposition by the assumption that `B` is a set.
We can therefore construct a homotopy `g~ h` by the induction principle of propositional truncations.
By the induction principle, it suffices to construct a homotopy `g∘ η~ h∘η`, which we obtain from the homotopies `f~ g∘η` and `f~ h∘η`.

<!-- rosetta-agda-block: theorem-14.4.6-uniqueness-before-existence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
  {f : A → B}
  where

  unique-extension-into-set-trunc-Prop :
    (g h : type-trunc-Prop A → B) →
    f ~ g ∘ unit-trunc-Prop → f ~ h ∘ unit-trunc-Prop → g ~ h
  unique-extension-into-set-trunc-Prop g h H K =
    ind-trunc-Prop
      ( λ z → (g z ＝ h z , is-set-B (g z) (h z)))
      ( inv-htpy H ∙h K)
```


Since we’ve already proven uniqueness, it remains to construct an extension of the map `f`.
We first claim that the type
```text
Σ(b:B) ‖Σ(x:A) f(x)=b‖
```
is a proposition.
To see this, consider two elements `b` and `b'` in this subtype of `B`.
It suffices to show that `b=b'`.
Since `B` is assumed to be a set, the identity type `b=b'` is a proposition.
Therefore we may assume an element `x:A` equipped with `p:f(x)=b` and an element `x':A` equipped with `p':f(x')=b'`.
Using the assumption that `f` is weakly constant, we obtain the identification
<!-- rosetta-diagram: 44459fe1a1c2; review: pending -->

*Linear diagram (automatic draft).*

```text
 [b] ---->[f(x)]---->[f(x')]----> [b']

Arrows:
- b --p^{-1}--> f(x)
- f(x) --{H(x,x')}--> f(x')
- f(x') --{p'}--> b'
```

<!-- rosetta-agda-block: theorem-14.4.6-image-is-a-proposition -->

```agda
abstract
  all-elements-equal-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
    (f : A → B) → is-weakly-constant-map f →
    all-elements-equal (Σ B (λ b → type-trunc-Prop (fiber f b)))
  all-elements-equal-image-is-weakly-constant-map B is-set-B f H (x , s) (y , t) =
    map-section-is-equiv
      ( pr2 (equiv-ap-inclusion-subtype (λ b → trunc-Prop (fiber f b))))
      ( map-universal-property-trunc-Prop
        ( x ＝ y , is-set-B x y)
        ( λ u →
          map-universal-property-trunc-Prop
            ( x ＝ y , is-set-B x y)
            ( λ v → inv (pr2 u) ∙ H (pr1 u) (pr1 v) ∙ pr2 v)
            ( t))
        ( s))

abstract
  is-prop-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
    (f : A → B) → is-weakly-constant-map f →
    is-prop (Σ B (λ b → type-trunc-Prop (fiber f b)))
  is-prop-image-is-weakly-constant-map B is-set-B f H =
    is-prop-all-elements-equal
      ( all-elements-equal-image-is-weakly-constant-map B is-set-B f H)

image-weakly-constant-map-Prop :
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
  (f : A → B) → is-weakly-constant-map f → Prop (l1 ⊔ l2)
pr1 (image-weakly-constant-map-Prop B is-set-B f H) =
  Σ B (λ b → type-trunc-Prop (fiber f b))
pr2 (image-weakly-constant-map-Prop B is-set-B f H) =
  is-prop-image-is-weakly-constant-map B is-set-B f H
```

Now we observe that the map `f:A→ B` factors uniquely as follows
<!-- rosetta-diagram: 7e7385271393; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                [Σ(b:B) ‖Σ(x:A) f(x)=b‖]

           [B]

Arrows:
- A --g--> Σ(b:B) ‖Σ(x:A) f(x)=b‖
- A --f--> B
- Σ(b:B) ‖Σ(x:A) f(x)=b‖ --pr 1--> B
```
Indeed, the map `g` is given by `x↦(f(x),η(x,refl))`.
Since the codomain of `g` is a proposition, we obtain via the universal property of the propositional truncation of `A` a unique map `h:‖A‖→Σ(b:B) ‖Σ(x:A) f(x)=b‖` equipped with a homotopy `g~ h∘η`.
Now we obtain the map `pr 1∘ h:‖A‖→ B` equipped with the concatenated homotopy
```text
(pr 1∘ h)∘η ≐ pr 1∘ (h∘η) ~ pr 1∘ g ~ f.
```
 ◻

<!-- rosetta-agda-block: theorem-14.4.6-extension -->

```agda
map-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
  (f : A → B) → is-weakly-constant-map f → type-trunc-Prop A → B
map-universal-property-set-quotient-trunc-Prop B is-set-B f H =
  pr1 ∘
  map-universal-property-trunc-Prop
    ( image-weakly-constant-map-Prop B is-set-B f H)
    ( λ a → (f a , unit-trunc-Prop (a , refl)))

map-universal-property-set-quotient-trunc-Prop' :
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B) →
  Σ (A → B) is-weakly-constant-map → type-trunc-Prop A → B
map-universal-property-set-quotient-trunc-Prop' B is-set-B (f , H) =
  map-universal-property-set-quotient-trunc-Prop B is-set-B f H
```

<!-- rosetta-agda-block: theorem-14.4.6-computation -->

```agda
abstract
  htpy-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
    (f : A → B) (H : is-weakly-constant-map f) →
    map-universal-property-set-quotient-trunc-Prop B is-set-B f H ∘ unit-trunc-Prop ~ f
  htpy-universal-property-set-quotient-trunc-Prop B is-set-B f H a =
    ap
      ( pr1)
      ( eq-is-prop'
        ( is-prop-image-is-weakly-constant-map B is-set-B f H)
        ( map-universal-property-trunc-Prop
          ( image-weakly-constant-map-Prop B is-set-B f H)
          ( λ x → (f x , unit-trunc-Prop (x , refl)))
          ( unit-trunc-Prop a))
        ( f a , unit-trunc-Prop (a , refl)))
```

<!-- rosetta-agda-block: theorem-14.4.6-weak-constancy-is-a-property -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B)
  (f : A → B)
  where

  abstract
    is-prop-is-weakly-constant-map-Set : is-prop (is-weakly-constant-map f)
    is-prop-is-weakly-constant-map-Set =
      is-prop-Π (λ x → is-prop-Π (λ y → is-set-B (f x) (f y)))

  is-weakly-constant-map-prop-Set : Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-map-prop-Set = is-weakly-constant-map f
  pr2 is-weakly-constant-map-prop-Set = is-prop-is-weakly-constant-map-Set
```

<!-- rosetta-agda-block: theorem-14.4.6-two-inverses-and-equivalence -->

```agda
abstract
  is-section-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B) →
    (precomp-universal-property-set-quotient-trunc-Prop {A = A} B is-set-B ∘
     map-universal-property-set-quotient-trunc-Prop' B is-set-B) ~ id
  is-section-map-universal-property-set-quotient-trunc-Prop B is-set-B (f , H) =
    map-section-is-equiv
      ( pr2
        ( equiv-ap-inclusion-subtype
          ( is-weakly-constant-map-prop-Set B is-set-B)))
      ( eq-htpy (htpy-universal-property-set-quotient-trunc-Prop B is-set-B f H))

  is-retraction-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B) →
    (map-universal-property-set-quotient-trunc-Prop' B is-set-B ∘
     precomp-universal-property-set-quotient-trunc-Prop {A = A} B is-set-B) ~ id
  is-retraction-map-universal-property-set-quotient-trunc-Prop B is-set-B g =
    eq-htpy
      ( ind-trunc-Prop
        ( λ x →
          ( map-universal-property-set-quotient-trunc-Prop' B is-set-B
              (precomp-universal-property-set-quotient-trunc-Prop B is-set-B g) x ＝ g x ,
            is-set-B
              ( map-universal-property-set-quotient-trunc-Prop' B is-set-B
                (precomp-universal-property-set-quotient-trunc-Prop B is-set-B g) x)
              ( g x)))
        ( htpy-universal-property-set-quotient-trunc-Prop B is-set-B
          ( g ∘ unit-trunc-Prop)
          ( is-weakly-constant-map-precomp-unit-trunc-Prop g)))

  universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} (B : Type l2) (is-set-B : is-set B) →
    is-equiv (precomp-universal-property-set-quotient-trunc-Prop {A = A} B is-set-B)
  universal-property-set-quotient-trunc-Prop B is-set-B =
    is-equiv-is-invertible
      ( map-universal-property-set-quotient-trunc-Prop' B is-set-B)
      ( is-section-map-universal-property-set-quotient-trunc-Prop B is-set-B)
      ( is-retraction-map-universal-property-set-quotient-trunc-Prop B is-set-B)
```
<!-- rosetta-item-end: theorem-14.4.6 -->
