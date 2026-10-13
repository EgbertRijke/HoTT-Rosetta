# Section 17.5 Classical mathematics with the univalence axiom

```agda
module section-17-5-classical-mathematics-with-the-univalence-axiom where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import exercise-7-5-observational-equality-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-3-sets
open import exercise-12-8-retracts-of-truncated-types
open import section-13-3-universal-properties
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-16-3-finite-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-17-6-the-binomial-types

```

In classical mathematics, the axiom of choice asserts that for any collection `X` of nonempty sets, there is a choice function `f` such that `f(x) ∈ x` for each `x ∈ X`.
The univalence axiom is consistent with the axiom of choice, but we have to be careful in our formulation of the axiom of choice to make it about sets.
A naive interpretation that would be applicable to all types, such as the assertion that every family `B` of inhabited types has a section, is not consistent with univalence.
We will use the type `BS₂` of `2`-element types for a counterexample.

## Proposition 17.5.1

The type

```text
  Σ(X : BS₂) X
```

of pointed `2`-element types is contractible.
Consequently, the canonical family of maps

```text
  (Fin₂ = X) → X
```
indexed by `X : BS₂`, is a family of equivalences.

### Proof

By the univalence axiom it follows that the type `Σ(X : BS₂) Fin₂ ≃ X` is contractible.
In order to show that `Σ(X : BS₂) X` is contractible, it therefore suffices to show that the map

```text
  f : (Fin₂ ≃ X) → X
```

given by `f(e) ≔ e(⋆)`, is an equivalence.
Since being an equivalence is a proposition by Exercise 13.4, we may assume an equivalence `α : Fin₂ ≃ X`, and we proceed by equivalence induction on `α`.
Therefore, it suffices to show that the map

```text
  f : (Fin₂ ≃ Fin₂) → Fin₂
```

give by `f(e) ≔ e(⋆)` is an equivalence.
Using the notation from Section 7.3, we define the inverse map `g` by

```text
     g(⋆) ≔ id
  g(i(⋆)) ≔ succ-Fin₂,
```

and it is a straightforward verification that `f` and `g` are inverse to each other. ◻

```agda
has-two-elements-Prop : {l : Level} → UU l → Prop l
has-two-elements-Prop X = has-cardinality-ℕ-Prop 2 X

has-two-elements : {l : Level} → UU l → UU l
has-two-elements X = type-Prop (has-two-elements-Prop X)

is-prop-has-two-elements : {l : Level} {X : UU l} → is-prop (has-two-elements X)
is-prop-has-two-elements {l} {X} = is-prop-type-Prop (has-two-elements-Prop X)

2-Element-Type : (l : Level) → UU (lsuc l)
2-Element-Type l = Type-With-Cardinality-ℕ l 2

type-2-Element-Type : {l : Level} → 2-Element-Type l → UU l
type-2-Element-Type = pr1

has-two-elements-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → has-two-elements (type-2-Element-Type X)
has-two-elements-type-2-Element-Type = pr2

is-finite-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-finite (type-2-Element-Type X)
is-finite-type-2-Element-Type X =
  is-finite-has-cardinality-ℕ 2 (has-two-elements-type-2-Element-Type X)

finite-type-2-Element-Type : {l : Level} → 2-Element-Type l → Finite-Type l
pr1 (finite-type-2-Element-Type X) = type-2-Element-Type X
pr2 (finite-type-2-Element-Type X) = is-finite-type-2-Element-Type X

standard-2-Element-Type : (l : Level) → 2-Element-Type l
standard-2-Element-Type l = raise-Fin-Type-With-Cardinality-ℕ l 2

type-standard-2-Element-Type : (l : Level) → UU l
type-standard-2-Element-Type l = type-2-Element-Type (standard-2-Element-Type l)

zero-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
zero-standard-2-Element-Type = map-raise (zero-Fin 1)

one-standard-2-Element-Type :
  {l : Level} → type-standard-2-Element-Type l
one-standard-2-Element-Type = map-raise (one-Fin 1)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-two-elements-equiv : X ≃ Y → has-two-elements X → has-two-elements Y
  has-two-elements-equiv e H =
    transitive-mere-equiv (Fin 2) X Y (unit-trunc-Prop e) H

  has-two-elements-equiv' : X ≃ Y → has-two-elements Y → has-two-elements X
  has-two-elements-equiv' e H =
    transitive-mere-equiv (Fin 2) Y X (unit-trunc-Prop (inv-equiv e)) H

is-inhabited-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → type-trunc-Prop (type-2-Element-Type X)
is-inhabited-2-Element-Type X =
  apply-universal-property-trunc-Prop
    ( has-two-elements-type-2-Element-Type X)
    ( trunc-Prop (type-2-Element-Type X))
    ( λ e → unit-trunc-Prop (map-equiv e (zero-Fin 1)))

is-set-has-two-elements :
  {l : Level} {X : UU l} → has-two-elements X → is-set X
is-set-has-two-elements H = is-set-has-cardinality-ℕ 2 H

is-set-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-set (type-2-Element-Type X)
is-set-type-2-Element-Type X =
  is-set-has-cardinality-ℕ 2 (has-two-elements-type-2-Element-Type X)

set-2-Element-Type :
  {l : Level} → 2-Element-Type l → Set l
pr1 (set-2-Element-Type X) = type-2-Element-Type X
pr2 (set-2-Element-Type X) = is-set-type-2-Element-Type X
```

### Characterizing identifications between general `2`-element types

```agda
equiv-2-Element-Type :
  {l1 l2 : Level} → 2-Element-Type l1 → 2-Element-Type l2 → UU (l1 ⊔ l2)
equiv-2-Element-Type X Y = equiv-Type-With-Cardinality-ℕ 2 X Y

id-equiv-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) → equiv-2-Element-Type X X
id-equiv-2-Element-Type X = id-equiv

equiv-eq-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → X ＝ Y → equiv-2-Element-Type X Y
equiv-eq-2-Element-Type X Y = equiv-eq-component-UU-Level

abstract
  is-torsorial-equiv-2-Element-Type :
    {l1 : Level} (X : 2-Element-Type l1) →
    is-torsorial (λ (Y : 2-Element-Type l1) → equiv-2-Element-Type X Y)
  is-torsorial-equiv-2-Element-Type X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-2-Element-Type :
    {l1 : Level} (X Y : 2-Element-Type l1) →
    is-equiv (equiv-eq-2-Element-Type X Y)
  is-equiv-equiv-eq-2-Element-Type = is-equiv-equiv-eq-component-UU-Level

eq-equiv-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → equiv-2-Element-Type X Y → X ＝ Y
eq-equiv-2-Element-Type X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-2-Element-Type X Y)

extensionality-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → (X ＝ Y) ≃ equiv-2-Element-Type X Y
pr1 (extensionality-2-Element-Type X Y) = equiv-eq-2-Element-Type X Y
pr2 (extensionality-2-Element-Type X Y) = is-equiv-equiv-eq-2-Element-Type X Y
```

### Characterization the identifications of `Fin 2` with a `2`-element type `X`

#### Evaluating an equivalence and an automorphism at `0 : Fin 2`

```agda
ev-zero-equiv-Fin-2 :
  {l1 : Level} {X : UU l1} → (Fin 2 ≃ X) → X
ev-zero-equiv-Fin-2 e = map-equiv e (zero-Fin 1)

ev-zero-aut-Fin-2 : (Fin 2 ≃ Fin 2) → Fin 2
ev-zero-aut-Fin-2 = ev-zero-equiv-Fin-2
```

#### Evaluating an automorphism at `0 : Fin 2` is an equivalence

```agda
aut-point-Fin-2 :
  Fin 2 → (Fin 2 ≃ Fin 2)
aut-point-Fin-2 (inl (inr star)) = id-equiv
aut-point-Fin-2 (inr star) = equiv-succ-Fin 2

abstract
  is-section-aut-point-Fin-2 :
    (ev-zero-aut-Fin-2 ∘ aut-point-Fin-2) ~ id
  is-section-aut-point-Fin-2 (inl (inr star)) = refl
  is-section-aut-point-Fin-2 (inr star) = refl

  is-retraction-aut-point-Fin-2' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    map-equiv e (zero-Fin 1) ＝ x →
    map-equiv e (one-Fin 1) ＝ y → htpy-equiv (aut-point-Fin-2 x) e
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inl (inr star)) p q (inr star) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inl (inr star)) (inr star) p q (inr star) = inv q
  is-retraction-aut-point-Fin-2' e
    (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
  is-retraction-aut-point-Fin-2' e
    (inr star) (inl (inr star)) p q (inr star) = inv q
  is-retraction-aut-point-Fin-2' e
    (inr star) (inr star) p q (inl (inr star)) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))
  is-retraction-aut-point-Fin-2' e
    (inr star) (inr star) p q (inr star) =
    ex-falso (Eq-Fin-eq 2 (is-injective-equiv e (p ∙ inv q)))

  is-retraction-aut-point-Fin-2 :
    (aut-point-Fin-2 ∘ ev-zero-aut-Fin-2) ~ id
  is-retraction-aut-point-Fin-2 e =
    eq-htpy-equiv
      ( is-retraction-aut-point-Fin-2' e
        ( map-equiv e (zero-Fin 1))
        ( map-equiv e (one-Fin 1))
        ( refl)
        ( refl))

abstract
  is-equiv-ev-zero-aut-Fin-2 : is-equiv ev-zero-aut-Fin-2
  is-equiv-ev-zero-aut-Fin-2 =
    is-equiv-is-invertible
      aut-point-Fin-2
      is-section-aut-point-Fin-2
      is-retraction-aut-point-Fin-2

equiv-ev-zero-aut-Fin-2 : (Fin 2 ≃ Fin 2) ≃ Fin 2
pr1 equiv-ev-zero-aut-Fin-2 = ev-zero-aut-Fin-2
pr2 equiv-ev-zero-aut-Fin-2 = is-equiv-ev-zero-aut-Fin-2
```

#### If `X` is a `2`-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where

  abstract
    is-equiv-ev-zero-equiv-Fin-2 :
      is-equiv (ev-zero-equiv-Fin-2 {l1} {type-2-Element-Type X})
    is-equiv-ev-zero-equiv-Fin-2 =
      apply-universal-property-trunc-Prop
        ( has-two-elements-type-2-Element-Type X)
        ( is-equiv-Prop (ev-zero-equiv-Fin-2))
        ( λ α →
          is-equiv-left-factor
            ( ev-zero-equiv-Fin-2)
            ( map-equiv (equiv-postcomp-equiv α (Fin 2)))
            ( is-equiv-comp
              ( map-equiv α)
              ( ev-zero-equiv-Fin-2)
              ( is-equiv-ev-zero-aut-Fin-2)
              ( is-equiv-map-equiv α))
            ( is-equiv-postcomp-equiv-equiv α))

  equiv-ev-zero-equiv-Fin-2 :
    (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
  pr1 equiv-ev-zero-equiv-Fin-2 = ev-zero-equiv-Fin-2
  pr2 equiv-ev-zero-equiv-Fin-2 = is-equiv-ev-zero-equiv-Fin-2

  equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 ≃ type-2-Element-Type X
  equiv-point-2-Element-Type =
    map-inv-equiv equiv-ev-zero-equiv-Fin-2

  map-equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 → type-2-Element-Type X
  map-equiv-point-2-Element-Type x = map-equiv (equiv-point-2-Element-Type x)

  map-inv-equiv-point-2-Element-Type :
    type-2-Element-Type X → type-2-Element-Type X → Fin 2
  map-inv-equiv-point-2-Element-Type x =
    map-inv-equiv (equiv-point-2-Element-Type x)

  is-section-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-equiv-point-2-Element-Type x ∘ map-inv-equiv-point-2-Element-Type x) ~
    id
  is-section-map-inv-equiv-point-2-Element-Type x =
    is-section-map-inv-equiv (equiv-point-2-Element-Type x)

  is-retraction-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-inv-equiv-point-2-Element-Type x ∘ map-equiv-point-2-Element-Type x) ~
    id
  is-retraction-map-inv-equiv-point-2-Element-Type x =
    is-retraction-map-inv-equiv (equiv-point-2-Element-Type x)

  compute-map-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    map-equiv-point-2-Element-Type x (zero-Fin 1) ＝ x
  compute-map-equiv-point-2-Element-Type =
    is-section-map-inv-equiv equiv-ev-zero-equiv-Fin-2

  is-unique-equiv-point-2-Element-Type :
    (e : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv (equiv-point-2-Element-Type (map-equiv e (zero-Fin 1))) e
  is-unique-equiv-point-2-Element-Type e =
    htpy-eq-equiv (is-retraction-map-inv-equiv equiv-ev-zero-equiv-Fin-2 e)
```

#### The type of pointed `2`-element types of any universe level is contractible

```agda
Pointed-2-Element-Type : (l : Level) → UU (lsuc l)
Pointed-2-Element-Type l = Σ (2-Element-Type l) type-2-Element-Type

abstract
  is-contr-pointed-2-Element-Type :
    {l : Level} → is-contr (Pointed-2-Element-Type l)
  is-contr-pointed-2-Element-Type {l} =
    is-contr-equiv'
      ( Σ ( 2-Element-Type l)
          ( equiv-2-Element-Type (standard-2-Element-Type l)))
      ( equiv-tot
        ( λ X →
          ( equiv-ev-zero-equiv-Fin-2 X) ∘e
          ( equiv-precomp-equiv (compute-raise-Fin l 2) (pr1 X))))
      ( is-torsorial-equiv-subuniverse
        ( has-cardinality-ℕ-Prop 2)
        ( standard-2-Element-Type l))
```

#### Completing the characterization of the identity type of the type of `2`-element types of arbitrary universe level

```agda
point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  standard-2-Element-Type l ＝ X → type-2-Element-Type X
point-eq-2-Element-Type refl = map-raise (zero-Fin 1)

abstract
  is-equiv-point-eq-2-Element-Type :
    {l : Level} (X : 2-Element-Type l) →
    is-equiv (point-eq-2-Element-Type {l} {X})
  is-equiv-point-eq-2-Element-Type {l} =
    fundamental-theorem-id
      ( is-contr-pointed-2-Element-Type)
      ( λ X → point-eq-2-Element-Type {l} {X})

equiv-point-eq-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  (standard-2-Element-Type l ＝ X) ≃ type-2-Element-Type X
pr1 (equiv-point-eq-2-Element-Type {l} {X}) =
  point-eq-2-Element-Type
pr2 (equiv-point-eq-2-Element-Type {l} {X}) =
  is-equiv-point-eq-2-Element-Type X

eq-point-2-Element-Type :
  {l : Level} {X : 2-Element-Type l} →
  type-2-Element-Type X → standard-2-Element-Type l ＝ X
eq-point-2-Element-Type =
  map-inv-equiv equiv-point-eq-2-Element-Type

is-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  is-identity-system (type-2-Element-Type {l1}) X x
is-identity-system-type-2-Element-Type X x =
  is-identity-system-is-torsorial X x (is-contr-pointed-2-Element-Type)

dependent-universal-property-identity-system-type-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) (x : type-2-Element-Type X) →
  dependent-universal-property-identity-system
    ( type-2-Element-Type {l1})
    { a = X}
    ( x)
dependent-universal-property-identity-system-type-2-Element-Type X x =
  dependent-universal-property-identity-system-is-torsorial x
    ( is-contr-pointed-2-Element-Type)
```


## Corollary 17.5.2

There is no dependent function

```text
  Π(X : BS₂) X.
```

### Proof

By Proposition 17.5.1 and Exercise 13.12, we have an equivalence

```text
  (Π(X : BS₂) Fin₂ = X) ≃ (Π(X : BS₂) X).
```

Note that `Π(X : BS₂) Fin₂ = X` is the type of contractions of `BS₂`, using the center of contraction `Fin₂`.
Therefore it suffices to show that `BS₂` is not contractible.
Recall from Exercise 10.1 that the identity types of contractible types are contractible.
On the other hand, it follows from Proposition 17.5.1 that the identity type `Fin₂ = Fin₂` in `BS₂` is equivalent to `Fin₂`.
This type isn’t contractible by Exercise 10.4.
We conclude that `BS₂` is not contractible. ◻

The family `X ↦ X` over `BS₂` is therefore an example of a family of nonempty types for which there are provably no sections.
In the following corollary we conclude more generally that there is no way to construct an element of an arbitrary inhabited type.

## Corollary 17.5.3

If `𝒰` is a univalent universe, then there is no **global choice** function

```text
  Π(A : 𝒰) ‖A‖ → A.
```

### Proof

Suppose `f : Π(A : 𝒰) ‖A‖ → A`.
By restricting `f` to the type of `2`-element types in `𝒰`, we obtain a function

```text
  Π(A : BS₂) ‖A‖ → A.
```

Note that every `2`-element type is inhabited, i.e., there is an element of type `‖A‖` for every `2`-element type `A`.
To see this, consider a type `A : 𝒰` such that `‖Fin₂ ≃ A‖`.
To obtain an element of type `‖A‖`, we may assume an equivalence `e : Fin₂ ≃ A`.
Then we have `η(e(0)) : ‖A‖`.

Since every `2`-element type is inhabited, we obtain a function `Π(A : BS₂) A`, which is impossible by Corollary 17.5.2. ◻

Corollary 17.5.3 is of philosophical importance.
It shows that the **principle of global choice** is incompatible with the univalence axiom, i.e., that there is no way to obtain construct a function `‖A‖ → A` for all types `A`.
In other words, we cannot obtain an element of `A` merely from the assumption that the type `A` is inhabited.
What is the obstruction?
It is the fact that no such choice of an element of `A` can be invariant under the automorphisms on `A`, i.e., under the self-equivalences on `A`.
Indeed, in the example where `A` is the `2`-element type `Fin₂` there are no fixed point of the equivalence `succ-Fin₂ : Fin₂ ≃ Fin₂`.
By the univalence axiom, there is an identification `p : Fin₂ = Fin₂` in `𝒰`, such that `tr(p,x) = succ-Fin₂(x)`.
If we had a function

```text
  f : Π(X : 𝒰) ‖X‖ → X,
```

the dependent action on paths of `f` would give an identification

```text
  apd_{f}(p) : succ-Fin₂(f(Fin₂,p,H))=f(Fin₂,p,η(0)).
```

In other words, it would give us a fixed point for the successor function on `Fin₂`.

This is perhaps a good moment to stress that the axiom of choice is really an axiom about *sets*, not about more general types.
And indeed, when we restrict the axiom of choice to sets, it turns out to be consistent with the univalence axiom and therefore safe to assume.
In this book, however, we will not have many applications for the axiom of choice and therefore we will not assume it, unless we explicitly say otherwise.

## Definition 17.5.4

The **axiom of choice** asserts that for any family `B` of inhabited sets indexed by a set `A`, the type of sections of `B` is also inhabited, i.e., it asserts that there is an element of type

```text
  AC_{𝒰}(A,B) ≔ (Π(x : A) ‖B(x)‖) → ‖Π(x : A) B(x)‖,
```

for every `A : Set_𝒰` and `B : A → Set_𝒰`.

Similar care has to be taken with the type theoretic formulation of the law of excluded middle.
It is again inconsistent to assume that every type is decidable.

## Theorem 17.5.5

There is no **global decidability function**

```text
  Π(X : 𝒰) is-decidable(X).
```

### Proof

Suppose there is such a dependent function `d`.
By restricting `d` to the subuniverse of `2`-element types, we obtain a dependent function

```text
  d : Π(X : BS₂) is-decidable(X).
```

However, each `2`-element type `X` is inhabited.
By Exercise 14.1 we obtain a function

```text
  is-decidable(X) → X
```

for each `2`-element type `X`.
Therefore, we obtain from `d` a dependent function `Π(X : BS₂) X`, which does not exist by Corollary 17.5.2. ◻

The law of excluded middle is really an axiom of propositional logic, and it is indeed consistent with the univalence axiom that every *proposition* is decidable.

## Definition 17.5.6

The **law of excluded middle** asserts that every proposition is decidable, i.e.,

```text
  LEM_𝒰 ≔ Π(P : Prop_𝒰) is-decidable(P).
```

We will again not assume the law of excluded middle, unless we say otherwise.
Nevertheless, we have seen in Chapter 8 that some propositions are already decidable without assuming the law of excluded middle, and decidability remains an important concept in type theory and mathematics.
