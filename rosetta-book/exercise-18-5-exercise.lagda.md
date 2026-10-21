# Exercise 18.5

```agda
module exercise-18-5-exercise where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-6-truncated-sigma-types
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-7-universal-property-contractible-types
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
open import section-16-3-finite-types
open import section-17-5-classical-mathematics-with-the-univalence-axiom
open import section-18-5-set-truncations
```

## Problem statement

Consider a type `A` equipped with an element `a : A`.
Show that the following are equivalent:

1. The type `A` is connected.

2. There is an element of type `‖a = x‖` for any `x : A`.

3. For any family `B` over `A`, the fiber inclusion
    ```text
    iₐ : B(a) → Σ(x : A) B(x)
    ```
    defined in Exercise 12.13 is surjective.

## Solution

PARTIAL BENCHMARK PROBLEM

The implications 1 ⇒ 2 and 2 ⇒ 1 are formalized below as `mere-eq-is-0-connected` and `is-0-connected-mere-eq`, respectively. The equivalence with condition 3 remains to be formalized.

### Elements of 0-connected types are all merely equal

```agda
abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → all-elements-merely-equal A
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)
```

### A type is 0-connected if it is inhabited and all elements are merely equal

```agda
abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → all-elements-merely-equal A → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K =
    apply-universal-property-trunc-Prop H
      ( is-0-connected-Prop _)
      ( λ a → is-0-connected-mere-eq a (K a))
```

## Supplement

### A type is 0-connected iff any point inclusion is surjective

```agda
abstract
  is-0-connected-is-surjective-point :
    {l1 : Level} {A : UU l1} (a : A) →
    is-surjective (point a) → is-0-connected A
  is-0-connected-is-surjective-point a H =
    is-0-connected-mere-eq a
      ( λ x →
        apply-universal-property-trunc-Prop
          ( H x)
          ( mere-eq-Prop a x)
          ( λ u → unit-trunc-Prop (pr2 u)))

abstract
  is-surjective-point-is-0-connected :
    {l1 : Level} {A : UU l1} (a : A) →
    is-0-connected A → is-surjective (point a)
  is-surjective-point-is-0-connected a H x =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected H a x)
      ( trunc-Prop (fiber (point a) x))
      ( λ where refl → unit-trunc-Prop (star , refl))
```

### If A is 0-connected and B is k+1-truncated then every evaluation map (A → B) → B is k-truncated

```agda
is-trunc-map-ev-is-connected :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
  is-0-connected A → is-trunc (succ-𝕋 k) B →
  is-trunc-map k (ev-function B a)
is-trunc-map-ev-is-connected k {A} {B} a H K =
  is-trunc-map-comp k
    ( ev-function B star)
    ( precomp (point a) B)
    ( is-trunc-map-is-equiv k
      ( universal-property-contr-is-contr star is-contr-unit B))
    ( is-trunc-map-precomp-Π-is-surjective k
      ( is-surjective-point-is-0-connected a H)
      ( λ _ → (B , K)))
```

### The type `Type-With-Cardinality-ℕ` is connected

```agda
abstract
  is-0-connected-Type-With-Cardinality-ℕ :
    {l : Level} (n : ℕ) → is-0-connected (Type-With-Cardinality-ℕ l n)
  is-0-connected-Type-With-Cardinality-ℕ {l} n =
    is-0-connected-mere-eq
      ( raise-Fin-Type-With-Cardinality-ℕ l n)
      ( λ A →
        map-trunc-Prop
          ( ( eq-equiv-Type-With-Cardinality-ℕ n
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( A)) ∘
            ( map-equiv
              ( equiv-precomp-equiv
                ( inv-equiv (compute-raise l (Fin n)))
                ( type-Type-With-Cardinality-ℕ n A))))
          ( pr2 A))
```
