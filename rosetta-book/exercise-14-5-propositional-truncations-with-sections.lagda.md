# Exercise 14.5

```agda
module exercise-14-5-propositional-truncations-with-sections where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-9-2-bi-invertible-maps
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
```

## Problem statement

Consider a map `f : A → P` into a proposition `P`.

### Exercise 14.5(a)

Show that if there is a map `g : P → A`, then `f` is a propositional truncation.
Conclude that for any type `A` equipped with a point `a : A`, the constant map

```text
  const_⋆ : A → unit
```

is a propositional truncation of `A`.

### Exercise 14.5(b)

Show that if `A` is a proposition, then `f` is a propositional truncation if and only if `f` is an equivalence.
Conclude that if `A` is a proposition, then the identity function `id : A → A` is a propositional truncation.

## Solutions

### Exercise 14.5(a)

```agda
abstract
  is-propositional-truncation-has-section :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    (g : type-Prop P → A) → is-propositional-truncation P f
  is-propositional-truncation-has-section {A = A} P f g Q =
    is-equiv-has-converse-is-prop
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( λ h → h ∘ g)

abstract
  is-propositional-truncation-terminal-map :
    { l1 : Level} (A : UU l1) (a : A) →
    is-propositional-truncation unit-Prop (terminal-map A)
  is-propositional-truncation-terminal-map A a =
    is-propositional-truncation-has-section
      ( unit-Prop)
      ( terminal-map A)
      ( ind-unit a)
```

### Exercise 14.5(b)

```agda
abstract
  is-propositional-truncation-is-equiv :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    {f : type-hom-Prop P Q} →
    is-equiv f → is-propositional-truncation Q f
  is-propositional-truncation-is-equiv P Q {f} is-equiv-f R =
    is-equiv-precomp-is-equiv f is-equiv-f (type-Prop R)

abstract
  is-propositional-truncation-map-equiv :
    { l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    (e : type-equiv-Prop P Q) →
    is-propositional-truncation Q (map-equiv e)
  is-propositional-truncation-map-equiv P Q e R =
    is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Prop R)

abstract
  is-equiv-is-propositional-truncation :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) {f : type-hom-Prop P Q} →
    is-propositional-truncation Q f → is-equiv f
  is-equiv-is-propositional-truncation P Q {f} H =
    is-equiv-is-equiv-precomp-Prop P Q f H

abstract
  is-propositional-truncation-id :
    { l1 : Level} (P : Prop l1) →
    is-propositional-truncation P id
  is-propositional-truncation-id P Q = is-equiv-id
```

## Supplement

### Being empty is preserved under propositional truncations

```agda
abstract
  is-empty-type-trunc-Prop :
    {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
  is-empty-type-trunc-Prop f =
    map-universal-property-trunc-Prop empty-Prop f

abstract
  is-empty-type-trunc-Prop' :
    {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
  is-empty-type-trunc-Prop' f = f ∘ unit-trunc-Prop

iff-is-empty-type-trunc-Prop :
  {l1 : Level} {X : UU l1} →
  is-empty X ↔ is-empty (type-trunc-Prop X)
iff-is-empty-type-trunc-Prop =
  ( is-empty-type-trunc-Prop , is-empty-type-trunc-Prop')
```
