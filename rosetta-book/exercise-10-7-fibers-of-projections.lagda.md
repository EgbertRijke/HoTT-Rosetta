# Exercise 10.7

```agda
module exercise-10-7-fibers-of-projections where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
```

## Problem statement

Let `B` be a family of types over `A`, and consider the projection map

```text
  pr1 : (Σ(x : A) B(x)) → A.
```

### Exercise 10.7(a)

Show that for any `a : A`, the map

```text
  λ ((x,y),p). tr_B(p,y) : fib(pr1,a) → B(a),
```

is an equivalence.

### Exercise 10.7(b)

Show that the following are equivalent:

1. The projection map `pr1` is an equivalence.

2. The type `B(x)` is contractible for each `x : A`.

### Exercise 10.7(c)

Consider a dependent function `b : Π(x : A) B(x)`.
Show that the following are equivalent:

1. The map

   ```text
     λ x. (x,b(x)) : A → Σ(x : A) B(x)
   ```

   is an equivalence.

2. The type `B(x)` is contractible for each `x : A`.

## Solutions

### Exercise 10.7(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fiber-pr1 : fiber (pr1 {B = B}) a → B a
  map-fiber-pr1 ((x , y) , p) = tr B p y

  map-inv-fiber-pr1 : B a → fiber (pr1 {B = B}) a
  map-inv-fiber-pr1 b = (a , b) , refl

  is-section-map-inv-fiber-pr1 :
    is-section map-fiber-pr1 map-inv-fiber-pr1
  is-section-map-inv-fiber-pr1 b = refl

  is-retraction-map-inv-fiber-pr1 :
    is-retraction map-fiber-pr1 map-inv-fiber-pr1
  is-retraction-map-inv-fiber-pr1 ((.a , y) , refl) = refl

  abstract
    is-equiv-map-fiber-pr1 : is-equiv map-fiber-pr1
    is-equiv-map-fiber-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1
        is-retraction-map-inv-fiber-pr1

  equiv-fiber-pr1 : fiber (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-pr1 = map-fiber-pr1
  pr2 equiv-fiber-pr1 = is-equiv-map-fiber-pr1

  abstract
    is-equiv-map-inv-fiber-pr1 : is-equiv map-inv-fiber-pr1
    is-equiv-map-inv-fiber-pr1 =
      is-equiv-is-invertible
        map-fiber-pr1
        is-retraction-map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1

  inv-equiv-fiber-pr1 : B a ≃ fiber (pr1 {B = B}) a
  pr1 inv-equiv-fiber-pr1 = map-inv-fiber-pr1
  pr2 inv-equiv-fiber-pr1 = is-equiv-map-inv-fiber-pr1
```

### Exercise 10.7(b)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-equiv-pr1-is-contr : ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
    is-equiv-pr1-is-contr is-contr-B =
      is-equiv-is-contr-map
        ( λ x →
          is-contr-equiv
            ( B x)
            ( equiv-fiber-pr1 B x)
            ( is-contr-B x))

  equiv-pr1 : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  pr1 (equiv-pr1 is-contr-B) = pr1
  pr2 (equiv-pr1 is-contr-B) = is-equiv-pr1-is-contr is-contr-B

  right-unit-law-Σ-is-contr : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  right-unit-law-Σ-is-contr = equiv-pr1

  abstract
    is-contr-is-equiv-pr1 : is-equiv (pr1 {B = B}) → ((a : A) → is-contr (B a))
    is-contr-is-equiv-pr1 is-equiv-pr1-B a =
      is-contr-equiv'
        ( fiber pr1 a)
        ( equiv-fiber-pr1 B a)
        ( is-contr-map-is-equiv is-equiv-pr1-B a)
```

### Exercise 10.7(c)

### Right unit law for dependent pair types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-inv-right-unit-law-Σ-is-contr :
    ((a : A) → is-contr (B a)) → A → Σ A B
  map-inv-right-unit-law-Σ-is-contr H a = (a , center (H a))

  is-section-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    pr1 ∘ map-inv-right-unit-law-Σ-is-contr H ~ id
  is-section-map-inv-right-unit-law-Σ-is-contr H = refl-htpy

  is-retraction-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    map-inv-right-unit-law-Σ-is-contr H ∘ pr1 ~ id
  is-retraction-map-inv-right-unit-law-Σ-is-contr H (a , b) =
    eq-pair-eq-fiber (eq-is-contr (H a))

  is-equiv-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    is-equiv (map-inv-right-unit-law-Σ-is-contr H)
  is-equiv-map-inv-right-unit-law-Σ-is-contr H =
    is-equiv-is-invertible
      ( pr1)
      ( is-retraction-map-inv-right-unit-law-Σ-is-contr H)
      ( is-section-map-inv-right-unit-law-Σ-is-contr H)

  inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) → A ≃ Σ A B
  pr1 (inv-right-unit-law-Σ-is-contr H) = map-inv-right-unit-law-Σ-is-contr H
  pr2 (inv-right-unit-law-Σ-is-contr H) =
    is-equiv-map-inv-right-unit-law-Σ-is-contr H
```

## Supplement

### The right unit law of cartesian product types with respect to contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-B : is-contr B)
  where

  right-unit-law-product-is-contr : A × B ≃ A
  right-unit-law-product-is-contr = right-unit-law-Σ-is-contr (λ _ → is-contr-B)

  inv-right-unit-law-product-is-contr : A ≃ A × B
  inv-right-unit-law-product-is-contr =
    inv-equiv right-unit-law-product-is-contr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : A → is-contr B)
  where

  right-unit-law-product-is-contr' : A × B ≃ A
  right-unit-law-product-is-contr' = right-unit-law-Σ-is-contr H
```
