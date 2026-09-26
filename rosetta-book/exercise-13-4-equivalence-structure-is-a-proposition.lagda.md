# Exercise 13.4

```agda
module exercise-13-4-equivalence-structure-is-a-proposition where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-1-identity-types-contractible
open import exercise-10-3-contractible-equivalences
open import exercise-10-5-contractible-products
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import exercise-11-2-paths-along-equivalences
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import exercise-12-6-truncated-sigma-types
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
```

## Problem statement

Let `f : A → B` be a function.

### Exercise 13.4(a)

Show that if `f` is an equivalence, then the type `Σ(g : B → A) f ∘ g ~ id` of sections of `f` is contractible.

### Exercise 13.4(b)

Show that if `f` is an equivalence, then the type `Σ(h : B → A) h ∘ f ~ id` of retractions of `f` is contractible.

### Exercise 13.4(c)

Show that `is-equiv(f)` is a proposition.

### Exercise 13.4(d)

Show that for any two equivalences `e, e' : A ≃ B`, the canonical map

```text
  (e = e') → (e ~ e')
```

is an equivalence.

### Exercise 13.4 (e)

Show that the type `A ≃ B` is a `k`-type if both `A` and `B` are `k`-types.

## Solutions

### Exercise 13.4(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-section-is-equiv : {f : A → B} → is-equiv f → is-contr (section f)
    is-contr-section-is-equiv {f} is-equiv-f =
      is-contr-equiv'
        ( (b : B) → fiber f b)
        ( distributive-Π-Σ)
        ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))
```

### Exercise 13.4(b)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-retraction-is-equiv :
      {f : A → B} → is-equiv f → is-contr (retraction f)
    is-contr-retraction-is-equiv {f} is-equiv-f =
      is-contr-equiv'
        ( Σ (B → A) (λ h → h ∘ f ＝ id))
        ( equiv-tot (λ h → equiv-funext))
        ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)
```

### Exercise 13.4(c)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-product
      ( is-contr-section-is-equiv is-equiv-f)
      ( is-contr-retraction-is-equiv is-equiv-f)

  abstract
    is-property-is-equiv : (f : A → B) → (H K : is-equiv f) → is-contr (H ＝ K)
    is-property-is-equiv f H =
      is-prop-is-contr (is-contr-is-equiv-is-equiv H) H

  is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
  pr1 (is-equiv-Prop f) = is-equiv f
  pr2 (is-equiv-Prop f) = is-property-is-equiv f

  eq-equiv-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → e ＝ e'
  eq-equiv-eq-map-equiv = eq-type-subtype is-equiv-Prop

  abstract
    is-emb-map-equiv :
      is-emb (map-equiv {A = A} {B = B})
    is-emb-map-equiv = is-emb-inclusion-subtype is-equiv-Prop

  is-injective-map-equiv :
    is-injective (map-equiv {A = A} {B = B})
  is-injective-map-equiv = is-injective-is-emb is-emb-map-equiv

  emb-map-equiv : (A ≃ B) ↪ (A → B)
  pr1 emb-map-equiv = map-equiv
  pr2 emb-map-equiv = is-emb-map-equiv
```

### Exercise 13.4(d)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  _~e_ = htpy-equiv

  extensionality-equiv : (f g : A ≃ B) → (f ＝ g) ≃ htpy-equiv f g
  extensionality-equiv f =
    extensionality-type-subtype
      ( is-equiv-Prop)
      ( pr2 f)
      ( refl-htpy' (pr1 f))
      ( λ g → equiv-funext)

  abstract
    is-torsorial-htpy-equiv :
      (e : A ≃ B) → is-torsorial (htpy-equiv e)
    is-torsorial-htpy-equiv e =
      fundamental-theorem-id'
        ( map-equiv ∘ extensionality-equiv e)
        ( is-equiv-map-equiv ∘ extensionality-equiv e)

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  eq-htpy-equiv : {e e' : A ≃ B} → htpy-equiv e e' → e ＝ e'
  eq-htpy-equiv {e} {e'} = map-inv-equiv (extensionality-equiv e e')

  htpy-eq-equiv : {e e' : A ≃ B} → e ＝ e' → htpy-equiv e e'
  htpy-eq-equiv {e} {e'} = map-equiv (extensionality-equiv e e')

  htpy-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → htpy-equiv e e'
  htpy-eq-map-equiv = htpy-eq
```

### Exercise 13.4(e)

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
  is-trunc-equiv-is-trunc k H K =
    is-trunc-Σ
      ( is-trunc-function-type k K)
      ( λ f →
        is-trunc-Σ
          ( is-trunc-Σ
            ( is-trunc-function-type k H)
            ( λ g →
              is-trunc-Π k (λ y → is-trunc-Id K (f (g y)) y)))
          ( λ _ →
            is-trunc-Σ
              ( is-trunc-function-type k H)
              ( λ h →
                is-trunc-Π k (λ x → is-trunc-Id H (h (f x)) x))))

type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  UU (l1 ⊔ l2)
type-equiv-Truncated-Type A B =
  type-Truncated-Type A ≃ type-Truncated-Type B

is-trunc-type-equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  is-trunc k (type-equiv-Truncated-Type A B)
is-trunc-type-equiv-Truncated-Type A B =
  is-trunc-equiv-is-trunc _
    ( is-trunc-type-Truncated-Type A)
    ( is-trunc-type-Truncated-Type B)

equiv-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k) (B : Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (equiv-Truncated-Type A B) = type-equiv-Truncated-Type A B
pr2 (equiv-Truncated-Type A B) = is-trunc-type-equiv-Truncated-Type A B
```

## Supplement

### The groupoid laws for equivalences

#### Composition of equivalences is associative

```agda
associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ((g ∘e f) ∘e e) ＝ (g ∘e (f ∘e e))
associative-comp-equiv e f g = eq-equiv-eq-map-equiv refl
```

#### Unit laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-unit-law-equiv : (e : X ≃ Y) → (id-equiv ∘e e) ＝ e
  left-unit-law-equiv e = eq-equiv-eq-map-equiv refl

  right-unit-law-equiv : (e : X ≃ Y) → (e ∘e id-equiv) ＝ e
  right-unit-law-equiv e = eq-equiv-eq-map-equiv refl
```

#### A coherence law for the unit laws for composition of equivalences

```agda
coh-unit-laws-equiv :
  {l : Level} {X : UU l} →
  left-unit-law-equiv (id-equiv {A = X}) ＝
  right-unit-law-equiv (id-equiv {A = X})
coh-unit-laws-equiv = ap eq-equiv-eq-map-equiv refl
```

#### Inverse laws for composition of equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-inverse-law-equiv : (e : X ≃ Y) → ((inv-equiv e) ∘e e) ＝ id-equiv
  left-inverse-law-equiv e =
    eq-htpy-equiv (is-retraction-map-inv-is-equiv (is-equiv-map-equiv e))

  right-inverse-law-equiv : (e : X ≃ Y) → (e ∘e (inv-equiv e)) ＝ id-equiv
  right-inverse-law-equiv e =
    eq-htpy-equiv (is-section-map-inv-is-equiv (is-equiv-map-equiv e))
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  inv-inv-equiv : (e : X ≃ Y) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv e = eq-equiv-eq-map-equiv refl

  inv-inv-equiv' : (e : Y ≃ X) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv' e = eq-equiv-eq-map-equiv refl

  is-equiv-inv-equiv : is-equiv (inv-equiv {A = X} {B = Y})
  is-equiv-inv-equiv =
    is-equiv-is-invertible
      ( inv-equiv)
      ( inv-inv-equiv')
      ( inv-inv-equiv)

  equiv-inv-equiv : (X ≃ Y) ≃ (Y ≃ X)
  pr1 equiv-inv-equiv = inv-equiv
  pr2 equiv-inv-equiv = is-equiv-inv-equiv
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  where

  distributive-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    inv-equiv (f ∘e e) ＝ (inv-equiv e) ∘e (inv-equiv f)
  distributive-inv-comp-equiv e f =
    eq-htpy-equiv
      ( λ x →
        map-eq-transpose-equiv-inv
          ( f ∘e e)
          ( ( ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv f))) ∙
            ( ap
              ( λ g → map-equiv (f ∘e (g ∘e (inv-equiv f))) x)
              ( inv (right-inverse-law-equiv e)))))

  distributive-map-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    map-inv-equiv (f ∘e e) ＝ map-inv-equiv e ∘ map-inv-equiv f
  distributive-map-inv-comp-equiv e f =
    ap map-equiv (distributive-inv-comp-equiv e f)
```

### Precomposition of equivalences by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : B ≃ C) → (f ∘e e) ∘e inv-equiv e ＝ f
  is-retraction-precomp-equiv-inv-equiv e f =
    eq-htpy-equiv (λ x → ap (map-equiv f) (is-section-map-inv-equiv e x))

  is-section-precomp-equiv-inv-equiv :
    (e : A ≃ B) (f : A ≃ C) → (f ∘e inv-equiv e) ∘e e ＝ f
  is-section-precomp-equiv-inv-equiv e f =
    eq-htpy-equiv (λ x → ap (map-equiv f) (is-retraction-map-inv-equiv e x))

  is-equiv-precomp-equiv-equiv :
    (e : A ≃ B) → is-equiv (λ (f : B ≃ C) → f ∘e e)
  is-equiv-precomp-equiv-equiv e =
    is-equiv-is-invertible
      ( _∘e inv-equiv e)
      ( is-section-precomp-equiv-inv-equiv e)
      ( is-retraction-precomp-equiv-inv-equiv e)

equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
pr1 (equiv-precomp-equiv e C) = _∘e e
pr2 (equiv-precomp-equiv e C) = is-equiv-precomp-equiv-equiv e
```
