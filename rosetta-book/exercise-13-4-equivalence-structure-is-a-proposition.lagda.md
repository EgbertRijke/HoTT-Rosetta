# Exercise 13.4

```agda
module exercise-13-4-equivalence-structure-is-a-proposition where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
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
open import section-12-1-propositions
open import section-12-2-subtypes
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

BENCHMARK PROBLEM

## Supplement

### Taking the inverse equivalence distributes over composition

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
