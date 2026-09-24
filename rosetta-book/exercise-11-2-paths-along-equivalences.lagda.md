# Exercise 11.2

```agda
module exercise-11-2-paths-along-equivalences where

open import universe-levels
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
```

## Problem statement

Consider an equivalence `e : A ≃ B`.
Construct an equivalence

```text
  p ↦ p̃ : (e(x) = y) ≃ (x = e⁻¹(y))
```

for every `x : A` and `y : B`, such that the triangle

```text
        ap_e(p̃) 
  e(x) ========= e(e⁻¹(y))
      \\       //
     p \\     // G(y)
        \\   //
         \\ //
           y
```

commutes for every `p : e(x) = y`.
In this diagram, the homotopy `G : e ∘ e⁻¹ ~ id` is the homotopy witnessing that `e⁻¹` is a section of `e`.

## Solution

### Transposing equalities along equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (is-section-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  map-inv-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  map-inv-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  eq-transpose-equiv' :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv' x y =
    ( equiv-concat
      ( inv (is-retraction-map-inv-equiv e x))
      ( map-inv-equiv e y)) ∘e
    ( equiv-ap (inv-equiv e) (map-equiv e x) y)

  map-eq-transpose-equiv' :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv' {x} {y} = map-equiv (eq-transpose-equiv' x y)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv-inv :
    (x : A) (y : B) → (y ＝ map-equiv e x) ≃ (map-inv-equiv e y ＝ x)
  eq-transpose-equiv-inv x y =
    ( inv-equiv (equiv-ap e _ _)) ∘e
    ( equiv-concat (is-section-map-inv-equiv e y) _)

  map-eq-transpose-equiv-inv :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv-inv {a} {b} = map-equiv (eq-transpose-equiv-inv a b)

  map-inv-eq-transpose-equiv-inv :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  map-inv-eq-transpose-equiv-inv {a} {b} =
    map-inv-equiv (eq-transpose-equiv-inv a b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  compute-refl-eq-transpose-equiv :
    {x : A} →
    map-eq-transpose-equiv e refl ＝ inv (is-retraction-map-inv-equiv e x)
  compute-refl-eq-transpose-equiv =
    map-eq-transpose-equiv-inv
      ( equiv-ap e _ (map-inv-equiv e _))
      ( ap inv (coherence-map-inv-equiv e _) ∙
        inv (ap-inv (map-equiv e) _))

  compute-refl-eq-transpose-equiv-inv :
    {x : A} →
    map-eq-transpose-equiv-inv e refl ＝ is-retraction-map-inv-equiv e x
  compute-refl-eq-transpose-equiv-inv {x} =
    map-eq-transpose-equiv-inv
      ( equiv-ap e _ _)
      ( ( right-unit) ∙
        ( coherence-map-inv-equiv e _))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  compute-map-eq-transpose-equiv :
    {x : A} {y : B} →
    map-eq-transpose-equiv e {x} {y} ~ map-eq-transpose-equiv' e
  compute-map-eq-transpose-equiv {x} refl =
    ( map-eq-transpose-equiv-inv
      ( equiv-ap e x _)
      ( ( ap inv (coherence-map-inv-equiv e x)) ∙
        ( inv (ap-inv (map-equiv e) (is-retraction-map-inv-equiv e x))))) ∙
    ( inv right-unit)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    coherence-triangle-identifications'
      ( p)
      ( is-section-map-inv-equiv e y)
      ( ap (map-equiv e) (map-eq-transpose-equiv e p))
  triangle-eq-transpose-equiv {x} {y} p =
    ( right-whisker-concat
      ( is-section-map-inv-equiv
        ( equiv-ap e x (map-inv-equiv e y))
        ( p ∙ inv (is-section-map-inv-equiv e y)))
      ( is-section-map-inv-equiv e y)) ∙
    ( is-section-inv-concat' (is-section-map-inv-equiv e y) p)

  triangle-eq-transpose-equiv-inv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    coherence-triangle-identifications'
      ( ap (map-equiv e) (map-eq-transpose-equiv-inv e p))
      ( p)
      ( is-section-map-inv-equiv e y)
  triangle-eq-transpose-equiv-inv {x} {y} p =
    inv
      ( is-section-map-inv-equiv
        ( equiv-ap e _ _)
        ( is-section-map-inv-equiv e y ∙ p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    coherence-triangle-identifications'
      ( ap (map-inv-equiv e) p)
      ( map-eq-transpose-equiv e p)
      ( is-retraction-map-inv-equiv e x)
  triangle-eq-transpose-equiv' {x} refl =
    ( left-whisker-concat
      ( is-retraction-map-inv-equiv e x)
      ( compute-map-eq-transpose-equiv e refl)) ∙
    ( is-section-inv-concat (is-retraction-map-inv-equiv e x) refl)

  triangle-eq-transpose-equiv-inv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    coherence-triangle-identifications
      ( map-eq-transpose-equiv-inv e p)
      ( is-retraction-map-inv-equiv e x)
      ( ap (map-inv-equiv e) p)
  triangle-eq-transpose-equiv-inv' {x} refl =
    compute-refl-eq-transpose-equiv-inv e

  right-inverse-eq-transpose-equiv :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( ( map-eq-transpose-equiv e (inv p)) ∙
      ( ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e x)) ＝
    ( refl)
  right-inverse-eq-transpose-equiv {x} refl =
    ( right-whisker-concat (compute-refl-eq-transpose-equiv e) _) ∙
    ( left-inv (is-retraction-map-inv-equiv e _))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  triangle-eq-transpose-equiv-concat :
    {x : A} {y z : B} (p : map-equiv e x ＝ y) (q : y ＝ z) →
    ( map-eq-transpose-equiv e (p ∙ q)) ＝
    ( map-eq-transpose-equiv e p ∙ ap (map-inv-equiv e) q)
  triangle-eq-transpose-equiv-concat refl refl = inv right-unit
```

