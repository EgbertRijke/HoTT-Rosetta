# Exercise 13.15

```agda
module exercise-13-15-morphisms-over-a-type where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-8-fiber-replacement
open import section-11-1-families-of-equivalences
open import section-11-6-the-structure-identity-principle
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import exercise-13-1-homotopy-operations-equivalences
open import exercise-13-4-equivalence-structure-is-a-proposition
```

## Problem statement

For any two maps `f : A → X` and `g : B → X`, define the type of **morphisms from `f` to `g` over `X`** by

```text
  hom-slice_X(f,g) ≔ Σ(h : A → B) f ~ g ∘ h.
```

In other words, the type `hom-slice_X(f,g)` is the type of maps `h : A → B` equipped with a homotopy witnessing that the triangle

```text
       h
  A ------> B
   \       /
  f \     / h
     \   /
      ∨ ∨ 
       X

```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  hom-slice :
    (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  hom-slice f g = Σ (A → B) (λ h → f ~ g ∘ h)

  map-hom-slice :
    (f : A → X) (g : B → X) → hom-slice f g → A → B
  map-hom-slice f g h = pr1 h

  triangle-hom-slice :
    (f : A → X) (g : B → X) (h : hom-slice f g) →
    f ~ g ∘ map-hom-slice f g h
  triangle-hom-slice f g h = pr2 h
```

Consider a family `P` of types over `X`.

### Exercise 13.15(a)

Show that the map

```text
  (Π(x:X) fib(f,x) → P(x)) → (Π(a : A) P(f(a)))
```

given by `h ↦ h_{f(a)}(a,refl)` is an equivalence.

### Exercise 13.15(b)

Construct three equivalences `α`, `β`, and `γ` as shown in the following diagram, and show that this triangle commutes:

```text
                              hom-slice_(f,g)
                                /         \
                               /           \
                            α /             \ β
                             /               \
                            ∨                 ∨
  Π(x:A) fib(f,x) → fib(g,x) ----------------> Π(a:A) fib(g,f(a))
                                     γ
```

Given a morphism `(h,H) : hom-slice_X(f,g)` over `X`, we also say that `α(h,H)` is its **action on fibers**.

### Exercise 13.15(c)

Given `(h,H) : hom-slice_X(f,g)`, show that the following are equivalent:

1. The map `h : A → B` is an equivalence.

2. The action on fibers

   ```text
     α(h,H):Π(x:X) fib(f, x)→fib(g, x)
   ```
    
   is a family of equivalences.

3. The precomposition function

   ```text
     - ∘ (h,H) : hom-slice_X(g,i) → hom-slice_X(f,i)
   ```
    
   given by `(k,K) ∘ (h,H) ≔ (k ∘ h,H ∙ (K · h))` is an equivalence for each map `i : C → X`.

Conclude that the type `Σ(h : A ≃ B) f ~ g ∘ h` is equivalent to the type of families of equivalences

```text
  Π(x:X) fib(f,x) ≃ fib(g,x).
```

## Solutions

BENCHMARK PROBLEM

### Exercise 13.15(b)

### Morphisms in the slice are equivalently described as families of maps between fibers

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  fiberwise-hom : (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  fiberwise-hom f g = (x : X) → fiber f x → fiber g x

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  fiberwise-hom-hom-slice : hom-slice f g → fiberwise-hom f g
  fiberwise-hom-hom-slice (h , H) = fiber-triangle f g h H

  hom-slice-fiberwise-hom : fiberwise-hom f g → hom-slice f g
  pr1 (hom-slice-fiberwise-hom α) a = pr1 (α (f a) (a , refl))
  pr2 (hom-slice-fiberwise-hom α) a = inv (pr2 (α (f a) (a , refl)))

  is-section-hom-slice-fiberwise-hom-eq-htpy :
    (α : fiberwise-hom f g) (x : X) →
    fiberwise-hom-hom-slice (hom-slice-fiberwise-hom α) x ~ α x
  is-section-hom-slice-fiberwise-hom-eq-htpy α .(f a) (a , refl) =
    eq-pair-eq-fiber (inv-inv (pr2 (α (f a) (a , refl))))

  is-section-hom-slice-fiberwise-hom :
    is-section fiberwise-hom-hom-slice hom-slice-fiberwise-hom
  is-section-hom-slice-fiberwise-hom α =
    eq-htpy (λ x → eq-htpy (is-section-hom-slice-fiberwise-hom-eq-htpy α x))

  is-retraction-hom-slice-fiberwise-hom :
    is-retraction fiberwise-hom-hom-slice hom-slice-fiberwise-hom
  is-retraction-hom-slice-fiberwise-hom (h , H) =
    eq-pair-eq-fiber (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-hom-hom-slice : is-equiv fiberwise-hom-hom-slice
    is-equiv-fiberwise-hom-hom-slice =
      is-equiv-is-invertible
        ( hom-slice-fiberwise-hom)
        ( is-section-hom-slice-fiberwise-hom)
        ( is-retraction-hom-slice-fiberwise-hom)

  equiv-fiberwise-hom-hom-slice : hom-slice f g ≃ fiberwise-hom f g
  pr1 equiv-fiberwise-hom-hom-slice = fiberwise-hom-hom-slice
  pr2 equiv-fiberwise-hom-hom-slice = is-equiv-fiberwise-hom-hom-slice

  abstract
    is-equiv-hom-slice-fiberwise-hom : is-equiv hom-slice-fiberwise-hom
    is-equiv-hom-slice-fiberwise-hom =
      is-equiv-is-invertible
        ( fiberwise-hom-hom-slice)
        ( is-retraction-hom-slice-fiberwise-hom)
        ( is-section-hom-slice-fiberwise-hom)

  equiv-hom-slice-fiberwise-hom :
    fiberwise-hom f g ≃ hom-slice f g
  pr1 equiv-hom-slice-fiberwise-hom = hom-slice-fiberwise-hom
  pr2 equiv-hom-slice-fiberwise-hom = is-equiv-hom-slice-fiberwise-hom
```

## Supplement

### Characterizing the identity type of morphisms in the slice over a type

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  coherence-htpy-hom-slice :
    (h h' : hom-slice f g) →
    map-hom-slice f g h ~ map-hom-slice f g h' →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-slice h h' H =
      coherence-triangle-homotopies'
        ( triangle-hom-slice f g h')
        ( g ·l H)
        ( triangle-hom-slice f g h)

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( coherence-htpy-hom-slice h h')

  extensionality-hom-slice :
    (h h' : hom-slice f g) → (h ＝ h') ≃ htpy-hom-slice h h'
  extensionality-hom-slice (h , H) =
    extensionality-Σ
      ( λ {h'} H' (K : h ~ h') → (H ∙h (g ·l K)) ~ H')
      ( refl-htpy)
      ( right-unit-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-concat-htpy right-unit-htpy H' ∘e equiv-funext)

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → h ＝ h'
  eq-htpy-hom-slice h h' = map-inv-equiv (extensionality-hom-slice h h')
```

### The predicate on a morphism in the slice of being an equivalence

```agda
is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)
```

### The type of equivalences in the slice

```agda
equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} →
  (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
equiv-slice {A = A} {B = B} f g = Σ (A ≃ B) (λ e → f ~ g ∘ map-equiv e)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (e : equiv-slice f g)
  where

  equiv-equiv-slice : A ≃ B
  equiv-equiv-slice = pr1 e

  map-equiv-slice : A → B
  map-equiv-slice = map-equiv equiv-equiv-slice

  is-equiv-map-equiv-slice : is-equiv map-equiv-slice
  is-equiv-map-equiv-slice = is-equiv-map-equiv equiv-equiv-slice

  coh-equiv-slice : f ~ g ∘ map-equiv-slice
  coh-equiv-slice = pr2 e

  hom-equiv-slice : hom-slice f g
  hom-equiv-slice = (map-equiv-slice , coh-equiv-slice)
```

### A morphism in the slice over `X` is an equivalence if and only if the induced map between fibers is a fiberwise equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-fiberwise-equiv-is-equiv-triangle :
      is-equiv h → is-fiberwise-equiv (fiber-triangle f g h H)
    is-fiberwise-equiv-is-equiv-triangle E =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fiber f)
          ( map-equiv-total-fiber g)
          ( tot (fiber-triangle f g h H))
          ( h)
          ( square-tot-fiber-triangle f g h H)
          ( is-equiv-map-equiv-total-fiber f)
          ( is-equiv-map-equiv-total-fiber g)
          ( E))

  abstract
    is-equiv-triangle-is-fiberwise-equiv :
      is-fiberwise-equiv (fiber-triangle f g h H) → is-equiv h
    is-equiv-triangle-is-fiberwise-equiv E =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fiber f)
        ( map-equiv-total-fiber g)
        ( tot (fiber-triangle f g h H))
        ( h)
        ( square-tot-fiber-triangle f g h H)
        ( is-equiv-map-equiv-total-fiber f)
        ( is-equiv-map-equiv-total-fiber g)
        ( is-equiv-tot-is-fiberwise-equiv E)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  abstract
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
      (t : hom-slice f g) → is-equiv (map-hom-slice f g t) →
      is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice (h , H) =
      is-fiberwise-equiv-is-equiv-triangle f g h H

  abstract
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
      (t : hom-slice f g) →
      ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
      is-equiv (map-hom-slice f g t)
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice (h , H) =
      is-equiv-triangle-is-fiberwise-equiv f g h H

  equiv-fiberwise-equiv-equiv-slice :
    equiv-slice f g ≃ fiberwise-equiv (fiber f) (fiber g)
  equiv-fiberwise-equiv-equiv-slice =
    equiv-Σ is-fiberwise-equiv (equiv-fiberwise-hom-hom-slice f g) α ∘e
    equiv-right-swap-Σ
    where
    α :
      (h : hom-slice f g) →
      is-equiv (map-hom-slice f g h) ≃
      is-fiberwise-equiv (map-equiv (equiv-fiberwise-hom-hom-slice f g) h)
    α h =
      equiv-iff-is-prop
        ( is-property-is-equiv _)
        ( is-prop-Π (λ _ → is-property-is-equiv _))
        ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice h)
        ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice h)

  equiv-equiv-slice-fiberwise-equiv :
    fiberwise-equiv (fiber f) (fiber g) ≃ equiv-slice f g
  equiv-equiv-slice-fiberwise-equiv =
    inv-equiv equiv-fiberwise-equiv-equiv-slice

  fiberwise-equiv-equiv-slice :
    equiv-slice f g → fiberwise-equiv (fiber f) (fiber g)
  fiberwise-equiv-equiv-slice =
    map-equiv equiv-fiberwise-equiv-equiv-slice

  equiv-fam-equiv-equiv-slice :
    equiv-slice f g ≃ fam-equiv (fiber f) (fiber g)
  equiv-fam-equiv-equiv-slice =
    inv-distributive-Π-Σ ∘e equiv-fiberwise-equiv-equiv-slice
```
