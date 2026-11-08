# Exercise 13.2

```agda
module exercise-13-2-identity-types-of-structured-function-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-6-the-structure-identity-principle
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-1-homotopy-operations-equivalences
```

## Problem statement

Characterize the identity types of the following types:

### Exercise 13.2(a)

The type `Σ(h : A → B) h(a) = b` of **pointed maps**, where `a : A` and `b : B` are given.

### Exercise 13.2(b)

The type `Σ(h : A → B) f ~ g ∘ h` of commuting triangles

```text
       h
  A ------> B
   \       /
  f \     / g
     \   /
      ∨ ∨
       X
```

where `f : A → X` and `g : B → X` are given.

### Exercise 13.2(c)

The type `Σ(h : X → Y) h ∘ f ~ g` of commuting triangles

```text
       A
      / \
   f /   \ g
    /     \
   ∨       ∨
  X ------> Y
       h
```

where `f : A → X` and `g : A → Y` are given.

### Exercise 13.2(d)

The type `Σ(i : A → X) Σ(j : B → Y) j ∘ f ~ g ∘ i` of commuting squares

```text
       i
  A ------> X
  |         |
f |         | g
  ∨         ∨
  B ------> Y
       j
```

where `f : A → B` and `g : X → Y` are given.

## Solutions

### Exercise 13.2(a)

This part is formalized by `extensionality-pointed-Π` in the [supplement to Section 19.4](section-19-4-homotopy-groups-of-types.lagda.md#extensionality-of-pointed-dependent-function-types-by-pointed-homotopies).

### Exercise 13.2(b)

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

### Exercise 13.2(c)

BENCHMARK PROBLEM

### Exercise 13.2(d)

BENCHMARK PROBLEM
