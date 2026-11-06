# Formal Statements for Exerecise 13.2

```agda
module formal-statements-exercise-13-2 where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
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

## Formalized statements

### Exercise 13.2(a)

```agda
pointed-type : (l : Level) → UU (lsuc l)
pointed-type l = Σ (UU l) (λ A → A)

module _
  {l : Level} (A : pointed-type l)
  where

  type-pointed-type : UU l
  type-pointed-type = pr1 A

  point-pointed-type : type-pointed-type
  point-pointed-type = pr2 A

pointed-map : {l1 l2 : Level} → pointed-type l1 → pointed-type l2 → UU (l1 ⊔ l2)
pointed-map A B =
  Σ ( type-pointed-type A → type-pointed-type B)
    ( λ f → f (point-pointed-type A) ＝ point-pointed-type B)

module _
  {l1 l2 : Level} {A : pointed-type l1} {B : pointed-type l2}
  (f : pointed-map A B)
  where

  map-pointed-map : type-pointed-type A → type-pointed-type B
  map-pointed-map = pr1 f

  preserves-point-pointed-map :
    map-pointed-map (point-pointed-type A) ＝ point-pointed-type B
  preserves-point-pointed-map = pr2 f

module _
  {l1 l2 : Level} {A : pointed-type l1} {B : pointed-type l2}
  (f : pointed-map A B)
  where

  htpy-pointed-map :
    (g : pointed-map A B) → UU (l1 ⊔ l2)
  htpy-pointed-map = {!!}

  refl-htpy-pointed-map :
    htpy-pointed-map f
  refl-htpy-pointed-map = {!!}

  htpy-eq-pointed-map :
    (g : pointed-map A B) → f ＝ g → htpy-pointed-map g
  htpy-eq-pointed-map = {!!}

  is-torsorial-htpy-pointed-map :
    is-torsorial htpy-pointed-map
  is-torsorial-htpy-pointed-map = {!!}

  is-equiv-htpy-eq-pointed-map :
    (g : pointed-map A B) → is-equiv (htpy-eq-pointed-map g)
  is-equiv-htpy-eq-pointed-map = {!!}

  extensionality-pointed-map :
    (g : pointed-map A B) → (f ＝ g) ≃ htpy-pointed-map g
  extensionality-pointed-map = {!!}

  eq-htpy-pointed-map :
    (g : pointed-map A B) → htpy-pointed-map g → f ＝ g
  eq-htpy-pointed-map = {!!}
```

### Exercise 13.2(b)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  hom-slice : UU (l1 ⊔ l2 ⊔ l3)
  hom-slice = Σ (A → B) (λ h → coherence-triangle-maps f g h)

  module _
    (h : hom-slice)
    where

    map-hom-slice : A → B
    map-hom-slice = pr1 h

    coherence-triangle-hom-slice : coherence-triangle-maps f g map-hom-slice
    coherence-triangle-hom-slice = pr2 h

  module _
    (h : hom-slice)
    where

    htpy-hom-slice :
      (k : hom-slice) → UU (l1 ⊔ l2 ⊔ l3)
    htpy-hom-slice = {!!}

    refl-htpy-hom-slice :
      htpy-hom-slice h
    refl-htpy-hom-slice = {!!}
  
    htpy-eq-slice :
      (k : hom-slice) → h ＝ k → htpy-hom-slice k
    htpy-eq-slice = {!!}
  
    is-torsorial-htpy-hom-slice :
      is-torsorial htpy-hom-slice
    is-torsorial-htpy-hom-slice = {!!}
  
    is-equiv-htpy-eq-slice :
      (k : hom-slice) → is-equiv (htpy-eq-slice k)
    is-equiv-htpy-eq-slice = {!!}
  
    extensionality-slice :
      (k : hom-slice) → (h ＝ k) ≃ htpy-hom-slice k
    extensionality-slice = {!!}
  
    eq-htpy-hom-slice :
      (k : hom-slice) → htpy-hom-slice k → h ＝ k
    eq-htpy-hom-slice = {!!}
```

### Exercise 13.2(c)

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : X → A) (g : X → B)
  where

  hom-coslice : UU (l1 ⊔ l2 ⊔ l3)
  hom-coslice = Σ (A → B) (λ h → coherence-triangle-maps' g h f)

  module _
    (h : hom-coslice)
    where

    map-hom-coslice : A → B
    map-hom-coslice = pr1 h

    coherence-triangle-hom-coslice :
      coherence-triangle-maps' g map-hom-coslice f
    coherence-triangle-hom-coslice = pr2 h

  module _
    (h : hom-coslice)
    where

    htpy-hom-coslice :
      (k : hom-coslice) → UU (l1 ⊔ l2 ⊔ l3)
    htpy-hom-coslice = {!!}

    refl-htpy-hom-coslice :
      htpy-hom-coslice h
    refl-htpy-hom-coslice = {!!}
  
    htpy-eq-coslice :
      (k : hom-coslice) → h ＝ k → htpy-hom-coslice k
    htpy-eq-coslice = {!!}
  
    is-torsorial-htpy-hom-coslice :
      is-torsorial htpy-hom-coslice
    is-torsorial-htpy-hom-coslice = {!!}
  
    is-equiv-htpy-eq-coslice :
      (k : hom-coslice) → is-equiv (htpy-eq-coslice k)
    is-equiv-htpy-eq-coslice = {!!}
  
    extensionality-coslice :
      (k : hom-coslice) → (h ＝ k) ≃ htpy-hom-coslice k
    extensionality-coslice = {!!}
  
    eq-htpy-hom-coslice :
      (k : hom-coslice) → htpy-hom-coslice k → h ＝ k
    eq-htpy-hom-coslice = {!!}
```

### Exercise 13.2.(d)

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  hom-arrow : UU {!!}
  hom-arrow = Σ (A → X) (λ i → Σ (B → Y) (λ j → coherence-square-maps i f g j))

  module _
    (h : hom-arrow)
    where

    top-map-hom-arrow : A → X
    top-map-hom-arrow = pr1 h

    bottom-map-hom-arrow : B → Y
    bottom-map-hom-arrow = pr1 (pr2 h)

    coherence-square-hom-arrow :
      coherence-square-maps top-map-hom-arrow f g bottom-map-hom-arrow
    coherence-square-hom-arrow = pr2 (pr2 h)

  module _
    (h : hom-arrow)
    where

    htpy-hom-arrow :
      (k : hom-arrow) → UU (l1 ⊔ l2 ⊔ l3)
    htpy-hom-arrow = {!!}

    refl-htpy-hom-arrow :
      htpy-hom-arrow h
    refl-htpy-hom-arrow = {!!}
  
    htpy-eq-arrow :
      (k : hom-arrow) → h ＝ k → htpy-hom-arrow k
    htpy-eq-arrow = {!!}
  
    is-torsorial-htpy-hom-arrow :
      is-torsorial htpy-hom-arrow
    is-torsorial-htpy-hom-arrow = {!!}
  
    is-equiv-htpy-eq-arrow :
      (k : hom-arrow) → is-equiv (htpy-eq-arrow k)
    is-equiv-htpy-eq-arrow = {!!}
  
    extensionality-arrow :
      (k : hom-arrow) → (h ＝ k) ≃ htpy-hom-arrow k
    extensionality-arrow = {!!}
  
    eq-htpy-hom-arrow :
      (k : hom-arrow) → htpy-hom-arrow k → h ＝ k
    eq-htpy-hom-arrow = {!!}
```
