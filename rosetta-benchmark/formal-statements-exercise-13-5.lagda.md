# Formal Statements for Exercise 13.5

```agda
module formal-statements-exercise-13-5 where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-11-10-path-split-maps
open import section-12-1-propositions
```

## Problem statement

### Exercise 13.5(a)

Show that `is-path-split(f)` and `is-coh-invertible(f)` are propositions for any map `f : A → B`.
Conclude that we have equivalences

```text
  is-equiv(f) ≃ is-path-split(f) ≃ is-coh-invertible(f).
```

### Exercise 13.5(b)

Construct for any type `A` an equivalence

```text
  has-inverse(id_A) ≃ (id_A ~ id_A).
```

Note: We will use this fact in Exercise 22.5 to show that there are types for which `has-inverse(id[A]) ≄ is-equiv(id[A])`.

## Formal Statements

### Exercise 13.5(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-prop-is-path-split : is-prop (is-path-split f)
  is-prop-is-path-split = {!!}

  is-prop-is-coherently-invertible : is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible = {!!}

  equiv-is-equiv-is-path-split :
    is-equiv f ≃ is-path-split f
  equiv-is-equiv-is-path-split = {!!}

  equiv-is-equiv-is-coherently-invertible :
    is-equiv f ≃ is-coherently-invertible f
  equiv-is-equiv-is-coherently-invertible = {!!}
```

### Exercise 13.5(b)

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  compute-is-invertible-id :
    is-invertible (id {A = A}) ≃ (id {A = A} ~ id {A = A})
  compute-is-invertible-id = {!!}
```
