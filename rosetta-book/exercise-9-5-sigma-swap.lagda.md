# Exercise 9.5

```agda
module exercise-9-5-sigma-swap where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
```

## Problem statement

### Exercise 9.5(a)

Let `A` and `B` be types, and let `C` be a family over `x : A, y : B`.
Construct an equivalence

```text
  (Σ(x : A) Σ(y : B) C(x,y)) ≃ (Σ(y : B) Σ(x : A) C(x,y)).
```

### Exercise 9.5(b)

Let `A` be a type, and let `B` and `C` be type families over `A`.
Construct an equivalence

```text
  (Σ(u : Σ(x : A) B(x)) C(pr1(u))) ≃ (Σ(v : Σ(x : A) C(x)) B(pr1(v))).
```

## Solution

### Exercise 9.5(a)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (a , b , c)) = b
  pr1 (pr2 (map-left-swap-Σ (a , b , c))) = a
  pr2 (pr2 (map-left-swap-Σ (a , b , c))) = c

  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (b , a , c)) = a
  pr1 (pr2 (map-inv-left-swap-Σ (b , a , c))) = b
  pr2 (pr2 (map-inv-left-swap-Σ (b , a , c))) = c

  is-retraction-map-inv-left-swap-Σ :
    map-inv-left-swap-Σ ∘ map-left-swap-Σ ~ id
  is-retraction-map-inv-left-swap-Σ (a , (b , c)) = refl

  is-section-map-inv-left-swap-Σ : map-left-swap-Σ ∘ map-inv-left-swap-Σ ~ id
  is-section-map-inv-left-swap-Σ (b , (a , c)) = refl

  is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
  is-equiv-map-left-swap-Σ =
    is-equiv-is-invertible
      map-inv-left-swap-Σ
      is-section-map-inv-left-swap-Σ
      is-retraction-map-inv-left-swap-Σ

  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = map-left-swap-Σ
  pr2 equiv-left-swap-Σ = is-equiv-map-left-swap-Σ
```

### Exercise 9.5(b)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  pr1 (pr1 (map-right-swap-Σ ((a , b) , c))) = a
  pr2 (pr1 (map-right-swap-Σ ((a , b) , c))) = c
  pr2 (map-right-swap-Σ ((a , b) , c)) = b

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  pr1 (pr1 (map-inv-right-swap-Σ ((a , c) , b))) = a
  pr2 (pr1 (map-inv-right-swap-Σ ((a , c) , b))) = b
  pr2 (map-inv-right-swap-Σ ((a , c) , b)) = c

  is-section-map-inv-right-swap-Σ :
    map-right-swap-Σ ∘ map-inv-right-swap-Σ ~ id
  is-section-map-inv-right-swap-Σ ((x , y) , z) = refl

  is-retraction-map-inv-right-swap-Σ :
    map-inv-right-swap-Σ ∘ map-right-swap-Σ ~ id
  is-retraction-map-inv-right-swap-Σ ((x , z) , y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-is-invertible
      map-inv-right-swap-Σ
      is-section-map-inv-right-swap-Σ
      is-retraction-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  pr1 equiv-right-swap-Σ = map-right-swap-Σ
  pr2 equiv-right-swap-Σ = is-equiv-map-right-swap-Σ
```
