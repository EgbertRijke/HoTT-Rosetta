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

<div class="subexenum">

Let `A` and `B` be types, and let `C` be a family over `x:A,y:B`.
Construct an equivalence
```text
(Σ(x:A) Σ(y:B) C(x,y)) ≃ (Σ(y:B) Σ(x:A) C(x,y)).
```

Let `A` be a type, and let `B` and `C` be type families over `A`.
Construct an equivalence
```text
(Σ(u:Σ(x:A) B(x)) C(pr 1(u))) ≃ (Σ(v:Σ(x:A) C(x)) B(pr 1(v))).
```

</div>

## Solution

<!-- rosetta-item: exercise-9-5 -->

### Part (b): swapping dependent families

<!-- rosetta-agda-block: exercise-9-5-right-swap -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3}
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
