# Exercise 11.8

```agda
module exercise-11-8-total-map-retractions where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-10-2-contractible-retracts
open import exercise-10-3-contractible-equivalences
open import section-10-1-contractible-types
open import section-11-1-families-of-equivalences
```

## Problem statement

<div class="subexenum">

Let `f,g:Π(x:A) B(x)→ C(x)` be two families of maps.
Show that
```text
(Π(x:A) f(x)~ g(x))→ (tot(f)~ tot(g)).
```

Let `f:Π(x:A) B(x)→ C(x)` and let `g:Π(x:A) C(x)→ D(x)`.
Show that
```text
tot(λ x. g(x)∘ f(x))~ tot(g)∘tot(f).
```

For any family `B` over `A`, show that
```text
tot(λ x. id[B(x)])~id.
```

Let `a:A`, and let `B` be a type family over `A`.
Use Exercise 10.2 to show that if each `B(x)` is a retract of `a = x`, then `B(x)` is equivalent to `a = x` for every `x:A`.

Conclude that for any family of maps
```text
f : Π(x:A) (a=x) → B(x),
```
if each `f(x)` has a section, then `f` is a family of equivalences.

</div>

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-retraction :
      (i : (x : A) → B x → a ＝ x) →
      ((x : A) → retraction (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retraction i R =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot i)
          ( is-contr-retract-of
            ( Σ _ (λ y → a ＝ y))
            ( ( tot i) ,
              ( tot (λ x → pr1 (R x))) ,
              ( ( inv-htpy (preserves-comp-tot i (pr1 ∘ R))) ∙h
                ( tot-htpy (pr2 ∘ R)) ∙h
                ( tot-id B)))
            ( is-contr-Id a))
          ( is-contr-Id a))
```

