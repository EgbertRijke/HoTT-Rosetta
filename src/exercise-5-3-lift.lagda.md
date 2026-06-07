# Exercise 5.3 Lifting identifications

```agda
module exercise-5-3-lift where

open import universe-levels
open import universe-levels using () renaming (Type to UU ; Typeω to UUω)

open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
```

## Problem statement

Let `B` be a type family over `A`, and consider an identification `p : a = x` in
`A`.
Construct for any `b : B(a)` an identification

```text
  lift_B(p,b) : (a, b) = (x, tr_B(p, b)).
```

In other words, an identification `p : x = y` in the *base type* `A` *lifts* to
an identification in `Σ(x : A) B(x)` for every element in `B(x)`, analogous to
the path lifting property for fibrations in homotopy theory.


## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  lift-eq-Σ :
    {x y : A} (p : x ＝ y) (b : B x) → (x , b) ＝ (y , tr B p b)
  lift-eq-Σ refl b = refl
```
