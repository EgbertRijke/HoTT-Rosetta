# Exercise 5.4

```agda
module exercise-5-4-mac-lane-pentagon where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
```

## Problem statement

Consider four consecutive identifications

<!-- rosetta-diagram: 59cb81762f07; review: pending -->

```text
 [a] ----> [b] ----> [c] ----> [d] ----> [e]

Arrows:
- a --p--> b
- b --q--> c
- c --r--> d
- d --s--> e
```

in a type `A`.
In this exercise we will show that the **Mac Lane pentagon** for identifications commutes.

<div class="subexenum">

Construct the five identifications `α_1,…,α_5` in the pentagon

<!-- rosetta-diagram: 9ea155e46c09; review: pending -->

```text
                        [((p ∙ q) ∙ r) ∙ s]                             [(p ∙ q) ∙ (r ∙ s)]

[(p ∙ (q ∙ r)) ∙ s]                                                                             [p ∙ (q ∙ (r ∙ s))]

                                                [p ∙ ((q ∙ r) ∙ s)]

Arrows:
- ((p ∙ q) ∙ r) ∙ s --α_4--> (p ∙ q) ∙ (r ∙ s)
- ((p ∙ q) ∙ r) ∙ s --α_1--> (p ∙ (q ∙ r)) ∙ s
- (p ∙ q) ∙ (r ∙ s) --α_5--> p ∙ (q ∙ (r ∙ s))
- (p ∙ (q ∙ r)) ∙ s --α_2--> p ∙ ((q ∙ r) ∙ s)
- p ∙ ((q ∙ r) ∙ s) --α_3--> p ∙ (q ∙ (r ∙ s))
```

where `α_1`, `α_2`, and `α_3` run counter-clockwise, and `α_4` and `α_5` run clockwise.

Show that

```text
(α_1 ∙ α_2) ∙ α_3 = α_4 ∙ α_5.
```

</div>

## Solution

<!-- rosetta-item: exercise-5-4 -->

<!-- rosetta-agda-block: exercise-5-4-mac-lane-pentagon-block-1 -->

```agda
module _
  {l : Level} {A : UU l} {x y z w v : A}
  where

  coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) → UU l
  coherence-pentagon-identifications
    top top-left top-right bottom-left bottom-right =
    top-left ∙ bottom-left ＝ (top ∙ top-right) ∙ bottom-right

mac-lane-pentagon :
  {l : Level} {A : UU l} {a b c d e : A}
  (p : a ＝ b) (q : b ＝ c) (r : c ＝ d) (s : d ＝ e) →
  let α₁ = (ap (_∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (p ∙_) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in
    coherence-pentagon-identifications α₁ α₄ α₂ α₅ α₃
mac-lane-pentagon refl refl refl refl = refl
```
