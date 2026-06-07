# Exercise 5.4 Mac Lane pentagon

```agda
module exercise-5-4-mac-lane-pentagon where

open import universe-levels renaming (Type to UU ; Typeω to UUω)

open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
```

## Problem statement

Consider four consecutive identifications

```text
      p       q       r       s
  a ===== b ===== c ===== d ===== e
```

in a type `A`.
In this exercise we will show that the **Mac Lane pentagon** for identifications
commutes.

## Problem 5.4(a)

Construct the five identifications `α₁, …, α₅` in the pentagon

```text
              α₄
  ((p ∙ q) ∙ r) ∙ s  =====  (p ∙ q) ∙ (r ∙ s)
          || α₁                         || α₅
          \/                            \/
  (p ∙ (q ∙ r)) ∙ s           p ∙ (q ∙ (r ∙ s))
          \\
           \\ α₂
            \\
             p ∙ ((q ∙ r) ∙ s)
                    ||
                    || α₃
                    \/
             p ∙ (q ∙ (r ∙ s)).
```

Here `α₁`, `α₂`, and `α₃` run counter-clockwise.
The identifications `α₄` and `α₅` run clockwise.

## Problem 5.4(b)

Show that
```text
  (α₁ ∙ α₂) ∙ α₃ = α₄ ∙ α₅.
```


## Solution

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
