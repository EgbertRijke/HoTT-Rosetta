# Exercise 5.2 Inverse concatenation maps

```agda
module exercise-5-2-inverse-concatenation-maps where

open import universe-levels renaming (Type to UU ; Typeω to UUω)

open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
```

## Problem statement

For any `p : x = y`, `q : y = z`, and `r : x = z`, construct maps

```text
  inv-con(p,q,r)  :  (p ∙ q = r) → (q = p⁻¹ ∙ r) \\
  con-inv(p,q,r)  :  (p ∙ q = r) → (p = r ∙ q⁻¹).
```


## Solution

```agda
module _
  {l : Level} {A : UU l}
  where

  left-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ q ＝ r → q ＝ inv p ∙ r
  left-transpose-eq-concat refl q r s = s

  inv-left-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    q ＝ inv p ∙ r → p ∙ q ＝ r
  inv-left-transpose-eq-concat refl q r s = s

  right-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ q ＝ r → p ＝ r ∙ inv q
  right-transpose-eq-concat p refl r s = (inv right-unit ∙ s) ∙ inv right-unit

  inv-right-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ＝ r ∙ inv q → p ∙ q ＝ r
  inv-right-transpose-eq-concat p refl r s = right-unit ∙ (s ∙ right-unit)
```
