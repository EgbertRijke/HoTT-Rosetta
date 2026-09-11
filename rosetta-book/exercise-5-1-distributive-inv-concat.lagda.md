# Exercise 5.1

```agda
module exercise-5-1-distributive-inv-concat where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
```

## Problem statement

Show that the operation inverting identifications distributes over the concatenation operation, i.e., construct an identification

```text
distributive-inv-concat(p,q):(p ∙ q)^{-1} = q^{-1} ∙ p^{-1}.
```

for any `p:x = y` and `q:y = z`.

## Solution

<!-- rosetta-item: exercise-5-1 -->

<!-- rosetta-agda-block: exercise-5-1-distributive-inv-concat-block-1 -->

```agda
module _
  {l : Level} {A : UU l}
  where

  distributive-inv-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    inv (p ∙ q) ＝ inv q ∙ inv p
  distributive-inv-concat refl refl = refl
```
