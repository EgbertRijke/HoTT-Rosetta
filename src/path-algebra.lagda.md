# Path algebra

```agda
module path-algebra where

open import universe-levels renaming (Type to UU ; Typeω to UUω)

open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
  ap-binary {x} {x'} p {y} {y'} q = ap (λ r → f r y) p ∙ ap (f x') q

infixl 1 equational-reasoning_
infixl 0 step-equational-reasoning

equational-reasoning_ :
  {l : Level} {X : UU l} (x : X) → x ＝ x
equational-reasoning x = refl

step-equational-reasoning :
  {l : Level} {X : UU l} {x y : X} →
  (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)
step-equational-reasoning p z q = p ∙ q

syntax step-equational-reasoning p z q = p ＝ z by q
```
