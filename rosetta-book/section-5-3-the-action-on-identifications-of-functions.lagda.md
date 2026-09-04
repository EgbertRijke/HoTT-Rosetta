# Section 5.3 The action on identifications of functions

```agda
module section-5-3-the-action-on-identifications-of-functions where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
```

<!-- rosetta-item: section-5.3 -->

Using the induction principle of the identity type we can show that every function preserves identifications.
In other words, every function sends identified elements to identified elements.
Note that this is a form of continuity for functions in type theory: if there is an identification that identifies two points `x` and `y` of a type `A`, then there also is an identification that identifies the values `f(x)` and `f(y)` in the codomain of `f`.

## Definition 5.3.1

<!-- rosetta-item: definition-5.3.1; latex-label: defn:ap -->

Let `f:A→ B` be a map.
We define the **action on paths** of `f` as an operation
```text
ap{f} : Π(x,y:A) (x = y)→(f(x) = f(y)).
```
Moreover, there are operations
```text
ap-id_A : Π(x,y:A) Π(p:x = y) p = ap_{id[A]}(p)
ap-comp(f,g) : Π(x,y:A) Π(p:x = y) ap_{g}(ap_{f}(p)) = ap_{g∘ f}(p).
```

### Construction

<!-- rosetta-item: subheading-5.3-construction -->

First we define `ap{f}` by the induction principle of identity types, taking
```text
ap{f}(refl)≔ refl.
```
Next, we construct `ap-id_A` by the induction principle of identity types, taking
```text
ap-id_A(refl) ≔ refl{refl}.
```
Finally, we construct `ap-comp(f,g)` by the induction principle of identity types, taking
```text
ap-comp(f,g,refl) ≔ refl{refl}.
```

<!-- rosetta-agda-block: section-5-3-the-action-on-identifications-of-functions-block-59 -->

```agda
ap :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {x y : A} →
  x ＝ y → f x ＝ f y
ap f refl = refl

module _
  {l : Level} {A : Type l} {x y : A}
  where

  ap-id : (p : x ＝ y) → ap id p ＝ p
  ap-id refl = refl

module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (g : B → C) (f : A → B)
  where

  ap-comp : {x y : A} (p : x ＝ y) → ap (g ∘ f) p ＝ (ap g ∘ ap f) p
  ap-comp refl = refl
```
<!-- rosetta-item-end: definition-5.3.1 -->

## Definition 5.3.2

<!-- rosetta-item: definition-5.3.2; latex-label: defn:ap-preserve -->

Let `f:A→ B` be a map.
Then there are identifications
```text
ap-refl(f,x) : ap_{f}(refl) = refl
ap-inv(f,p) : ap_{f}(p^{-1}) = ap_{f}(p)^{-1}
ap-concat(f,p,q) : ap_{f}(p ∙ q) = ap_{f}(p) ∙ ap_{f}(q)
```
for every `p:x = y` and `q:x = y`.

### Construction

<!-- rosetta-item: subheading-5.3-construction-2 -->

To construct `ap-refl(f,x)` we simply observe that `{ap_{f}(refl)}≐ {refl}`, so we take
```text
ap-refl(f,x)≔refl{refl}.
```
We construct `ap-inv(f,p)` by identification elimination on `p`, taking
```text
ap-inv(f,refl) ≔ refl{ap_{f}(refl)}.
```
Finally we construct `ap-concat(f,p,q)` by identification elimination on `p`, taking
```text
ap-concat(f,refl,q) ≔ refl{ap_{f}(q)}.
```

<!-- rosetta-agda-block: section-5-3-the-action-on-identifications-of-functions-block-115 -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (x y : A)
  where

  ap-refl : ap f (refl {x = x}) ＝ refl
  ap-refl = refl

  ap-inv : (p : x ＝ y) → ap f (inv p) ＝ inv (ap f p)
  ap-inv refl = refl

  ap-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ap f (p ∙ q) ＝ ap f p ∙ ap f q
  ap-concat refl q = refl
```
<!-- rosetta-item-end: definition-5.3.2 -->
