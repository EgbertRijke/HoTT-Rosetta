# Section 5.3 The action on identifications of functions

```agda
module section-5-3-the-action-on-identifications-of-functions where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
```

Using the induction principle of the identity type we can show that every
function preserves identifications.
In other words, every function sends identified elements to identified elements.
Note that this is a form of continuity for functions in type theory: If there is
an identification that identifies two points `x` and `y` of a type `A`, then
there also is an identification that identifies the values `f(x)` and `f(y)` in
the codomain of `f`.

## Definition 5.3.1

Let `f : A → B` be a map. We define the **action on paths** of `f` as an
operation

```text
  ap_f : Π(x, y : A) x = y → f(x) = f(y).
```

Moreover, there are operations

```text
      ap-id_A  : Π(x, y : A) Π(p : x = y) p = ap_(id)(p),
  ap-comp(f,g) : Π(x, y : A) Π(p : x = y) ap_g(ap_f(p)) = ap_(g ∘ f)(p).
```

## Construction

First we define `ap_f` by the induction principle of identity types, taking

```text
  ap_f(refl) ≔ refl.
```

Next, we construct `ap-id_A` by the induction principle of identity types,
taking

```text
  ap-id_A(refl) ≔ refl.
```

Finally, we construct `ap-comp(f,g)` by the induction principle of identity
types, taking

```text
  ap-comp(f, g, refl) ≔ refl.
```

```agda
ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A} →
  x ＝ y → f x ＝ f y
ap f refl = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  ap-id : (p : x ＝ y) → ap id p ＝ p
  ap-id refl = refl

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  where

  ap-comp : {x y : A} (p : x ＝ y) → ap (g ∘ f) p ＝ (ap g ∘ ap f) p
  ap-comp refl = refl
```

## Definition 5.3.2

Let `f : A → B` be a map.
Then there are identifications

```text
       ap-refl(f, x) : ap_f(refl) = refl
        ap-inv(f, p) : ap_f(p⁻¹) = ap_f(p)⁻¹
  ap-concat(f, p, q) : ap_f(p ∙ q) = ap_f(p) ∙ ap_f(q)
```

for every `p : x = y` and `q : x = y`.

## Construction

To construct `ap-refl(f,x)` we simply observe that `ap_f(refl) ≐ refl`, so we
take

```text
  ap-refl(f,x) ≔ refl.
```

We construct `ap-inv(f,p)` by identification elimination on `p`, taking

```text
  ap-inv(f, refl) ≔ refl.
```

Finally we construct `ap-concat(f,p,q)` by identification elimination on `p`,
taking

```text
  ap-concat(f, refl, q)  ≔  refl.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : A)
  where

  ap-refl : ap f (refl {x = x}) ＝ refl
  ap-refl = refl

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  ap-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ap f (p ∙ q) ＝ ap f p ∙ ap f q
  ap-concat refl q = refl

  inv-ap-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ap f p ∙ ap f q ＝ ap f (p ∙ q)
  inv-ap-concat p q = inv (ap-concat p q)

  compute-right-refl-ap-concat :
    {x y : A} (p : x ＝ y) →
    ap-concat p refl ＝ ap (ap f) right-unit ∙ inv right-unit
  compute-right-refl-ap-concat refl = refl

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A}
  where

  ap-inv : (p : x ＝ y) → ap f (inv p) ＝ inv (ap f p)
  ap-inv refl = refl

  inv-ap-inv : (p : x ＝ y) → inv (ap f p) ＝ ap f (inv p)
  inv-ap-inv p = inv (ap-inv p)
```

## Supplementary definitions

### The binary action on identifications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
  ap-binary {x} {x'} p {y} {y'} q = ap (λ r → f r y) p ∙ ap (f x') q
```

### The action of functions on higher identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p q : x ＝ y} (f : A → B) (α : p ＝ q)
  where

  ap² : ap f p ＝ ap f q
  ap² = ap (ap f) α
```

## Agda-unimath sources

- The action on identifications of functions, with all its identifications, is defined in `foundation.action-on-identifications-functions`
