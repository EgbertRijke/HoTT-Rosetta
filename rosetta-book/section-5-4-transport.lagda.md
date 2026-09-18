# Section 5.4 Transport

```agda
module section-5-4-transport where

open import universe-levels renaming (UU to Type)

open import section-2-2-ordinary-function-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
```

Dependent types also come with an action on identifications:  the *transport*
functions.
Given an identification `p : x = y` in the base type `A`, we can transport any
element `b : B(x)` to the fiber `B(y)`.

## Definition 5.4.1

Let `A` be a type, and let `B` be a type family over `A`.
We will construct a **transport**

```text
  tr_B : Π(x, y : A) x = y → B(x) → B(y).
```

## Construction

We construct `tr_B(p)` by induction on `p : x = y`, taking

```text
  tr_B(refl) ≔  id.
```

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x y : A}
  where

  tr : x ＝ y → B x → B y
  tr refl b = b

  inv-tr : y ＝ x → B x → B y
  inv-tr p = tr (inv p)
```

## Prelude to Definition 5.4.2

Thus we see that type theory cannot distinguish between identified elements `x`
and `y`, because for any type family `B` over `A` one obtains an element of
`B(y)` from the elements of `B(x)`.

As an application of the transport function we construct the *dependent* action
on paths of a dependent function `f : Π(x : A) B(x)`.
Note that for such a dependent function `f`, and an identification `p : x = y`,
it does not make sense to directly compare `f(x)` and `f(y)`, since the type of
`f(x)` is `B(x)` whereas the type of `f(y)` is `B(y)`, which might not be
exactly the same type.
However, we can first *transport* `f(x)` along `p`, so that we obtain the
element `tr_B(p, f(x))` which is of type `B(y)`.
Now we can ask whether it is the case that `tr_B(p, f(x)) = f(y)`.

```agda
dependent-identification :
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → Type l2
dependent-identification B p u v = (tr B p u ＝ v)

refl-dependent-identification :
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x : A} {y : B x} →
  dependent-identification B refl y y
refl-dependent-identification B = refl

dependent-identification' :
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → Type l2
dependent-identification' B p u v = (u ＝ inv-tr B p v)

refl-dependent-identification' :
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x : A} {y : B x} →
  dependent-identification' B refl y y
refl-dependent-identification' B = refl
```

The dependent action on paths of `f` establishes this identification.

## Definition 5.4.2

Given a dependent function `f : Π(a : A) B(a)` and an identification
`p : x = y` in `A`, we construct an identification

```text
  apd_f(p) : tr_B(p, f(x)) = f(y).
```

## Construction

The identification `apd_f(p)` is constructed by the induction principle for
identity types.
Thus, it suffices to construct an identification

```text
  apd_f(refl) : tr_B(refl, f(x)) = f(x).
```

Since transporting along `refl` is the identity function on `B(x)`, we simply
take `apd_f(refl) ≔ refl`.

```agda
apd :
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → dependent-identification B p (f x) (f y)
apd f refl = refl
```

## Supplements

We will occasionally need to know how to trasport along an identification of the form ap_f(p).
Such a computation is most naturally defined here.

```agda
tr-ap :
  {l1 l2 l3 l4 : Level} {A : Type l1} {B : A → Type l2} {C : Type l3} {D : C → Type l4}
  (f : A → C) (g : (x : A) → B x → D (f x))
  {x y : A} (p : x ＝ y) (z : B x) →
  tr D (ap f p) (g x z) ＝ g y (tr B p z)
tr-ap f g refl z = refl
```

## Supplement

### Transposing transport along the inverse of an identification

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  eq-transpose-tr :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    v ＝ tr B p u → tr B (inv p) v ＝ u
  eq-transpose-tr refl q = q

  eq-transpose-tr' :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    tr B p u ＝ v → u ＝ tr B (inv p) v
  eq-transpose-tr' refl q = q
```

### Substitution law for transport

```agda
substitution-law-tr :
  {l1 l2 l3 : Level} {X : Type l1} {A : Type l2} (B : A → Type l3) (f : X → A)
  {x y : X} (p : x ＝ y) {x' : B (f x)} →
  tr B (ap f p) x' ＝ tr (B ∘ f) p x'
substitution-law-tr B f p {x'} = tr-ap f (λ _ → id) p x'
```


## Agda-unimath sources

- The transport operation for non-dependent functions is defined in `foundation-core.transport-along-identifications`
- The dependent action on paths of a dependent function is defined in `foundation.action-on-identifications-dependent-functions`
