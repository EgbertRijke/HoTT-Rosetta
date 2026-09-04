# Section 5.4 Transport

```agda
module section-5-4-transport where

open import universe-levels
open import section-5-1-the-inductive-definition-of-identity-types
```

<!-- rosetta-item: section-5.4 -->

Dependent types also come with an action on identifications: the *transport* functions.
Given an identification `p:x = y` in the base type `A`, we can transport any element `b:B(x)` to the fiber `B(y)`.

## Definition 5.4.1

<!-- rosetta-item: definition-5.4.1 -->

Let `A` be a type, and let `B` be a type family over `A`.
We will construct a **transport** operation
```text
tr_B:Π(x,y:A) (x = y)→ (B(x)→ B(y)).
```

### Construction

<!-- rosetta-item: subheading-5.4-construction -->

We construct `tr_B(p)` by induction on `p:x=_A y`, taking
```text
tr_B(refl) ≔ id[B(x)].
```

<!-- rosetta-agda-block: section-5-4-transport-block-33 -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x y : A}
  where

  tr : x ＝ y → B x → B y
  tr refl b = b
```
<!-- rosetta-item-end: definition-5.4.1 -->

Thus we see that type theory cannot distinguish between identified elements `x` and `y`, because for any type family `B` over `A` one obtains an element of `B(y)` from the elements of `B(x)`.

As an application of the transport function we construct the *dependent* action on paths of a dependent function `f:Π(x:A) B(x)`.
Note that for such a dependent function `f`, and an identification `p:x =_A y`, it does not make sense to directly compare `f(x)` and `f(y)`, since the type of `f(x)` is `B(x)` whereas the type of `f(y)` is `B(y)`, which might not be exactly the same type.
However, we can first *transport* `f(x)` along `p`, so that we obtain the element `tr_B(p,f(x))` which is of type `B(y)`.
Now we can ask whether it is the case that `tr_B(p,f(x))=f(y)`.
The dependent action on paths of `f` establishes this identification.

## Definition 5.4.2

<!-- rosetta-item: definition-5.4.2; latex-label: defn:apd -->

Given a dependent function `f:Π(a:A) B(a)` and an identification `p:x = y` in `A`, we construct an identification
```text
apd_{f}(p) : tr_B(p,f(x)) = f(y).
```

### Construction

<!-- rosetta-item: subheading-5.4-construction-2 -->

The identification `apd_{f}(p)` is constructed by the induction principle for identity types.
Thus, it suffices to construct an identification
```text
apd_{f}(refl):tr_B(refl,f(x)) = f(x).
```
Since transporting along `refl` is the identity function on `B(x)`, we simply take `apd_{f}(refl)≔refl`.

<!-- rosetta-agda-block: section-5-4-transport-block-82 -->

```agda
dependent-identification :
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → Type l2
dependent-identification B p u v = (tr B p u ＝ v)

apd :
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → dependent-identification B p (f x) (f y)
apd f refl = refl
```
<!-- rosetta-item-end: definition-5.4.2 -->
