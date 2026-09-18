# Section 14.1 The universal property of propositional truncations

```agda
module section-14-1-the-universal-property-of-propositional-truncations where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-12-1-propositions
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
open import exercise-4-3-double-negation-logic
open import exercise-10-1-identity-types-contractible
open import exercise-12-6-truncated-sigma-types
open import exercise-12-7-truncated-products
```

The propositional truncation of a type `A` is a proposition `‖A‖` equipped with a map

```text
  η : A → ‖A‖.
```

This map ensures that if we have an element `a : A`, then the proposition `‖A‖` that `A` is inhabited holds.
The complete specification of the propositional truncation includes the universal property of the map `η`.
In this section we will specify in full generality when a map `f : A → P` into a proposition `P` is a propositional truncation.

## Definition 14.1.1

Let `A` be a type, and let `f : A → P` be a map into a proposition `P`.
We say that `f` **is a propositional truncation** of `A` if for every proposition `Q`, the precomposition map

```text
  - ∘ f : (P → Q) → (A → Q)
```

is an equivalence.
This property of `f` is called the **universal property of the propositional truncation of `A`**.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
  where

  precomp-Prop :
    {l3 : Level} (Q : Prop l3) →
    type-hom-Prop P Q → A → type-Prop Q
  precomp-Prop Q g = g ∘ f

  is-propositional-truncation : UUω
  is-propositional-truncation =
    {l : Level} (Q : Prop l) → is-equiv (precomp-Prop Q)
```

Note: The agda-unimath definition of the universal property of propositional truncation is the one in the following remark.

## Remark 14.1.2

Using the fact that equivalences are maps that have contractible fibers, we can reformulate the universal property of the propositional truncation.
Note that the fiber of the precomposition map `- ∘ f : (P → Q) → (A → Q)` at a map `g : A → Q` is the type.

```text
  Σ(h : P → Q) h ∘ f = g
```

Therefore we see that if `f` satisfies the universal property of the propositional truncation, then these fibers are contractible.
In other words, for each map `g : A → Q` into a proposition `Q` there is a unique map `h : P → Q` for which `h ∘ f = g`.
We also say that every map `g : A → Q` into a proposition `Q` *extends* uniquely along `f`, as indicated in the diagram

```text
    A
    | \
  f |  \ g
    |   \
    ∨    ∨
    P ⋯⋯> Q
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  universal-property-propositional-truncation : UUω
  universal-property-propositional-truncation =
    {l : Level} (Q : Prop l) (g : A → type-Prop Q) →
    is-contr (Σ ((type-Prop P → type-Prop Q)) (λ h → h ∘ f ＝ g))

  abstract
    universal-property-is-propositional-truncation :
      is-propositional-truncation P f →
      universal-property-propositional-truncation
    universal-property-is-propositional-truncation H Q =
      is-contr-map-is-equiv (H Q)

  abstract
    is-propositional-truncation-universal-property :
      universal-property-propositional-truncation →
      is-propositional-truncation P f
    is-propositional-truncation-universal-property H Q =
      is-equiv-is-contr-map (H Q)

  abstract
    map-is-propositional-truncation :
      {l3 : Level} → is-propositional-truncation P f →
      (Q : Prop l3) (g : A → type-Prop Q) → (type-Prop P → type-Prop Q)
    map-is-propositional-truncation is-ptr-f Q g =
      pr1
        ( center
          ( universal-property-is-propositional-truncation is-ptr-f Q g))

    eq-is-propositional-truncation :
      {l3 : Level} (is-ptr-f : is-propositional-truncation P f) →
      (Q : Prop l3) (g : A → type-Prop Q) →
      map-is-propositional-truncation is-ptr-f Q g ∘ f ＝ g
    eq-is-propositional-truncation is-ptr-f Q g =
      pr2
        ( center
          ( universal-property-is-propositional-truncation is-ptr-f Q g))
```

## Remark 14.1.3

For any two propositions `P` and `P'`, a map `f : P → P'` is an equivalence if and only if there is a function `g : P' → P`.
To see this, simply note that any such function `g` is an inverse of `f`, because any two elements in `P` and any two elements in `P'` are equal.

Note that the type `X → Q` is a proposition, for any type `X` and any proposition `Q`.
Using the previous observation, it therefore follows that the map `(P → Q) → (A → Q)` is an equivalence as soon as there is a map in the converse direction.
In other words, to prove that a map `f : A → P` into a proposition `P` satisfies the universal property of the propositional truncation of `A`, it suffices to construct a function

```text
  (A → Q) → (P → Q)
```

for every proposition `Q`.

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  extension-property-propositional-truncation : UUω
  extension-property-propositional-truncation =
    {l : Level} (Q : Prop l) → (A → type-Prop Q) → (type-Prop P → type-Prop Q)

  abstract
    is-propositional-truncation-extension-property :
      extension-property-propositional-truncation →
      is-propositional-truncation P f
    is-propositional-truncation-extension-property up-P Q =
      is-equiv-has-converse-is-prop
        ( is-prop-Π (λ x → is-prop-type-Prop Q))
        ( is-prop-Π (λ x → is-prop-type-Prop Q))
        ( up-P Q)
```

In the following proposition we show that the propositional truncation of a type `A` is uniquely determined up to equivalence, if it exists.
In other words, any two propositional truncations of a type `A` must be equivalent.

## Proposition 14.1.4

Let `A` be a type, and consider two maps

```text
  f : A → P    and    f' : A → P'
```

into two propositions `P` and `P'`.
If any two of the following three assertions hold, so does the third:

1. The map `f` is a propositional truncation of `A`.

2. The map `f'` is a propositional truncation of `A`.

3. There is a (unique) equivalence `P ≃ P'`.

### Proof

We first show that (i) and (ii) together imply (iii).
If `f` and `f'` are both propositional truncations of `A`, then we have maps `P → P'` and `P' → P` by the universal properties of `f` and `f'`.
Since `P` and `P'` are both propositions, it follows that `P ≃ P'`.
For the uniqueness claim, note that the type `P ≃ P'` is itself a proposition.

Finally we show that (iii) implies that (i) holds if and only if (ii) holds.
Suppose we have an equivalence `P ≃ P'`, let `Q` be an arbitrary proposition, and consider the triangle

```text
             (A → Q)
            /       \
           /         \
          /           \
         ∨             ∨
  (P → Q) <-----------> (P' → Q)
```

where the fact that `(P → Q) ↔ (P' → Q)` holds follows from the assumption that `P` is equivalent to `P'`.
We see from this triangle that

```text
  ((A → Q) → (P → Q)) ↔ ((A → Q) → (P' → Q)),
```
and this implies that (i) holds if and only if (ii) holds. ◻

```agda
equiv-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3) →
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  is-propositional-truncation P f → is-propositional-truncation P' f' →
  type-Prop P ≃ type-Prop P'
equiv-is-propositional-truncation P P' f f' H K =
  equiv-iff-is-prop
    ( is-prop-type-Prop P)
    ( is-prop-type-Prop P')
    ( map-is-propositional-truncation P f H P' f')
    ( map-is-propositional-truncation P' f' K P f)

abstract
  is-ptruncation-is-ptruncation-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : (type-Prop P → type-Prop P')) →
    is-equiv h → is-propositional-truncation P f →
    is-propositional-truncation P' f'
  is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
    is-propositional-truncation-extension-property P' f'
      ( λ R g →
        ( map-is-propositional-truncation P f is-ptr-f R g) ∘
        ( map-section-is-equiv is-equiv-h))

abstract
  is-ptruncation-is-equiv-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : (type-Prop P → type-Prop P')) →
    is-propositional-truncation P' f' → is-equiv h →
    is-propositional-truncation P f
  is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
    is-propositional-truncation-extension-property P f
      ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)
```

## Remark 14.1.5

One might be tempted to think that a type is inhabited if and only if it is nonempty.
Recall that a type `A` is nonempty if it satisfies the property `¬¬ A`.
Indeed, the type `¬¬ A` is a proposition, and it comes equipped with a map `A → ¬¬ A`.
It is therefore natural to wonder whether the map `A → ¬¬ A` satisfies the universal property of the propositional truncation.

Recall that we have shown in Exercise 4.3 that any map `A → ¬¬ Q` extends to a map `¬¬ A → ¬¬ Q`, as indicated in the diagram

```text
      A
     |  \
     |   \
     |    \
     ∨     ∨
  ¬¬ A ⋯⋯⋯> ¬¬ Q
```

It follows that the natural map

```text
  (¬¬ A → ¬¬ Q) → (A → ¬¬ Q)
```

given by precomposition by `A → ¬¬ A` is an equivalence.
However, this only gives us a universal property with respect to doubly negated propositions and there is no way to prove the more general universal property of the propositional truncation for the map `A → ¬¬ A`.
In fact, propositional truncations are not guaranteed to exist in Martin Löf’s dependent type theory, the way it is set up in Chapter I.
We will therefore add new rules to the type theory to ensure their existence.

```agda
is-equiv-precomp-double-negation :
  {l1 l2 : Level} (A : UU l1) (Q : UU l2) →
  is-equiv (precomp (double-negation-introduction {P = A}) (¬¬ Q))
is-equiv-precomp-double-negation A Q =
  is-equiv-has-converse-is-prop
    ( is-prop-function-type is-prop-double-negation)
    ( is-prop-function-type is-prop-double-negation)
    ( extend-double-negation)

equiv-precomp-double-negation :
  {l1 l2 : Level} (A : UU l1) (Q : UU l2) →
  ((¬¬ A) → (¬¬ Q)) ≃ (A → (¬¬ Q))
pr1 (equiv-precomp-double-negation A Q) =
  precomp (double-negation-introduction {P = A}) (¬¬ Q)
pr2 (equiv-precomp-double-negation A Q) =
  is-equiv-precomp-double-negation A Q
```

## Supplement

Note: In agda-unimath, propositional truncation is defined in terms of the general truncation operations. Therefore, we have to introduce the general truncation operations prior to introducing the propositional truncation operations.

### The condition on a map to be a truncation

```agda
precomp-Trunc :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : Truncated-Type l3 k) →
  (B → type-Truncated-Type C) → (A → type-Truncated-Type C)
precomp-Trunc f C = precomp f (type-Truncated-Type C)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  where

  is-truncation : UUω
  is-truncation =
    {l : Level} (C : Truncated-Type l k) → is-equiv (precomp-Trunc f C)

  equiv-is-truncation :
    {l3 : Level} (H : is-truncation) (C : Truncated-Type l3 k) →
    ( type-Truncated-Type B → type-Truncated-Type C) ≃
    ( A → type-Truncated-Type C)
  pr1 (equiv-is-truncation H C) = precomp-Trunc f C
  pr2 (equiv-is-truncation H C) = H C
```

### The truncation operations

```agda
postulate
  type-trunc : {l : Level} (k : 𝕋) → UU l → UU l

postulate
  is-trunc-type-trunc :
    {l : Level} {k : 𝕋} {A : UU l} → is-trunc k (type-trunc k A)

trunc : {l : Level} (k : 𝕋) → UU l → Truncated-Type l k
pr1 (trunc k A) = type-trunc k A
pr2 (trunc k A) = is-trunc-type-trunc

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-truncation (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  (type-trunc k A → type-Truncated-Type B) ≃ (A → type-Truncated-Type B)
pr1 (equiv-universal-property-trunc A B) = precomp-Trunc unit-trunc B
pr2 (equiv-universal-property-trunc A B) = is-truncation-trunc B
```

### The dependent universal property of truncations

```agda
precomp-Π-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : B → Truncated-Type l3 k) →
  ((b : B) → type-Truncated-Type (C b)) →
  ((a : A) → type-Truncated-Type (C (f a)))
precomp-Π-Truncated-Type f C h a = h (f a)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B)
  where

  dependent-universal-property-truncation : UUω
  dependent-universal-property-truncation =
    {l : Level} (X : type-Truncated-Type B → Truncated-Type l k) →
    is-equiv (precomp-Π-Truncated-Type f X)
```

### A map into a truncated type is a truncation if and only if it satisfies the dependent universal property of the truncation

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  where

  abstract
    dependent-universal-property-truncation-is-truncation :
      is-truncation B f →
      dependent-universal-property-truncation B f
    dependent-universal-property-truncation-is-truncation H X =
      is-fiberwise-equiv-is-equiv-map-Σ
        ( λ (h : A → type-Truncated-Type B) →
          (a : A) → type-Truncated-Type (X (h a)))
        ( λ (g : type-Truncated-Type B → type-Truncated-Type B) → g ∘ f)
        ( λ g (s : (b : type-Truncated-Type B) →
          type-Truncated-Type (X (g b))) (a : A) → s (f a))
        ( H B)
        ( is-equiv-equiv
          ( inv-distributive-Π-Σ)
          ( inv-distributive-Π-Σ)
          ( ind-Σ (λ g s → refl))
          ( H (Σ-Truncated-Type B X)))
        ( id)

  abstract
    is-truncation-dependent-universal-property-truncation :
      dependent-universal-property-truncation B f → is-truncation B f
    is-truncation-dependent-universal-property-truncation H X = H (λ _ → X)

  section-is-truncation :
    is-truncation B f →
    {l3 : Level} (C : Truncated-Type l3 k)
    (h : A → type-Truncated-Type C) (g : type-hom-Truncated-Type k C B) →
    f ~ g ∘ h → section g
  section-is-truncation H C h g K =
    map-distributive-Π-Σ
      ( map-inv-is-equiv
        ( dependent-universal-property-truncation-is-truncation H
          ( fiber-Truncated-Type C B g))
        ( λ a → (h a , inv (K a))))
```

### The `n`-truncations satisfy the dependent universal property of `n`-truncations

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  dependent-universal-property-trunc :
    dependent-universal-property-truncation (trunc k A) unit-trunc
  dependent-universal-property-trunc =
    dependent-universal-property-truncation-is-truncation
      ( trunc k A)
      ( unit-trunc)
      ( is-truncation-trunc)

  equiv-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : type-trunc k A) → type-Truncated-Type (B x)) ≃
    ((a : A) → type-Truncated-Type (B (unit-trunc a)))
  pr1 (equiv-dependent-universal-property-trunc B) =
    precomp-Π-Truncated-Type unit-trunc B
  pr2 (equiv-dependent-universal-property-trunc B) =
    dependent-universal-property-trunc B

  unique-dependent-function-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k)
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    is-contr
      ( Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
          ( λ h → (h ∘ unit-trunc) ~ f))
  unique-dependent-function-trunc B f =
    is-contr-equiv'
      ( fiber (precomp-Π-Truncated-Type unit-trunc B) f)
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (dependent-universal-property-trunc B) f)

  apply-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
      ( λ h → (h ∘ unit-trunc) ~ f)
  apply-dependent-universal-property-trunc B f =
    center (unique-dependent-function-trunc B f)

  function-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    (x : type-trunc k A) → type-Truncated-Type (B x)
  function-dependent-universal-property-trunc B f =
    pr1 (apply-dependent-universal-property-trunc B f)

  htpy-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    ( function-dependent-universal-property-trunc B f ∘ unit-trunc) ~ f
  htpy-dependent-universal-property-trunc B f =
    pr2 (apply-dependent-universal-property-trunc B f)
```
