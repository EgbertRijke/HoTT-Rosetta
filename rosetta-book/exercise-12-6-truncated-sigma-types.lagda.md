# Exercise 12.6

```agda
module exercise-12-6-truncated-sigma-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
open import section-4-6-dependent-pair-types
open import section-9-1-homotopies
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-3-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
```

## Problem statement

### Exercise 12.6(a)

Consider a type family `B` over a `k`-truncated type `A`.
Show that the following are equivalent:

1. The type `B(x)` is `k`-truncated for each `x : A`.

2. The type `Σ(x : A) B(x)` is `k`-truncated.

Hint: For the base case, use Exercises 10.6 and 10.3.

### Exercise 12.6(b)

Consider a map `f : A → B` into a `k`-type `B`.
Show that the following are equivalent:

1. The type `A` is `k`-truncated.

2. The map `f` is `k`-truncated.

## Solution

### Exercise 12.6(a)

```agda
abstract
  is-prop-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ H K x y =
    is-contr-equiv'
      ( Eq-Σ x y)
      ( equiv-eq-pair-Σ x y)
      ( is-contr-Σ'
        ( H (pr1 x) (pr1 y))
        ( λ p → K (pr1 y) (tr _ p (pr2 x)) (pr2 y)))

Σ-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2) → Prop (l1 ⊔ l2)
pr1 (Σ-Prop P Q) = Σ (type-Prop P) (λ p → type-Prop (Q p))
pr2 (Σ-Prop P Q) =
  is-prop-Σ
    ( is-prop-type-Prop P)
    ( λ p → is-prop-type-Prop (Q p))

abstract
  is-trunc-Σ :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ {k = neg-two-𝕋} is-trunc-A is-trunc-B =
    is-contr-Σ' is-trunc-A is-trunc-B
  is-trunc-Σ {k = succ-𝕋 k} {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-equiv k
      ( Σ (pr1 s ＝ pr1 t) (λ p → tr B p (pr2 s) ＝ pr2 t))
      ( equiv-pair-eq-Σ s t)
      ( is-trunc-Σ
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

Σ-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : type-Truncated-Type A → Truncated-Type l2 k) →
  Truncated-Type (l1 ⊔ l2) k
pr1 (Σ-Truncated-Type A B) =
  Σ (type-Truncated-Type A) (λ a → type-Truncated-Type (B a))
pr2 (Σ-Truncated-Type A B) =
  is-trunc-Σ
    ( is-trunc-type-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fiber-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : Truncated-Type l1 k)
  (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → Truncated-Type (l1 ⊔ l2) k
fiber-Truncated-Type A B f b =
  Σ-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)

abstract
  is-trunc-map-is-trunc-domain-codomain :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-Id is-trunc-B (f x) b)

abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-equiv' k
      ( fiber pr1 x)
      ( equiv-fiber-pr1 B x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)
```

### Exercise 12.6(b)

BENCHMARK PROBLEM

We formalized the forward direction in the previous part. However, the statement that if `f : A → B` is a `k`-truncated map into a `k`-truncated type `B` is not formalized as such.

## Supplement

### Truncated maps are closed under composition

```agda
abstract
  is-trunc-map-comp :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k (g ∘ h)
  is-trunc-map-comp k g h is-trunc-g is-trunc-h x =
    is-trunc-is-equiv k
        ( Σ (fiber g x) (λ t → fiber h (pr1 t)))
        ( map-compute-fiber-comp g h x)
        ( is-equiv-map-compute-fiber-comp g h x)
        ( is-trunc-Σ
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t)))

comp-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {X : UU l3} (g : trunc-map k B X) (h : trunc-map k A B) →
  trunc-map k A X
pr1 (comp-trunc-map k g h) = pr1 g ∘ pr1 h
pr2 (comp-trunc-map k g h) =
  is-trunc-map-comp k (pr1 g) (pr1 h) (pr2 g) (pr2 h)
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are truncated maps, then `f` is a truncated map

```agda
abstract
  is-trunc-map-left-map-triangle :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-left-map-triangle k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k H
      ( is-trunc-map-comp k g h is-trunc-g is-trunc-h)
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot H y =
      is-trunc-equiv k
        ( fiber (f (pr1 y)) (pr2 y))
        ( compute-fiber-tot f y)
        ( H (pr1 y) (pr2 y))

  abstract
    is-trunc-map-is-trunc-map-tot :
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot is-trunc-tot-f x z =
      is-trunc-equiv k
        ( fiber (tot f) (x , z))
        ( inv-compute-fiber-tot f (x , z))
        ( is-trunc-tot-f (x , z))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot =
      is-trunc-map-tot neg-two-𝕋

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = is-trunc-map-tot neg-one-𝕋
```

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-map-map-Σ-map-base :
      (k : 𝕋) {f : A → B} (C : B → UU l3) →
      is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
    is-trunc-map-map-Σ-map-base k {f} C H y =
      is-trunc-equiv' k
        ( fiber f (pr1 y))
        ( compute-fiber-map-Σ-map-base f C y)
        ( H (pr1 y))

  abstract
    is-prop-map-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) →
      is-prop-map f → is-prop-map (map-Σ-map-base f C)
    is-prop-map-map-Σ-map-base C = is-trunc-map-map-Σ-map-base neg-one-𝕋 C

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  abstract
    is-trunc-map-map-Σ :
      (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
      is-trunc-map k (map-Σ D f g)
    is-trunc-map-map-Σ k D {f} {g} H K =
      is-trunc-map-left-map-triangle k
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-trunc-map-map-Σ-map-base k D H)
        ( is-trunc-map-tot k K)

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    abstract
      is-contr-map-map-Σ :
        is-contr-map f → ((x : A) → is-contr-map (g x)) →
        is-contr-map (map-Σ D f g)
      is-contr-map-map-Σ = is-trunc-map-map-Σ neg-two-𝕋 D

    abstract
      is-prop-map-map-Σ :
        is-prop-map f → ((x : A) → is-prop-map (g x)) →
        is-prop-map (map-Σ D f g)
      is-prop-map-map-Σ = is-trunc-map-map-Σ neg-one-𝕋 D
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) → is-emb f → is-emb (map-Σ-map-base f C)
    is-emb-map-Σ-map-base C H =
      is-emb-is-prop-map (is-prop-map-map-Σ-map-base C (is-prop-map-is-emb H))

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = map-Σ-map-base (map-emb f) C
  pr2 (emb-Σ-emb-base f C) =
    is-emb-map-Σ-map-base C (is-emb-map-emb f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-emb-map-Σ :
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
  is-emb-map-Σ D H K =
    is-emb-is-prop-map
      ( is-prop-map-map-Σ D
        ( is-prop-map-is-emb H)
        ( λ x → is-prop-map-is-emb (K x)))

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = map-Σ D (map-emb f) (λ x → map-emb (g x))
  pr2 (emb-Σ D f g) =
    is-emb-map-Σ D (is-emb-map-emb f) (λ x → is-emb-map-emb (g x))
```
