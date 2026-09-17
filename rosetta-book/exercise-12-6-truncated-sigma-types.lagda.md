# Exercise 12.6

```agda
module exercise-12-6-truncated-sigma-types where

open import universe-levels
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
open import section-4-6-dependent-pair-types
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-3-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
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

We formalized the forward direction in the previous part. However, the statement that if `f : A → B` is a `k`-truncated map into a `k`-truncated type `B` is not formalized as such. It is a consequence of thigs that are in the library, so we leave this open for the benchmark.
