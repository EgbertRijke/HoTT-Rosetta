# Exercise 12.6

```agda
module exercise-12-6-truncated-sigma-types where

open import universe-levels
open import section-5-4-transport
open import section-4-6-dependent-pair-types
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
```

## Problem statement

<div class="subexenum">

Consider a type family `B` over a `k`-truncated type `A`.
Show that the following are equivalent:

1.  The type `B(x)` is `k`-truncated for each `x:A`.

2.  The type `Σ(x:A) B(x)` is `k`-truncated.

Hint: for the base case, use Exercises 10.6 and 10.3.

Consider a map `f:A→ B` into a `k`-type `B`.
Show that the following are equivalent:

1.  The type `A` is `k`-truncated.

2.  The map `f` is `k`-truncated.

</div>

## Solution

<!-- rosetta-item: exercise-12-6 -->

### Part (a): proposition-level forward implication needed by Section 14.1

<!-- rosetta-agda-block: exercise-12-6-propositional-sigma -->

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
```


```agda
abstract
  is-prop-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-product H K = is-prop-Σ H (λ x → K)
```
