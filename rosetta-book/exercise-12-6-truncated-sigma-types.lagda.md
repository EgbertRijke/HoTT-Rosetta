# Exercise 12.6

```agda
module exercise-12-6-truncated-sigma-types where

open import universe-levels
open import section-4-6-dependent-pair-types
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
    {l1 l2 : Level} {A : Type l1} {B : A → Type l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ H K =
    is-trunc-is-emb neg-two-𝕋 pr1 (is-emb-pr1-is-subtype K) H
```

<!-- rosetta-agda-block: exercise-12-6-propositional-product -->

```agda
abstract
  is-prop-product :
    {l1 l2 : Level} {A : Type l1} {B : Type l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-product H K = is-prop-Σ H (λ x → K)
```
