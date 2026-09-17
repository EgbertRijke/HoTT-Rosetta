# Exercise 8.2

```agda
module exercise-8-2-decidability-of-decidability where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-8-1-decidability-and-decidable-equality
```

## Problem statement

Show that
```text
is-decidable(is-decidable(P))→is-decidable(P)
```
for any type `P`.

## Solution

```agda
module _
  {l : Level} {P : UU l}
  where

  map-idempotent-is-decidable : is-decidable P → is-decidable (is-decidable P)
  map-idempotent-is-decidable = inl

  map-inv-idempotent-is-decidable :
    is-decidable (is-decidable P) → is-decidable P
  map-inv-idempotent-is-decidable (inl (inl p)) = inl p
  map-inv-idempotent-is-decidable (inl (inr np)) = inr np
  map-inv-idempotent-is-decidable (inr np) = inr (λ p → np (inl p))
```
