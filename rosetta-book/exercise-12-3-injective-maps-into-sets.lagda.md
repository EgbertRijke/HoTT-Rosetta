# Exercise 12.3

```agda
module exercise-12-3-injective-maps-into-sets where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-6-3-order-natural-numbers
open import section-12-1-propositions
```

## Problem statement

Show that any injective map `f:A→ B` into a set `B` is an embedding, and conclude that `A` is automatically a set in this case.

Show that `n↦ m+n` is an embedding, for each `m:ℕ`.
Moreover, conclude that there is an equivalence
```text
(m≤ n)≃ Σ(k:ℕ) m+k=n.
```

Show that `n↦ mn` is an embedding, for each nonzero number `m:ℕ`.
Conclude that the divisibility relation
```text
d| n
```
is a proposition for each `d,n:ℕ` such that `d>0`.

## Solution

No formalization has been curated yet.

```agda
abstract
  is-prop-leq-ℕ :
    (m n : ℕ) → is-prop (leq-ℕ m n)
  is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
  is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
  is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n
```
