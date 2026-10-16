# Exercise 12.3

```agda
module exercise-12-3-injective-maps-into-sets where

open import universe-levels
open import section-5-1-the-inductive-definition-of-identity-types
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
```

## Problem statement

### Exercise 12.3(a)

Show that any injective map `f : A → B` into a set `B` is an embedding, and conclude that `A` is automatically a set in this case.

### Exercise 12.3(b)

Show that `n ↦ m + n` is an embedding, for each `m : ℕ`.
Moreover, conclude that there is an equivalence

```text
  (m ≤ n) ≃ Σ(k : ℕ) m + k = n.
```

### Exercise 12.3(c)

Show that `n ↦ mn` is an embedding, for each nonzero number `m : ℕ`.
Conclude that the divisibility relation

```text
  d | n
```

is a proposition for each `d, n : ℕ` such that `d > 0`.

## Solutions

### Exercise 12.3(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-set-is-injective :
      {f : A → B} → is-set B → is-injective f → is-set A
    is-set-is-injective {f} H I =
      is-set-prop-in-id
        ( λ x y → f x ＝ f y)
        ( λ x y → H (f x) (f y))
        ( λ x → refl)
        ( λ x y → I)
```

### Exercise 12.3(b)

BENCHMARK PROBLEM

### Exercise 12.3(c)

BENCHMARK PROBLEM

## Supplement

### Any injective map between sets is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-is-injective' :
      (is-set-A : is-set A) (is-set-B : is-set B) (f : A → B) →
      is-injective f → is-emb f
    is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
      is-equiv-has-converse-is-prop
        ( is-set-A x y)
        ( is-set-B (f x) (f y))
        ( is-injective-f)

    is-emb-is-injective :
      {f : A → B} → is-set B → is-injective f → is-emb f
    is-emb-is-injective {f} H I =
      is-emb-is-injective' (is-set-is-injective H I) H f I

    is-prop-map-is-injective :
      {f : A → B} → is-set B → is-injective f → is-prop-map f
    is-prop-map-is-injective {f} H I =
      is-prop-map-is-emb (is-emb-is-injective H I)

emb-injection :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  injection A (type-Set B) → A ↪ (type-Set B)
emb-injection B = tot (λ f → is-emb-is-injective (is-set-type-Set B))
```
