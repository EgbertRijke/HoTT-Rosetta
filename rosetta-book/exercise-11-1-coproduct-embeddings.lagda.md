# Exercise 11.1

```agda
module exercise-11-1-coproduct-embeddings where

open import universe-levels
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-10-1-contractible-types
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-11-5-disjointness-of-coproducts
```

## Problem statement

### Exercise 11.1(a)

Show that the map `empty → A` is an embedding for every type `A`.

### Exercise 11.1(b)

Show that `inl : A → A + B` and `inr : B → A + B` are embeddings for any two types `A` and `B`.

### Exercise 11.1(c)

Show that `inl : A → A + B` is an equivalence if and only if `B` is empty, and that `inr : B → A + B` is an equivalence if and only if `A` is empty.

## Solutions

### Exercise 11.1(a)

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-emb-ex-falso : is-emb (ex-falso {A = A})
    is-emb-ex-falso ()

  ex-falso-emb : empty ↪ A
  pr1 ex-falso-emb = ex-falso
  pr2 ex-falso-emb = is-emb-ex-falso
```

### Exercise 11.1(b)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coproduct-inl-inl x))
          ( is-torsorial-Id x))
        ( λ y → ap inl)

  emb-inl : A ↪ (A + B)
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coproduct-inr-inr x))
          ( is-torsorial-Id x))
        ( λ y → ap inr)

  emb-inr : B ↪ (A + B)
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr
```

### Exercise 11.1(c)

PARTIAL BENCHMARK PROBLEM

Section 9.2 proves that `inl` is an equivalence when `B` is empty, and that `inr` is an equivalence when `A` is empty.
The converse implications remain to be formalized.

```agda
open import section-9-2-bi-invertible-maps
  using (is-equiv-inl-is-empty; is-equiv-inr-is-empty)
```
