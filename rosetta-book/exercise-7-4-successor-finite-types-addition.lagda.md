# Exercise 7.4

```agda
module exercise-7-4-successor-finite-types-addition where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-1-injectivity-addition-multiplication
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
```

## Problem statement

Define `1≔[1]_{k+1}:Fin{k+1}`.
Show that
```text
succ-Fin_{k+1}(x)=x+1
```
for any `x:Fin{k+1}`.

## Solution

```agda
one-Fin : (k : ℕ) → Fin (succ-ℕ k)
one-Fin k = succ-Fin (succ-ℕ k) (zero-Fin k)
```

```agda
is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k)))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k
```

```agda
is-add-one-succ-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) x (one-Fin k)
is-add-one-succ-Fin' zero-ℕ (inr _) = refl
is-add-one-succ-Fin' (succ-ℕ k) x =
  ( ap (succ-Fin (succ-ℕ (succ-ℕ k))) (inv (is-section-nat-Fin (succ-ℕ k) x))) ∙
  ( ap
    ( mod-succ-ℕ (succ-ℕ k))
    ( ap
      ( (nat-Fin (succ-ℕ (succ-ℕ k)) x) +ℕ_)
      ( inv (is-one-nat-one-Fin (succ-ℕ k)))))
```
