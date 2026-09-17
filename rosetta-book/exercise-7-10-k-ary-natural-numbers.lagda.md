# Exercise 7.10

```agda
module exercise-7-10-k-ary-natural-numbers where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import section-6-4-peanos-seventh-and-eighth-axioms
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import section-2-2-ordinary-function-types
```

## Problem statement

The type `ℕ_k` of **`k`-ary natural numbers** is an inductive type with the following constructors:

```text
constant-based-ℕ{k} : Fin{k} → based-ℕ{k}
unary-op-based-ℕ{k} : Fin{k} → (based-ℕ{k} → based-ℕ{k}).
```

A `k`-ary natural number can be converted back into an ordinary natural number via the function `convert-based-ℕ{k}:based-ℕ{k}→ℕ`, which is defined recursively by

```text
convert-based-ℕ{k}(constant-based-ℕ {k}(x)) ≔ nat-Fin(x)
convert-based-ℕ{k}(unary-op-based-ℕ{k}(x,n)) ≔ k(convert-based-ℕ{k}(n)+1)+nat-Fin(x).
```

Show that the type `based-ℕ{0}` is empty.

Show that the function `convert-based-ℕ{k}:based-ℕ{k}→ℕ` is injective.

Show that the function `convert-based-ℕ{k+1}:based-ℕ{k+1}→ℕ` has an inverse, i.e. construct a function

```text
g_{k} : ℕ→based-ℕ{k+1}
```

equipped with identifications

```text
convert-based-ℕ{k+1}(g_k(n)) = n
g_{k}(convert-based-ℕ{k+1}(x)) = x
```

for each `n:ℕ` and each `x: based-ℕ {k+1}`.

## Solution

```agda
data based-ℕ : ℕ → UU lzero where
  constant-based-ℕ : (k : ℕ) → Fin k → based-ℕ k
  unary-op-based-ℕ : (k : ℕ) → Fin k → based-ℕ k → based-ℕ k
```

```agda
constant-ℕ : (k : ℕ) → Fin k → ℕ
constant-ℕ k x = nat-Fin k x

unary-op-ℕ : (k : ℕ) → Fin k → ℕ → ℕ
unary-op-ℕ k x n = (k *ℕ (succ-ℕ n)) +ℕ (nat-Fin k x)

convert-based-ℕ : (k : ℕ) → based-ℕ k → ℕ
convert-based-ℕ k (constant-based-ℕ .k x) =
  constant-ℕ k x
convert-based-ℕ k (unary-op-based-ℕ .k x n) =
  unary-op-ℕ k x (convert-based-ℕ k n)
```

```agda
is-empty-based-zero-ℕ : is-empty (based-ℕ zero-ℕ)
is-empty-based-zero-ℕ (constant-based-ℕ .zero-ℕ ())
is-empty-based-zero-ℕ (unary-op-based-ℕ .zero-ℕ () n)
```

```agda
abstract
  leq-mul-ℕ :
    (k x : ℕ) → x ≤-ℕ (x *ℕ (succ-ℕ k))
  leq-mul-ℕ k x =
    concatenate-eq-leq-ℕ
      ( x *ℕ (succ-ℕ k))
      ( inv (right-unit-law-mul-ℕ x))
      ( preserves-leq-right-mul-ℕ x 1 (succ-ℕ k) (leq-zero-ℕ k))

  leq-mul-ℕ' :
    (k x : ℕ) → x ≤-ℕ ((succ-ℕ k) *ℕ x)
  leq-mul-ℕ' k x =
    concatenate-leq-eq-ℕ x
      ( leq-mul-ℕ k x)
      ( commutative-mul-ℕ x (succ-ℕ k))
```

```agda
cong-unary-op-ℕ :
  (k : ℕ) (x : Fin k) (n : ℕ) →
  cong-ℕ k (unary-op-ℕ k x n) (nat-Fin k x)
cong-unary-op-ℕ (succ-ℕ k) x n =
  concatenate-cong-eq-ℕ
    ( succ-ℕ k)
    { unary-op-ℕ (succ-ℕ k) x n}
    ( translation-invariant-cong-ℕ'
      ( succ-ℕ k)
      ( (succ-ℕ k) *ℕ (succ-ℕ n))
      ( zero-ℕ)
      ( nat-Fin (succ-ℕ k) x)
      ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (succ-ℕ k))))
    ( left-unit-law-add-ℕ (nat-Fin (succ-ℕ k) x))
```

```agda
le-constant-unary-op-ℕ :
  (k : ℕ) (x y : Fin k) (m : ℕ) → le-ℕ (constant-ℕ k x) (unary-op-ℕ k y m)
le-constant-unary-op-ℕ k x y m =
  concatenate-le-leq-ℕ {nat-Fin k x} {k} {unary-op-ℕ k y m}
    ( strict-upper-bound-nat-Fin k x)
    ( transitive-leq-ℕ
      ( k)
      ( k *ℕ (succ-ℕ m))
      ( unary-op-ℕ k y m)
      ( leq-add-ℕ (k *ℕ (succ-ℕ m)) (nat-Fin k y))
      ( leq-mul-ℕ m k))

is-injective-convert-based-ℕ :
  (k : ℕ) → is-injective (convert-based-ℕ k)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ap (constant-based-ℕ (succ-ℕ k)) (is-injective-nat-Fin (succ-ℕ k) p)
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { constant-based-ℕ .(succ-ℕ k) x}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) x y (convert-based-ℕ (succ-ℕ k) m))
      ( p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { constant-based-ℕ .(succ-ℕ k) y} p =
  ex-falso
    ( neq-le-ℕ
      ( le-constant-unary-op-ℕ (succ-ℕ k) y x (convert-based-ℕ (succ-ℕ k) n))
      ( inv p))
is-injective-convert-based-ℕ
  ( succ-ℕ k)
  { unary-op-based-ℕ .(succ-ℕ k) x n}
  { unary-op-based-ℕ .(succ-ℕ k) y m} p with
  is-injective-nat-Fin (succ-ℕ k) {x} {y}
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) x)
      ( nat-Fin (succ-ℕ k) y)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) x)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) y)
      ( concatenate-cong-eq-cong-ℕ
        { succ-ℕ k}
        { nat-Fin (succ-ℕ k) x}
        { unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)}
        { unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m)}
        { nat-Fin (succ-ℕ k) y}
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n))
          ( nat-Fin (succ-ℕ k) x)
          ( cong-unary-op-ℕ (succ-ℕ k) x (convert-based-ℕ (succ-ℕ k) n)))
        ( p)
        ( cong-unary-op-ℕ (succ-ℕ k) y (convert-based-ℕ (succ-ℕ k) m))))
... | refl =
  ap
    ( unary-op-based-ℕ (succ-ℕ k) x)
    ( is-injective-convert-based-ℕ (succ-ℕ k)
      ( is-injective-succ-ℕ
        ( is-injective-left-mul-succ-ℕ k
          ( is-injective-right-add-ℕ (nat-Fin (succ-ℕ k) x) p))))
```

```agda
zero-based-ℕ : (k : ℕ) → based-ℕ (succ-ℕ k)
zero-based-ℕ k = constant-based-ℕ (succ-ℕ k) (zero-Fin k)
```

```agda
succ-based-ℕ : (k : ℕ) → based-ℕ k → based-ℕ k
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  constant-based-ℕ (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x))
succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr _)) =
  unary-op-based-ℕ
    (succ-ℕ k) (zero-Fin k) (constant-based-ℕ (succ-ℕ k) (zero-Fin k))
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  unary-op-based-ℕ (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x)) n
succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr x) n) =
  unary-op-based-ℕ (succ-ℕ k) (zero-Fin k) (succ-based-ℕ (succ-ℕ k) n)
```

```agda
inv-convert-based-ℕ : (k : ℕ) → ℕ → based-ℕ (succ-ℕ k)
inv-convert-based-ℕ k zero-ℕ =
  zero-based-ℕ k
inv-convert-based-ℕ k (succ-ℕ n) =
  succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)

convert-based-succ-based-ℕ :
  (k : ℕ) (x : based-ℕ k) →
  convert-based-ℕ k (succ-based-ℕ k x) ＝ succ-ℕ (convert-based-ℕ k x)
convert-based-succ-based-ℕ (succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inl x)) =
  nat-succ-Fin k x
convert-based-succ-based-ℕ
  ( succ-ℕ k) (constant-based-ℕ .(succ-ℕ k) (inr _)) =
  ( ap
    ( λ t → ((succ-ℕ k) *ℕ (succ-ℕ t)) +ℕ t)
    ( is-zero-nat-zero-Fin {k})) ∙
  ( right-unit-law-mul-ℕ (succ-ℕ k))
convert-based-succ-based-ℕ (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inl x) n) =
  ap
    ( ((succ-ℕ k) *ℕ (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))) +ℕ_)
    ( nat-succ-Fin k x)
convert-based-succ-based-ℕ
  (succ-ℕ k) (unary-op-based-ℕ .(succ-ℕ k) (inr _) n) =
  ( ap
    ( ( ( succ-ℕ k) *ℕ
        ( succ-ℕ (convert-based-ℕ (succ-ℕ k) (succ-based-ℕ (succ-ℕ k) n))))
          +ℕ_)
    ( is-zero-nat-zero-Fin {k})) ∙
  ( ( ap
      ( ((succ-ℕ k) *ℕ_) ∘ succ-ℕ)
      ( convert-based-succ-based-ℕ (succ-ℕ k) n)) ∙
    ( ( right-successor-law-mul-ℕ
        ( succ-ℕ k)
        ( succ-ℕ (convert-based-ℕ (succ-ℕ k) n))) ∙
      ( commutative-add-ℕ
        ( succ-ℕ k)
        ( (succ-ℕ k) *ℕ (succ-ℕ (convert-based-ℕ (succ-ℕ k) n))))))

is-section-inv-convert-based-ℕ :
  (k n : ℕ) → convert-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n) ＝ n
is-section-inv-convert-based-ℕ k zero-ℕ = is-zero-nat-zero-Fin {k}
is-section-inv-convert-based-ℕ k (succ-ℕ n) =
  ( convert-based-succ-based-ℕ (succ-ℕ k) (inv-convert-based-ℕ k n)) ∙
  ( ap succ-ℕ (is-section-inv-convert-based-ℕ k n))

is-retraction-inv-convert-based-ℕ :
  (k : ℕ) (x : based-ℕ (succ-ℕ k)) →
  inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x) ＝ x
is-retraction-inv-convert-based-ℕ k x =
  is-injective-convert-based-ℕ
    ( succ-ℕ k)
    ( is-section-inv-convert-based-ℕ k (convert-based-ℕ (succ-ℕ k) x))
```
