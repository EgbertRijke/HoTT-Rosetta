# Exercise 6.1 Injectivity of addition and multiplication

```agda
module exercise-6-1-injectivity-addition-multiplication where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
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
open import section-6-4-peanos-seventh-and-eighth-axioms
```

```agda
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = (n ＝ zero-ℕ)

is-zero-ℕ' : ℕ → UU lzero
is-zero-ℕ' n = (zero-ℕ ＝ n)

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → n ＝ succ-ℕ y)

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = (n ＝ 1)

is-one-ℕ' : ℕ → UU lzero
is-one-ℕ' n = (1 ＝ n)

is-not-one-ℕ : ℕ → UU lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → UU lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ (x , refl) ()

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
pr1 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = x
pr2 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = refl
```

## Problem statement

Show that

```text
  (m = n) ↔ (m + k = n + k)
  (m = n) ↔ (m · (k + 1) = n · (k + 1))
```

for all `m, n, k : ℕ`.
In other words, adding `k` and multiplying by `k + 1` are injective functions.

## Solution

```agda
abstract
  is-injective-right-add-ℕ :
    (k : ℕ) {x y : ℕ} → x +ℕ k ＝ y +ℕ k → x ＝ y
  is-injective-right-add-ℕ zero-ℕ p = p
  is-injective-right-add-ℕ (succ-ℕ k) p =
    is-injective-right-add-ℕ k (is-injective-succ-ℕ p)

  is-injective-left-add-ℕ :
    (k : ℕ) {x y : ℕ} → k +ℕ x ＝ k +ℕ y → x ＝ y
  is-injective-left-add-ℕ k {x} {y} p =
    is-injective-right-add-ℕ
      ( k)
      ( commutative-add-ℕ x k ∙ (p ∙ commutative-add-ℕ k y))
```

```agda
abstract
  is-injective-right-mul-succ-ℕ :
    (k : ℕ) {m n : ℕ} → m *ℕ (succ-ℕ k) ＝ n *ℕ (succ-ℕ k) → m ＝ n
  is-injective-right-mul-succ-ℕ k {zero-ℕ} {zero-ℕ} p = refl
  is-injective-right-mul-succ-ℕ k {succ-ℕ m} {succ-ℕ n} p =
    ap succ-ℕ
      ( is-injective-right-mul-succ-ℕ k {m} {n}
        ( is-injective-right-add-ℕ
          ( succ-ℕ k)
          ( ( inv (left-successor-law-mul-ℕ m (succ-ℕ k))) ∙
            ( ( p) ∙
              ( left-successor-law-mul-ℕ n (succ-ℕ k))))))

  is-injective-right-mul-ℕ :
    (k : ℕ) → is-nonzero-ℕ k →
    {m n : ℕ} → m *ℕ k ＝ n *ℕ k → m ＝ n
  is-injective-right-mul-ℕ k H p with
    is-successor-is-nonzero-ℕ H
  ... | pair l refl = is-injective-right-mul-succ-ℕ l p

  is-injective-left-mul-succ-ℕ :
    (k : ℕ) {m n : ℕ} → (succ-ℕ k) *ℕ m ＝ (succ-ℕ k) *ℕ n → m ＝ n
  is-injective-left-mul-succ-ℕ k {m} {n} p =
    is-injective-right-mul-succ-ℕ k
      ( ( commutative-mul-ℕ m (succ-ℕ k)) ∙
        ( p ∙ commutative-mul-ℕ (succ-ℕ k) n))

  is-injective-left-mul-ℕ :
    (k : ℕ) → is-nonzero-ℕ k →
    {m n : ℕ} → k *ℕ m ＝ k *ℕ n → m ＝ n
  is-injective-left-mul-ℕ k H p with
    is-successor-is-nonzero-ℕ H
  ... | pair l refl = is-injective-left-mul-succ-ℕ l p
```

## Problem statement

Show that

```text
  (m + n = 0) ↔ (m = 0) × (n = 0)
  (mn = 0)    ↔ (m = 0) + (n = 0)
  (mn = 1)    ↔ (m = 1) × (n = 1)
```

for all `m, n : ℕ`.

## Solution

```agda
abstract
  is-zero-right-is-zero-add-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → is-zero-ℕ y
  is-zero-right-is-zero-add-ℕ x zero-ℕ p = refl
  is-zero-right-is-zero-add-ℕ x (succ-ℕ y) p =
    ex-falso (is-nonzero-succ-ℕ (x +ℕ y) p)

  is-zero-left-is-zero-add-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → is-zero-ℕ x
  is-zero-left-is-zero-add-ℕ x y p =
    is-zero-right-is-zero-add-ℕ y x ((commutative-add-ℕ y x) ∙ p)

  is-zero-summand-is-zero-sum-ℕ :
    (x y : ℕ) → is-zero-ℕ (x +ℕ y) → (is-zero-ℕ x) × (is-zero-ℕ y)
  is-zero-summand-is-zero-sum-ℕ x y p =
    pair (is-zero-left-is-zero-add-ℕ x y p) (is-zero-right-is-zero-add-ℕ x y p)

  is-zero-sum-is-zero-summand-ℕ :
    (x y : ℕ) → (is-zero-ℕ x) × (is-zero-ℕ y) → is-zero-ℕ (x +ℕ y)
  is-zero-sum-is-zero-summand-ℕ .zero-ℕ .zero-ℕ (pair refl refl) = refl
```

```agda
abstract
  is-one-right-is-one-mul-ℕ :
    (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ y
  is-one-right-is-one-mul-ℕ zero-ℕ zero-ℕ p = p
  is-one-right-is-one-mul-ℕ zero-ℕ (succ-ℕ y) ()
  is-one-right-is-one-mul-ℕ (succ-ℕ x) zero-ℕ p =
    is-one-right-is-one-mul-ℕ x zero-ℕ p
  is-one-right-is-one-mul-ℕ (succ-ℕ x) (succ-ℕ y) p =
    ap
      ( succ-ℕ)
      ( is-zero-right-is-zero-add-ℕ (x *ℕ (succ-ℕ y)) y
        ( is-injective-succ-ℕ p))

  is-one-left-is-one-mul-ℕ :
    (x y : ℕ) → is-one-ℕ (x *ℕ y) → is-one-ℕ x
  is-one-left-is-one-mul-ℕ x y p =
    is-one-right-is-one-mul-ℕ y x (commutative-mul-ℕ y x ∙ p)

  is-one-mul-ℕ :
    (x y : ℕ) → is-one-ℕ x → is-one-ℕ y → is-one-ℕ (x *ℕ y)
  is-one-mul-ℕ .1 .1 refl refl = refl
```

```agda
abstract
  is-zero-summand-is-zero-mul-ℕ :
    (x y : ℕ) → is-zero-ℕ (x *ℕ y) → is-zero-ℕ x + is-zero-ℕ y
  is-zero-summand-is-zero-mul-ℕ 0 y H = inl refl
  is-zero-summand-is-zero-mul-ℕ (succ-ℕ x) 0 H = inr refl

  is-zero-mul-ℕ-is-zero-left-summand :
    (x y : ℕ) → is-zero-ℕ x → is-zero-ℕ (x *ℕ y)
  is-zero-mul-ℕ-is-zero-left-summand .0 y refl = left-zero-law-mul-ℕ y

  is-zero-mul-ℕ-is-zero-right-summand :
    (x y : ℕ) → is-zero-ℕ y → is-zero-ℕ (x *ℕ y)
  is-zero-mul-ℕ-is-zero-right-summand x .0 refl = right-zero-law-mul-ℕ x

  is-zero-mul-ℕ-is-zero-summand :
    (x y : ℕ) → is-zero-ℕ x + is-zero-ℕ y → is-zero-ℕ (x *ℕ y)
  is-zero-mul-ℕ-is-zero-summand x y (inl H) =
    is-zero-mul-ℕ-is-zero-left-summand x y H
  is-zero-mul-ℕ-is-zero-summand x y (inr H) =
    is-zero-mul-ℕ-is-zero-right-summand x y H
```

## Problem statement

Show that

```text
  m     ≠ m + (n + 1)
  m + 1 ≠ (m + 1)(n + 2)
```

for all `m, n : ℕ`.

## Solution

```agda
abstract
  neq-add-ℕ :
    (m n : ℕ) → ¬ (m ＝ m +ℕ (succ-ℕ n))
  neq-add-ℕ (succ-ℕ m) n p =
    neq-add-ℕ m n
      ( ( is-injective-succ-ℕ p) ∙
        ( left-successor-law-add-ℕ m n))

  neq-mul-ℕ :
    (m n : ℕ) → ¬ (succ-ℕ m ＝ succ-ℕ m *ℕ (succ-ℕ (succ-ℕ n)))
  neq-mul-ℕ m n p =
    neq-add-ℕ
      ( succ-ℕ m)
      ( ( m *ℕ (succ-ℕ n)) +ℕ n)
      ( ( p) ∙
        ( ( right-successor-law-mul-ℕ (succ-ℕ m) (succ-ℕ n)) ∙
          ( ap ((succ-ℕ m) +ℕ_) (left-successor-law-mul-ℕ m (succ-ℕ n)))))
```
