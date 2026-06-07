# Exercise 6.3 Order on the natural numbers

```agda
module exercise-6-3-order-natural-numbers where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
open import section-2-2-ordinary-function-types
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
open import path-algebra
open import exercise-6-1-injectivity-addition-multiplication
```

## Problem statement

The ordering relation `≤` on `ℕ` is defined recursively by

```text
  (0 ≤ 0)       := 𝟙      (0 ≤ n + 1)       := 𝟙
  (m + 1 ≤ 0)   := ∅      (m + 1 ≤ n + 1)   := (m ≤ n).
```

Show that `≤` satisfies the axioms of a *poset*, i.e., show that `≤` is
reflexive, antisymmetric, and transitive.

## Solution

```agda
leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

infix 30 _≤-ℕ_
_≤-ℕ_ = leq-ℕ
```

```agda
concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → x' ＝ x → x ≤-ℕ y → y ＝ y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → n ＝ n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → m' ＝ m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H
```

```agda
refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

leq-eq-ℕ : (m n : ℕ) → m ＝ n → m ≤-ℕ n
leq-eq-ℕ m .m refl = refl-leq-ℕ m
```

```agda
abstract
  transitive-leq-ℕ :
    (n m l : ℕ) → m ≤-ℕ l → n ≤-ℕ m → n ≤-ℕ l
  transitive-leq-ℕ zero-ℕ m l p q = star
  transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
    transitive-leq-ℕ n m l p q

antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → m ＝ n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)
```

## Problem statement

Show that

```text
  (m ≤ n) + (n ≤ m)
```

for any `m, n : ℕ`.

## Solution

```agda
linear-leq-ℕ :
  (m n : ℕ) → (m ≤-ℕ n) + (n ≤-ℕ m)
linear-leq-ℕ zero-ℕ zero-ℕ = inl star
linear-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
linear-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
linear-leq-ℕ (succ-ℕ m) (succ-ℕ n) = linear-leq-ℕ m n
```

```agda
cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  ( ( leq-ℕ x y × leq-ℕ y z) +
    ( leq-ℕ x z × leq-ℕ z y)) +
  ( ( ( leq-ℕ y z × leq-ℕ z x) +
      ( leq-ℕ y x × leq-ℕ x z)) +
    ( ( leq-ℕ z x × leq-ℕ x y) +
      ( leq-ℕ z y × leq-ℕ y x)))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ =
  inl (inl (star , star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) =
  inl (inl (star , star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ =
  inl (inr (star , star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coproduct (pair star) (pair star) (linear-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (star , star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coproduct (pair star) (pair star) (linear-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coproduct (pair star) (pair star) (linear-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z
```

## Problem statement

Show that

```text
  (m ≤ n) ↔ (m + k ≤ n + k)
```

holds for any `m, n, k : ℕ`.

## Solution

```agda
leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star

is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' zero-ℕ star = refl

abstract
  succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
  succ-leq-ℕ zero-ℕ = star
  succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n

  preserves-leq-succ-ℕ :
    (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
  preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) (succ-leq-ℕ n) p
```

```agda
abstract
  contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
  contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

  contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
  contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K
```

```agda
abstract
  preserves-leq-left-add-ℕ :
    (k m n : ℕ) → m ≤-ℕ n → (m +ℕ k) ≤-ℕ (n +ℕ k)
  preserves-leq-left-add-ℕ zero-ℕ m n = id
  preserves-leq-left-add-ℕ (succ-ℕ k) m n H = preserves-leq-left-add-ℕ k m n H

  preserves-leq-right-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (k +ℕ m) ≤-ℕ (k +ℕ n)
  preserves-leq-right-add-ℕ k m n H =
    concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ k m)
      ( preserves-leq-left-add-ℕ k m n H)
      ( commutative-add-ℕ n k)

  preserves-leq-add-ℕ :
    {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → (m +ℕ n) ≤-ℕ (m' +ℕ n')
  preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
    transitive-leq-ℕ
      ( m +ℕ n)
      ( m' +ℕ n)
      ( m' +ℕ n')
      ( preserves-leq-right-add-ℕ m' n n' K)
      ( preserves-leq-left-add-ℕ n m m' H)
```

```agda
abstract
  reflects-leq-left-add-ℕ :
    (k m n : ℕ) → (m +ℕ k) ≤-ℕ (n +ℕ k) → m ≤-ℕ n
  reflects-leq-left-add-ℕ zero-ℕ m n = id
  reflects-leq-left-add-ℕ (succ-ℕ k) m n = reflects-leq-left-add-ℕ k m n

  reflects-leq-right-add-ℕ :
    (k m n : ℕ) → (k +ℕ m) ≤-ℕ (k +ℕ n) → m ≤-ℕ n
  reflects-leq-right-add-ℕ k m n H =
    reflects-leq-left-add-ℕ k m n
      ( concatenate-eq-leq-eq-ℕ
        ( commutative-add-ℕ m k)
        ( H)
        ( commutative-add-ℕ k n))
```

```agda
abstract
  leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (m +ℕ n)
  leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
  leq-add-ℕ m (succ-ℕ n) =
    transitive-leq-ℕ
      ( m)
      ( m +ℕ n)
      ( succ-ℕ (m +ℕ n))
      ( succ-leq-ℕ (m +ℕ n))
      ( leq-add-ℕ m n)

  leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (n +ℕ m)
  leq-add-ℕ' m n =
    concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)
```

## Problem statement

Show that

```text
  (m ≤ n) ↔ (m · (k + 1) ≤ n · (k + 1))
```

holds for any `m, n, k : ℕ`.

## Solution

```agda
abstract
  preserves-leq-left-mul-ℕ :
    (k m n : ℕ) → m ≤-ℕ n → (m *ℕ k) ≤-ℕ (n *ℕ k)
  preserves-leq-left-mul-ℕ k zero-ℕ n p = star
  preserves-leq-left-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
    preserves-leq-left-add-ℕ k
      ( m *ℕ k)
      ( n *ℕ k)
      ( preserves-leq-left-mul-ℕ k m n p)

  preserves-leq-right-mul-ℕ :
    (k m n : ℕ) → m ≤-ℕ n → (k *ℕ m) ≤-ℕ (k *ℕ n)
  preserves-leq-right-mul-ℕ k m n H =
    concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ k m)
      ( preserves-leq-left-mul-ℕ k m n H)
      ( commutative-mul-ℕ n k)

  preserves-leq-mul-ℕ :
    (m m' n n' : ℕ) → m ≤-ℕ m' → n ≤-ℕ n' → (m *ℕ n) ≤-ℕ (m' *ℕ n')
  preserves-leq-mul-ℕ m m' n n' H K =
    transitive-leq-ℕ
      ( m *ℕ n)
      ( m' *ℕ n)
      ( m' *ℕ n')
      ( preserves-leq-right-mul-ℕ m' n n' K)
      ( preserves-leq-left-mul-ℕ n m m' H)
```

```agda
abstract
  reflects-leq-mul-ℕ :
    (k m n : ℕ) → (m *ℕ (succ-ℕ k)) ≤-ℕ (n *ℕ (succ-ℕ k)) → m ≤-ℕ n
  reflects-leq-mul-ℕ k zero-ℕ n p = star
  reflects-leq-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
    reflects-leq-mul-ℕ k m n
      ( reflects-leq-left-add-ℕ
        ( succ-ℕ k)
        ( m *ℕ (succ-ℕ k))
        ( n *ℕ (succ-ℕ k))
        ( p))

  reflects-leq-mul-ℕ' :
    (k m n : ℕ) → ((succ-ℕ k) *ℕ m) ≤-ℕ ((succ-ℕ k) *ℕ n) → m ≤-ℕ n
  reflects-leq-mul-ℕ' k m n H =
    reflects-leq-mul-ℕ k m n
      ( concatenate-eq-leq-eq-ℕ
        ( commutative-mul-ℕ m (succ-ℕ k))
        ( H)
        ( commutative-mul-ℕ (succ-ℕ k) n))
```

## Problem statement

Show that `k ≤ min(m, n)` holds if and only if both `k ≤ m` and `k ≤ n` hold,
and show that `max(m, n) ≤ k` holds if and only if both `m ≤ k` and `n ≤ k`
hold.

## Solution

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

ap-min-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → min-ℕ x y ＝ min-ℕ x' y'
ap-min-ℕ p q = ap-binary min-ℕ p q
```

```agda
abstract
  leq-min-ℕ :
    (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
  leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
  leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
  leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
  leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
  leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

  leq-left-leq-min-ℕ :
    (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
  leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
  leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
  leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
  leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
  leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
    leq-left-leq-min-ℕ k m n H

  leq-right-leq-min-ℕ :
    (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
  leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
  leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
  leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
  leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
  leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
    leq-right-leq-min-ℕ k m n H
```

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

max-ℕ' : ℕ → (ℕ → ℕ)
max-ℕ' x y = max-ℕ y x

ap-max-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → max-ℕ x y ＝ max-ℕ x' y'
ap-max-ℕ p q = ap-binary max-ℕ p q
```

```agda
abstract
  leq-max-ℕ :
    (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
  leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
  leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
  leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
  leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
  leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

  leq-left-leq-max-ℕ :
    (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → m ≤-ℕ k
  leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
  leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
  leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
  leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
    leq-left-leq-max-ℕ k m n H

  leq-right-leq-max-ℕ :
    (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → n ≤-ℕ k
  leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
  leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
  leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
  leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
    leq-right-leq-max-ℕ k m n H

  left-leq-max-ℕ : (m n : ℕ) → leq-ℕ m (max-ℕ m n)
  left-leq-max-ℕ m n =
    leq-left-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n))

  right-leq-max-ℕ : (m n : ℕ) → leq-ℕ n (max-ℕ m n)
  right-leq-max-ℕ m n =
    leq-right-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n))
```
