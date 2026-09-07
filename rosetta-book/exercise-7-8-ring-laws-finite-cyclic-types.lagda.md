# Exercise 7.8

```agda
module exercise-7-8-ring-laws-finite-cyclic-types where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import path-algebra
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-5-distance-natural-numbers
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import exercise-7-4-successor-finite-types-addition
```

## Problem statement

The multiplication operation `x,y↦ xy` on `ℤ/{(k+1)}` is defined by
```text
xy ≔ [nat-Fin(x)nat-Fin(y)]_{k+1}.
```

<div class="subexenum">

Show that `nat-Fin(xy)≡nat-Fin(x)nat-Fin(y)mod{k+1}` for each `x,y:ℤ/{(k+1)}`.

Show that
```text
xy≡ x'y'mod k
```
for any `x,y,x',y':ℕ` such that `x≡ x'` and `y≡ y' mod k`.

Show that multiplication on `ℤ/{(k+1)}` satisfies the laws of a commutative ring:
```text
(xy)z = x(yz) xy = yx
1x = x x1 = x
x(y+z) = xy+xz (x+y)z = xz+yz.
```

</div>

## Solution

<!-- rosetta-item: exercise-7-8 -->

<!-- rosetta-agda-block: exercise-7-8-multiplication-finite -->

```agda
mul-Fin :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin (succ-ℕ k) x y =
  mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))

mul-Fin' :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin' k x y = mul-Fin k y x

ap-mul-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → mul-Fin k x y ＝ mul-Fin k x' y'
ap-mul-Fin k p q = ap-binary (mul-Fin k) p q

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin k (mul-Fin k x y)) ((nat-Fin k x) *ℕ (nat-Fin k y))
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
```

<!-- rosetta-agda-block: exercise-7-8-action-addition-finite -->

```agda
ap-add-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → add-Fin k x y ＝ add-Fin k x' y'
ap-add-Fin k p q = ap-binary (add-Fin k) p q
```

<!-- rosetta-agda-block: exercise-7-8-congruence-multiplication-natural -->

```agda
scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (z *ℕ x) (z *ℕ y)
scalar-invariant-cong-ℕ k x y z =
  ind-Σ (λ d p →
    pair (z *ℕ d)
      ((associative-mul-ℕ z d k) ∙
        ((ap (z *ℕ_) p) ∙
          (left-distributive-mul-dist-ℕ x y z))))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (x *ℕ z) (y *ℕ z)
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)
congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (x *ℕ y) (x' *ℕ y')
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (x *ℕ y) (x *ℕ y') (x' *ℕ y')
    ( scalar-invariant-cong-ℕ' k x x' y' H)
    ( scalar-invariant-cong-ℕ k y y' x K)
```

<!-- rosetta-agda-block: exercise-7-8-ring-laws-finite -->

```agda
associative-mul-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (mul-Fin k x y) z ＝ mul-Fin k x (mul-Fin k y z)
associative-mul-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)) *ℕ
      ( nat-Fin (succ-ℕ k) z))
    ( ( nat-Fin (succ-ℕ k) x) *ℕ
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 =
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)) *ℕ
          ( nat-Fin (succ-ℕ k) z)}
      { x2 =
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y)) *ℕ
          ( nat-Fin (succ-ℕ k) z)}
      { x3 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)}
        { y = nat-Fin (succ-ℕ k) z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) z)))
      ( associative-mul-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( symmetric-cong-ℕ
        ( succ-ℕ k)
        ( ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)))
        ( ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (succ-ℕ k) x}
          { y = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  (k : ℕ) (x y : Fin k) → mul-Fin k x y ＝ mul-Fin k y x
commutative-mul-Fin (succ-ℕ k) x y =
  eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
    ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y)))

left-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (one-Fin k) x ＝ x
left-unit-law-mul-Fin zero-ℕ (inr _) = refl
left-unit-law-mul-Fin (succ-ℕ k) x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( ( nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k))) *ℕ
      ( nat-Fin (succ-ℕ (succ-ℕ k)) x))
    ( nat-Fin (succ-ℕ (succ-ℕ k)) x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap
          ( _*ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) x))
          ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) x))))) ∙
  ( is-section-nat-Fin (succ-ℕ k) x)

right-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (one-Fin k) ＝ x
right-unit-law-mul-Fin k x =
  ( commutative-mul-Fin (succ-ℕ k) x (one-Fin k)) ∙
  ( left-unit-law-mul-Fin k x)

left-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (zero-Fin k) x ＝ zero-Fin k
left-zero-law-mul-Fin k x =
  ( eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) (zero-Fin k)) *ℕ (nat-Fin (succ-ℕ k) x))
    ( nat-Fin (succ-ℕ k) (zero-Fin k))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { (nat-Fin (succ-ℕ k) (zero-Fin k)) *ℕ (nat-Fin (succ-ℕ k) x)}
      { nat-Fin (succ-ℕ k) (zero-Fin k)}
      ( ( ap (_*ℕ (nat-Fin (succ-ℕ k) x)) (is-zero-nat-zero-Fin {k})) ∙
        ( inv (is-zero-nat-zero-Fin {k}))))) ∙
  ( is-section-nat-Fin k (zero-Fin k))

right-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (zero-Fin k) ＝ zero-Fin k
right-zero-law-mul-Fin k x =
  ( commutative-mul-Fin (succ-ℕ k) x (zero-Fin k)) ∙
  ( left-zero-law-mul-Fin k x)

left-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k x (add-Fin k y z) ＝ add-Fin k (mul-Fin k x y) (mul-Fin k x z)
left-distributive-mul-add-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( ( nat-Fin (succ-ℕ k) x) *ℕ
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)))
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z))}
      { x2 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))}
      { x3 =
        add-ℕ
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) x}
        { y = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)}
        { x' = nat-Fin (succ-ℕ k) x}
        { y' = (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( symmetric-cong-ℕ (succ-ℕ k)
        ( add-ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)))
        ( add-ℕ
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)}
          { y = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)}
          { x' = (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y)}
          { y' = (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (add-Fin k x y) z ＝ add-Fin k (mul-Fin k x z) (mul-Fin k y z)
right-distributive-mul-add-Fin k x y z =
  ( commutative-mul-Fin k (add-Fin k x y) z) ∙
  ( ( left-distributive-mul-add-Fin k z x y) ∙
    ( ap-add-Fin k (commutative-mul-Fin k z x) (commutative-mul-Fin k z y)))
```
