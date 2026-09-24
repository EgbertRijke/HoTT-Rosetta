# Section 6.4 Peano's seventh and eighth axioms

```agda
module section-6-4-peanos-seventh-and-eighth-axioms where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-3-observational-equality-of-the-natural-numbers
```

Using the observational equality of `ℕ`, we can prove Peano’s seventh and eighth axioms.
In his _Arithmetices Principia_ \[citation: `Peano`\], the natural numbers are based at `1`, but today it is customary to have the natural numbers based at `0`.
Adapting for this, the seventh and eighth axioms assert that

1. For any two natural numbers `m` and `n`, we have

   ```text
     (m = n) ↔ (succ-ℕ(m) = succ-ℕ(n)).
   ```

2. For any natural number `n`, we have `0 ≠ succ-ℕ(n)`.

## Theorem 6.4.1

For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ (succ-ℕ(m) = succ-ℕ(n)).
```

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = {x y : A} → f x ＝ f y → x ＝ y

injection : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
injection A B = Σ (A → B) is-injective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : injection A B)
  where

  map-injection : A → B
  map-injection = pr1 f

  is-injective-map-injection : is-injective map-injection
  is-injective-map-injection = pr2 f
```

### Proof

The forward implication is given by the action on paths of the successor function

```text
  ap_{succ-ℕ} : (m = n) → (succ-ℕ(m) = succ-ℕ(n)).
```

The direction of interest is the converse, which asserts that the successor function is injective.

Here we use Proposition 6.3.3, which asserts that `(m = n) ↔ Eq-ℕ(m,n)` for all `m, n : ℕ`.
Furthermore, we have `Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) ≐ Eq-ℕ(m,n)`.
Therefore, we obtain

```text
      succ-ℕ(m) = succ-ℕ(n) ------> m = n
                |                     ∧
                |                     |
                ∨                     |
  Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) ----> Eq-ℕ(m,n)
                             id
```

and we define the function `(succ-ℕ(m) = succ-ℕ(n)) → (m = n)` as the composite of the maps going down, then right, and then up. ◻

```agda
ap-succ-ℕ : {m n : ℕ} → m ＝ n → succ-ℕ m ＝ succ-ℕ n
ap-succ-ℕ = ap succ-ℕ

is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ refl = refl

peano-7-ℕ :
  (m n : ℕ) → ((m ＝ n) ↔ (succ-ℕ m ＝ succ-ℕ n))
pr1 (peano-7-ℕ m n) refl = refl
pr2 (peano-7-ℕ m n) = is-injective-succ-ℕ
```

## Theorem 6.4.2

For any natural number `n`, we have `0 ≠ succ-ℕ(n)`.

### Proof

By Proposition 6.3.3 it follows that there is a family of maps

```text
  (0 = n) → Eq-ℕ(0,n).
```

indexed by `n : ℕ`.
Since `Eq-ℕ(0,succ-ℕ(n)) ≐ empty` it follows that

```text
  (0 = succ-ℕ(n)) → empty,
```

which is precisely the claim. ◻

```agda
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = (n ＝ zero-ℕ)

is-zero-ℕ' : ℕ → UU lzero
is-zero-ℕ' n = (zero-ℕ ＝ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = (n ＝ 1)

is-one-ℕ' : ℕ → UU lzero
is-one-ℕ' n = (1 ＝ n)

is-not-one-ℕ : ℕ → UU lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → UU lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → n ＝ succ-ℕ y)

pred-is-successor-ℕ :
  (n : ℕ) → is-successor-ℕ n → ℕ
pred-is-successor-ℕ n H = pr1 H

eq-pred-is-successor-ℕ :
  (n : ℕ) (H : is-successor-ℕ n) → succ-ℕ (pred-is-successor-ℕ n H) ＝ n
eq-pred-is-successor-ℕ n H = inv (pr2 H)

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ x ()

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ (x , refl) ()

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
pr1 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = x
pr2 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = refl

pred-is-nonzero-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → ℕ
pred-is-nonzero-ℕ n H =
  pred-is-successor-ℕ n (is-successor-is-nonzero-ℕ H)

eq-pred-is-nonzero-ℕ :
  (n : ℕ) (H : is-nonzero-ℕ n) → succ-ℕ (pred-is-nonzero-ℕ n H) ＝ n
eq-pred-is-nonzero-ℕ n H =
  eq-pred-is-successor-ℕ n (is-successor-is-nonzero-ℕ H)

peano-8-ℕ : (n : ℕ) → zero-ℕ ＝ succ-ℕ n → empty
peano-8-ℕ n p = is-nonzero-is-successor-ℕ (n , p) refl
```
