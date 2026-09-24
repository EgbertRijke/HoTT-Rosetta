# Section 6.4 Peano's seventh and eighth axioms

```agda
module section-6-4-peanos-seventh-and-eighth-axioms where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-3-observational-equality-of-the-natural-numbers
```

Using the observational equality of `ℕ`, we can prove Peano’s seventh and eighth axioms.
In his _Arithmetices Principia_ \[citation: `Peano`\], the natural numbers are based at `1`, but today it is customary to have the natural numbers based at `0`.
Adapting for this, the seventh and eighth axioms assert that

1. For any two natural numbers `m` and `n`, we have

```text
(m=n) ↔ (succ-ℕ(m) = succ-ℕ(n)).
```

2. For any natural number `n`, we have `0 ≠ succ-ℕ(n)`.

## Theorem 6.4.1

For any two natural numbers `m` and `n`, we have

```text
(m=n) ↔ (succ-ℕ(m)=succ-ℕ(n)).
```

### Proof

_Proof._ The forward implication is given by the action on paths of the successor function

```text
ap{succ-ℕ}:(m=n) → (succ-ℕ(m)=succ-ℕ(n)).
```

The direction of interest is the converse, which asserts that the successor function is injective.

Here we use Proposition 6.3.3, which asserts that `(m=n) ↔ Eq-ℕ(m,n)` for all `m,n:ℕ`.
Furthermore, we have `Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) ≐ Eq-ℕ(m,n)`.
Therefore, we obtain

```text
  [(succ-ℕ(m)=succ-ℕ(n))]  ------>  [(m=n)]
             |                       ^
             |                       |
             v                       |
[Eq-ℕ(succ-ℕ(m),succ-ℕ(n))]--id-->[Eq-ℕ(m,n)]
```

and we define the function `(succ-ℕ(m)=succ-ℕ(n)) → (m=n)` as the composite of the maps going down, then right, and then up. ◻

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

_Proof._ By Proposition 6.3.3 it follows that there is a family of maps

```text
(0=n) → Eq-ℕ(0,n).
```

indexed by `n:ℕ`.
Since `Eq-ℕ(0,succ-ℕ(n)) ≐ empty` it follows that

```text
(0=succ-ℕ(n)) → empty,
```

which is precisely the claim. ◻

```agda
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = (n ＝ zero-ℕ)

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-nonzero-succ-ℕ : (n : ℕ) → is-nonzero-ℕ (succ-ℕ n)
is-nonzero-succ-ℕ n ()

peano-8-ℕ : (n : ℕ) → succ-ℕ n ＝ zero-ℕ → empty
peano-8-ℕ = is-nonzero-succ-ℕ
```
