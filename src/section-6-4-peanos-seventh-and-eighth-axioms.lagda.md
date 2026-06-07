# Section 6.4 Peano's seventh and eighth axioms

```agda
module section-6-4-peanos-seventh-and-eighth-axioms where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-3-observational-equality-of-the-natural-numbers
```

Using the observational equality of `ℕ`, we can prove Peano's seventh and
eighth axioms.
In his *Arithmetices Principia*, the natural numbers are based at `1`, but today
it is customary to have the natural numbers based at `0`.
Adapting for this, the seventh and eighth axioms assert that

1. For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ (succ(m) = succ(n)).
```

2. For any natural number `n`, we have `0 ≠ succ(n)`.

## Theorem 6.4.1

For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ (succ(m) = succ(n)).
```

## Proof

The forward implication is given by the action on paths of the successor
function

```text
  ap_succ : (m = n) → (succ(m) = succ(n)).
```

```agda
ap-succ-ℕ : {m n : ℕ} → m ＝ n → succ-ℕ m ＝ succ-ℕ n
ap-succ-ℕ = ap succ-ℕ
```

The direction of interest is the converse, which asserts that the successor
function is injective.

Here we use the proposition that `(m = n) ↔ EqN(m, n)` for all `m, n : ℕ`.
Furthermore, we have `EqN(succ(m), succ(n)) ≐ EqN(m, n)`.
Therefore, we define the function `(succ(m) = succ(n)) → (m = n)` as the
composite of the maps

```text
  (succ(m) = succ(n)) → EqN(succ(m), succ(n)) →
  EqN(m, n) → (m = n).
```

```agda
is-injective-succ-ℕ :
  {m n : ℕ} → succ-ℕ m ＝ succ-ℕ n → m ＝ n
is-injective-succ-ℕ {m} {n} p = eq-EqN m n (EqN-eq p)

peano-7-ℕ :
  (m n : ℕ) →
  ((m ＝ n) → succ-ℕ m ＝ succ-ℕ n) ×
  ((succ-ℕ m ＝ succ-ℕ n) → m ＝ n)
peano-7-ℕ m n = ap-succ-ℕ , is-injective-succ-ℕ
```

## Theorem 6.4.2

For any natural number `n`, we have `0 ≠ succ(n)`.

## Proof

By the proposition that `(m = n) ↔ EqN(m, n)`, it follows that there is a family
of maps

```text
  (0 = n) → EqN(0, n)
```

indexed by `n : ℕ`.
Since `EqN(0, succ(n)) ≐ ∅` it follows that

```text
  (0 = succ(n)) → ∅,
```

which is precisely the claim.

```agda
is-nonzero-succ-ℕ : (n : ℕ) → succ-ℕ n ＝ zero-ℕ → empty
is-nonzero-succ-ℕ n ()

neq-zero-succ-ℕ : (n : ℕ) → zero-ℕ ＝ succ-ℕ n → empty
neq-zero-succ-ℕ n p = EqN-eq p

peano-8-ℕ : (n : ℕ) → zero-ℕ ＝ succ-ℕ n → empty
peano-8-ℕ = neq-zero-succ-ℕ
```

## Agda-unimath sources

- The successor injectivity and nonzero successor facts are defined in
  `elementary-number-theory.natural-numbers`.
- The corresponding Peano axiom packaging is in
  `elementary-number-theory.peano-arithmetic`.
