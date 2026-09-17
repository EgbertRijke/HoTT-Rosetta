# Exercise 8.1

```agda
module exercise-8-1-open-number-theory-conjectures where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
open import section-7-1-the-curry-howard-interpretation
open import exercise-7-2-divisibility-poset
open import section-8-5-the-infinitude-of-primes
```

## Problem statement

<div class="subexenum">

State Goldbach’s conjecture in type theory.

State the twin prime conjecture in type theory.

State the Collatz conjecture in type theory.

</div>

If you have a solution to any of these open problems, you should certainly formalize it before you submit it to the Annals of Mathematics.

## Solution

<!-- rosetta-item: exercise-8-1 -->

<!-- rosetta-agda-block: exercise-8-1-even -->

```agda
is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n
```

<!-- rosetta-agda-block: exercise-8-1-goldbach -->

```agda
Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ 2 n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × (p +ℕ q ＝ n))))
```

<!-- rosetta-agda-block: exercise-8-1-twin-prime -->

```agda
is-twin-prime-ℕ : ℕ → UU lzero
is-twin-prime-ℕ n = (is-prime-ℕ n) × (is-prime-ℕ (succ-ℕ (succ-ℕ n)))

twin-prime-conjecture : UU lzero
twin-prime-conjecture =
  (n : ℕ) → Σ ℕ (λ p → (is-twin-prime-ℕ p) × (leq-ℕ n p))
```

<!-- rosetta-agda-block: exercise-8-1-collatz -->

```agda
iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n = collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) → is-nonzero-ℕ n → Σ ℕ (λ k → is-one-ℕ (iterate-collatz k n))
```
