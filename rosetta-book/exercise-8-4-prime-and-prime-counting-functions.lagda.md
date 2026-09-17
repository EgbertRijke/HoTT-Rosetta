# Exercise 8.4

```agda
module exercise-8-4-prime-and-prime-counting-functions where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-8-1-decidability-and-decidable-equality
open import section-8-5-the-infinitude-of-primes
```

## Problem statement

<div class="subexenum">

Define the **prime function** `prime:ℕ→ℕ` for which `prime(n)` is the `n`-th prime.

Define the **prime-counting function** `π:ℕ→ℕ`, which counts for each `n:ℕ` the number of primes `p≤ n`.

</div>

## Solution

<!-- rosetta-item: exercise-8-4 -->

<!-- rosetta-agda-block: exercise-8-4-iterate -->

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate : ℕ → (X → X) → (X → X)
  iterate zero-ℕ f x = x
  iterate (succ-ℕ k) f x = f (iterate k f x)
```

<!-- rosetta-agda-block: exercise-8-4-prime-function -->

```agda
prime-ℕ : ℕ → ℕ
prime-ℕ n = iterate (succ-ℕ n) (λ x → pr1 (infinitude-of-primes-ℕ x)) 0

is-prime-prime-ℕ : (n : ℕ) → is-prime-ℕ (prime-ℕ n)
is-prime-prime-ℕ zero-ℕ = pr1 (pr2 (infinitude-of-primes-ℕ 0))
is-prime-prime-ℕ (succ-ℕ n) = pr1 (pr2 (infinitude-of-primes-ℕ (prime-ℕ n)))
```

<!-- rosetta-agda-block: exercise-8-4-prime-counting -->

```agda
prime-counting-succ-ℕ :
  (n : ℕ) → is-decidable (is-prime-ℕ (succ-ℕ n)) → ℕ → ℕ
prime-counting-succ-ℕ n (inl d) x = succ-ℕ x
prime-counting-succ-ℕ n (inr d) x = x

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = zero-ℕ
prime-counting-ℕ (succ-ℕ n) =
  prime-counting-succ-ℕ n
    ( is-decidable-is-prime-ℕ (succ-ℕ n))
    ( prime-counting-ℕ n)
```
