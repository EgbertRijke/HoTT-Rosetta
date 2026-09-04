# Section 8.5 The infinitude of primes

```agda
module section-8-5-the-infinitude-of-primes where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import exercise-3-3-triangular-numbers-and-factorials
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-3-negation
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-6-3-observational-equality-of-the-natural-numbers
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import exercise-7-1-divisibility-three-for-two
open import exercise-7-2-divisibility-poset
open import exercise-7-3-divisibility-factorials
open import exercise-7-9-euclidean-division
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
open import section-8-3-the-well-ordering-principle-of-natural-numbers
open import section-8-4-the-greatest-common-divisor
```

<!-- rosetta-item: section-8.5 -->

When the natural numbers are ordered by the divisibility relation, the number `1` is at the bottom.
Directly above `1` are the prime numbers.
Above the prime numbers are the multiples of two primes, then the multiples of three primes, and so on.
At the top of this ordering we find `0`.
For any natural number `n`, the numbers strictly below `n` are the proper divisors of `n`.
A prime number is therefore a number of which has exactly one proper divisor.

### Agda prerequisites for Section 8.5

<!-- rosetta-agda-block: definition-8.5.1-multiplication-bound -->

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

  leq-mul-is-nonzero-ℕ :
    (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (x *ℕ k)
  leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
  ... | (l , refl) = leq-mul-ℕ l x

  leq-mul-is-nonzero-ℕ' :
    (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (k *ℕ x)
  leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
  ... | (l , refl) = leq-mul-ℕ' l x
```

<!-- rosetta-agda-block: definition-8.5.1-weak-order-split -->

```agda
eq-or-le-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → ((x ＝ y) + (le-ℕ x y))
eq-or-le-leq-ℕ zero-ℕ zero-ℕ H = inl refl
eq-or-le-leq-ℕ zero-ℕ (succ-ℕ y) H = inr star
eq-or-le-leq-ℕ (succ-ℕ x) (succ-ℕ y) H =
  map-coproduct (ap succ-ℕ) section-2-2-ordinary-function-types.id (eq-or-le-leq-ℕ x y H)
```

<!-- rosetta-agda-block: definition-8.5.1-divisor-bound -->

```agda
abstract
  leq-div-succ-ℕ-8-5 : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
  leq-div-succ-ℕ-8-5 d x (pair (succ-ℕ k) p) =
    concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

  leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
  leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
  ... | (pair y refl) = leq-div-succ-ℕ-8-5 d y H
```

<!-- rosetta-agda-block: definition-8.5.1-negated-equality -->

```agda
nonequal : {l : Level} {A : Type l} → A → A → Type l
nonequal x y = ¬ (x ＝ y)

infix 6 _≠_
_≠_ = nonequal
```

<!-- rosetta-agda-block: definition-8.5.1-strict-from-weak-unequal -->

```agda
abstract
  le-leq-neq-ℕ : {x y : ℕ} → x ≤-ℕ y → x ≠ y → le-ℕ x y
  le-leq-neq-ℕ {x} {y} x≤y x≠y =
    rec-coproduct (ex-falso ∘ x≠y) section-2-2-ordinary-function-types.id
      (eq-or-le-leq-ℕ x y x≤y)
```

<!-- rosetta-agda-block: theorem-8.5.6-empty-product-factor -->

```agda
is-empty-left-factor-is-empty-product :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → is-empty (A × B) → B → is-empty A
is-empty-left-factor-is-empty-product f b a = f (pair a b)
```

## Definition 8.5.1

<!-- rosetta-item: definition-8.5.1 -->

 

1.  Consider two natural numbers `d` and `n`.
Then `d` is said to be a **proper divisor** of `n` if it comes equipped with an element of type
```text
is-proper-divisor(n,d)≔ (d≠ n)× (d| n).
```

2.  A natural number `n` is said to be **prime** if it comes equipped with an element of type
```text
is-prime(n)≔ Π(x:ℕ) is-proper-divisor(n,x)↔ (x=1).
```

<!-- rosetta-agda-block: definition-8.5.1-proper-divisor -->

```agda
is-proper-divisor-ℕ : ℕ → ℕ → Type lzero
is-proper-divisor-ℕ n d = (d ≠ n) × (div-ℕ d n)

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-product
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = is-nonzero-succ-ℕ n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)
```

<!-- rosetta-agda-block: definition-8.5.1-prime -->

```agda
is-prime-ℕ : ℕ → Type lzero
is-prime-ℕ n = (x : ℕ) → (is-proper-divisor-ℕ n x ↔ is-one-ℕ x)
```
<!-- rosetta-item-end: definition-8.5.1 -->

## Proposition 8.5.2

<!-- rosetta-item: proposition-8.5.2 -->

For any `n:ℕ`, the type `is-prime(n)` is decidable.

### Proof

<!-- rosetta-item: subheading-8.5-proof -->

*Proof.* We will first show that `is-prime(n)↔is-prime'(n)`, where
```text
is-prime'(n)≔ (n≠ 1)× Π(x:ℕ) is-proper-divisor(n,x)→ (x=1).
```
For the forward direction, simply note that `1` is not a proper divisor of itself, and therefore `1` is not a prime.
For the converse direction, suppose that `n≠ 1` and that any proper divisor of `n` is `1`.
Then it follows that `1` is a proper divisor of `n`, which implies that `n` is prime.

Now we proceed by showing that the type `is-prime'(n)` is decidable for every `n:ℕ`.
The proof is by case analysis on whether `n=0` or `n≠ 0`.
In the case where `n=0`, note that any nonzero number is a proper divisor of `0`, and therefore `is-prime'(0)` doesn’t hold.
In particular, `is-prime'(0)` is decidable.

Now suppose that `n≠ 0`.
In order to show that the type `is-prime'(n)` is decidable, note that the type `n≠ 1` is decidable since it is the negation of the decidable type `n=1`.
Therefore it suffices to show that the type
```text
Π(x:ℕ) is-proper-divisor(n,x)→ (x=1)
```
is decidable.
Since the types `(x≠ n)× (x| n)` and `x=1` are decidable, it follows from Corollary 8.2.5 that it suffices to check that
```text
((x≠ n)× (x| n))→ (x≤ n)
```
for any `x:ℕ`.
This follows from the implication `(x| n)→ (x≤ n)`, which holds because we have assumed that `n≠ 0`. ◻

<!-- rosetta-agda-block: proposition-8.5.2-divisor-of-one -->

```agda
is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)
```

<!-- rosetta-agda-block: proposition-8.5.2-proper-divisor-one -->

```agda
is-proper-divisor-one-is-proper-divisor-ℕ :
  {n x : ℕ} → is-proper-divisor-ℕ n x → is-proper-divisor-ℕ n 1
pr1 (is-proper-divisor-one-is-proper-divisor-ℕ {.1} {x} H) refl =
  pr1 H (is-one-div-one-ℕ x (pr2 H))
pr1 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) = n
pr2 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) =
  right-unit-law-mul-ℕ n
```

<!-- rosetta-agda-block: proposition-8.5.2-prime-easy -->

```agda
is-one-is-proper-divisor-ℕ : ℕ → Type lzero
is-one-is-proper-divisor-ℕ n =
  (x : ℕ) → is-proper-divisor-ℕ n x → is-one-ℕ x

is-prime-easy-ℕ : ℕ → Type lzero
is-prime-easy-ℕ n = (is-not-one-ℕ n) × (is-one-is-proper-divisor-ℕ n)
```

<!-- rosetta-agda-block: proposition-8.5.2-one-not-prime -->

```agda
abstract
  is-not-one-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-not-one-ℕ n
  is-not-one-is-prime-ℕ n H p = pr1 (pr2 (H 1) refl) (inv p)
```

<!-- rosetta-agda-block: proposition-8.5.2-prime-equivalence -->

```agda
abstract
  is-prime-easy-is-prime-ℕ : (n : ℕ) → is-prime-ℕ n → is-prime-easy-ℕ n
  pr1 (is-prime-easy-is-prime-ℕ n H) = is-not-one-is-prime-ℕ n H
  pr2 (is-prime-easy-is-prime-ℕ n H) x = forward-implication (H x)

  is-prime-is-prime-easy-ℕ : (n : ℕ) → is-prime-easy-ℕ n → is-prime-ℕ n
  pr1 (is-prime-is-prime-easy-ℕ n H x) = pr2 H x
  pr1 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) q =
    pr1 H (inv q)
  pr2 (pr2 (is-prime-is-prime-easy-ℕ n H .(succ-ℕ zero-ℕ)) refl) = div-one-ℕ n
```

<!-- rosetta-agda-block: proposition-8.5.2-two-not-one -->

```agda
is-not-one-two-ℕ : is-not-one-ℕ 2
is-not-one-two-ℕ ()
```

<!-- rosetta-agda-block: proposition-8.5.2-prime-decidable -->

```agda
is-decidable-is-prime-easy-ℕ : (n : ℕ) → is-decidable (is-prime-easy-ℕ n)
is-decidable-is-prime-easy-ℕ zero-ℕ =
  inr
    ( λ H →
      is-not-one-two-ℕ (pr2 H 2 (is-proper-divisor-zero-succ-ℕ 1)))
is-decidable-is-prime-easy-ℕ (succ-ℕ n) =
  is-decidable-product
    ( is-decidable-neg (is-decidable-is-one-ℕ (succ-ℕ n)))
    ( is-decidable-bounded-Π-ℕ
      ( is-proper-divisor-ℕ (succ-ℕ n))
      ( is-one-ℕ)
      ( is-decidable-is-proper-divisor-ℕ (succ-ℕ n))
      ( is-decidable-is-one-ℕ)
      ( succ-ℕ n)
      ( λ x H → leq-div-succ-ℕ x n (pr2 H)))

is-decidable-is-prime-ℕ : (n : ℕ) → is-decidable (is-prime-ℕ n)
is-decidable-is-prime-ℕ n =
  is-decidable-iff
    ( is-prime-is-prime-easy-ℕ n)
    ( is-prime-easy-is-prime-ℕ n)
    ( is-decidable-is-prime-easy-ℕ n)
```
<!-- rosetta-item-end: proposition-8.5.2 -->

The proof that there are infinitely many primes proceeds by constructing a prime number larger than `n`, for any `n:ℕ`.
The number `n!+1` is relatively prime with any number `x≤ n`.
Therefore there is a least number `n<m` that is relatively prime with any number `x≤ n`, and it follows that this number `m` must be prime.

## Definition 8.5.3

<!-- rosetta-item: definition-8.5.3 -->

For any two natural numbers `n` and `m`, we define the type
```text
R(n,m)≔ (n<m)× Π(x:ℕ) (x≤ n)→ ((x| m)→ (x=1)).
```

<!-- rosetta-agda-block: definition-8.5.3-sieve -->

```agda
is-one-is-divisor-below-ℕ : ℕ → ℕ → Type lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x

in-sieve-of-eratosthenes-ℕ : ℕ → ℕ → Type lzero
in-sieve-of-eratosthenes-ℕ n a =
  (le-ℕ n a) × (is-one-is-divisor-below-ℕ n a)

le-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → in-sieve-of-eratosthenes-ℕ n a → le-ℕ n a
le-in-sieve-of-eratosthenes-ℕ n a = pr1
```
<!-- rosetta-item-end: definition-8.5.3 -->

## Lemma 8.5.4

<!-- rosetta-item: lemma-8.5.4 -->

The type `R(n,m)` is decidable for each `n,m:ℕ`.

### Proof

<!-- rosetta-item: subheading-8.5-proof-2 -->

*Proof.* The type `n<m` and, and for each `x:ℕ` both types `x≤ n` and `(x| m)→ (x=1)` are decidable, so it follows via Corollary 8.2.5 that the product
```text
Π(x:ℕ) (x≤ n)→ ((x| m)→ (x=1))
```
is decidable. ◻

<!-- rosetta-agda-block: lemma-8.5.4-sieve-decidable -->

```agda
is-decidable-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → is-decidable (in-sieve-of-eratosthenes-ℕ n a)
is-decidable-in-sieve-of-eratosthenes-ℕ n a =
  is-decidable-product
    ( is-decidable-le-ℕ n a)
    ( is-decidable-bounded-Π-ℕ
      ( λ x → leq-ℕ x n)
      ( λ x → div-ℕ x a → is-one-ℕ x)
      ( λ x → is-decidable-leq-ℕ x n)
      ( λ x →
        is-decidable-function-type
          ( is-decidable-div-ℕ x a)
          ( is-decidable-is-one-ℕ x))
      ( n)
      ( λ x → section-2-2-ordinary-function-types.id))
```
<!-- rosetta-item-end: lemma-8.5.4 -->

## Lemma 8.5.5

<!-- rosetta-item: lemma-8.5.5; latex-label: lem:succ-factorial-has-one-bounded-divisor -->

There is an element of type `R(n,{n!}+1)` for each `n:ℕ`.

### Proof

<!-- rosetta-item: subheading-8.5-proof-3 -->

*Proof.* The fact that `n<{n!}+1` follows from the fact that `n≤ n!`, which is shown by induction.
We leave this to the reader, and focus on the second aspect of the claim: that every `x≤ n` that divides `{n!}+1` must be equal to `1`.

To see this, note that any divisor of `{n!}+1` is automatically nonzero, and recall that any nonzero `x≤ n` divides `n!` by Exercise 7.3.
Therefore it follows that any `x≤ n` that divides `{n!}+1` also divides `n!`, and consequently it divides `1` as well.
Now we are done, because if `x` divides `1` then `x=1`. ◻

<!-- rosetta-agda-block: lemma-8.5.5-zero-divisor -->

```agda
is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d
```

<!-- rosetta-agda-block: lemma-8.5.5-consecutive-divisor -->

```agda
abstract
  is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
  is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)
```

<!-- rosetta-agda-block: lemma-8.5.5-product-nonzero -->

```agda
abstract
  is-nonzero-mul-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → is-nonzero-ℕ y → is-nonzero-ℕ (x *ℕ y)
  is-nonzero-mul-ℕ x y H K p =
    K (is-injective-left-mul-ℕ x H (p ∙ (inv (right-zero-law-mul-ℕ x))))
```

<!-- rosetta-agda-block: lemma-8.5.5-factorial-nonzero -->

```agda
abstract
  is-nonzero-factorial-ℕ :
    (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
  is-nonzero-factorial-ℕ zero-ℕ = Eq-eq-ℕ
  is-nonzero-factorial-ℕ (succ-ℕ x) =
    is-nonzero-mul-ℕ
      ( factorial-ℕ x)
      ( succ-ℕ x)
      ( is-nonzero-factorial-ℕ x)
      ( is-nonzero-succ-ℕ x)
```

<!-- rosetta-agda-block: lemma-8.5.5-factorial-bound -->

```agda
abstract
  leq-factorial-ℕ :
    (n : ℕ) → leq-ℕ n (factorial-ℕ n)
  leq-factorial-ℕ zero-ℕ = leq-zero-ℕ 1
  leq-factorial-ℕ (succ-ℕ n) =
    leq-mul-is-nonzero-ℕ'
      ( factorial-ℕ n)
      ( succ-ℕ n)
      ( is-nonzero-factorial-ℕ n)
```

<!-- rosetta-agda-block: lemma-8.5.5-factorial-sieve -->

```agda
in-sieve-of-eratosthenes-succ-factorial-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (succ-ℕ (factorial-ℕ n))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) = star
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) x l d =
  ex-falso
    ( Eq-eq-ℕ
      ( is-zero-is-zero-div-ℕ x 2 d (is-zero-leq-zero-ℕ x l)))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) =
  concatenate-leq-le-ℕ
    { succ-ℕ n}
    { factorial-ℕ (succ-ℕ n)}
    { succ-ℕ (factorial-ℕ (succ-ℕ n))}
    ( leq-factorial-ℕ (succ-ℕ n))
    ( succ-le-ℕ (factorial-ℕ (succ-ℕ n)))
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) x l (pair y p) with
  is-decidable-is-zero-ℕ x
... | inl refl =
  ex-falso
    ( is-nonzero-succ-ℕ
      ( factorial-ℕ (succ-ℕ n))
      ( inv p ∙ (right-zero-law-mul-ℕ y)))
... | inr f =
  is-one-div-ℕ x
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-ℕ (succ-ℕ n) x l f)
    ( pair y p)
```
<!-- rosetta-item-end: lemma-8.5.5 -->

We finally show that there are infinitely many primes.

## Theorem 8.5.6

<!-- rosetta-item: theorem-8.5.6 -->

For each `n:ℕ`, there is a prime number `p:ℕ` such that `n< p`.

### Proof

<!-- rosetta-item: subheading-8.5-proof-4 -->

*Proof.* It suffices to show that for each *nonzero* `n:ℕ`, there is a prime number `p:ℕ` such that `n≤ p`.
Let `n` be a nonzero natural number.

Since the type `R(n,m)` is decidable for each `m:ℕ`, and since `R(n,{n!}+1)` holds by Lemma 8.5.5, it follows by the well-ordering principle of `ℕ` (Theorem 8.3.2) that there is a minimal `m:ℕ` such that `R(n,m)` holds.
In order to prove the theorem, we will show that this number `m` is prime, i.e., that there is an element of type
```text
(m≠ 1)× Π(x:ℕ) is-proper-divisor(m,x)→ (x=1).
```

First, we note that `m≠ 1` because `n<m` holds by construction, and `n` is assumed to be nonzero.
Therefore it suffices to show that `1` is the only proper divisor of `m`.
Let `x` be a proper divisor of `m`.
Since `R(n,m)` holds by construction, we will prove that `x=1` by showing that `x≤ n` holds.

Since `m` is nonzero, it follows from the assumption that `x| m` that `x<m`.
By minimality of `m`, it therefore follows that `¬ R(n,x)` holds.
However, any divisor of `x` is also a divisor of `m` by transitivity of the divisibility relation.
Therefore it follows that any `y≤ n` that divides `x` must be `1`.
In other words:
```text
Π(y:ℕ) (y≤ n)→ ((y| x)→ (y=1))
```
holds.
Since `¬ R(n,x)` holds, we conclude now that `n≮ x`.
To finish the proof, it follows that `x≤ n`. ◻

<!-- rosetta-agda-block: theorem-8.5.6-two-prime -->

```agda
abstract
  is-one-is-proper-divisor-two-ℕ : is-one-is-proper-divisor-ℕ 2
  is-one-is-proper-divisor-two-ℕ zero-ℕ (pair f (pair k p)) =
    ex-falso (f (inv (right-zero-law-mul-ℕ k) ∙ p))
  is-one-is-proper-divisor-two-ℕ (succ-ℕ zero-ℕ) (pair f H) = refl
  is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) (pair f H) =
    ex-falso (f refl)
  is-one-is-proper-divisor-two-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) (pair f H) =
    ex-falso (leq-div-succ-ℕ (succ-ℕ (succ-ℕ (succ-ℕ x))) 1 H)

is-prime-easy-two-ℕ : is-prime-easy-ℕ 2
pr1 is-prime-easy-two-ℕ = Eq-eq-ℕ
pr2 is-prime-easy-two-ℕ = is-one-is-proper-divisor-two-ℕ

is-prime-two-ℕ : is-prime-ℕ 2
is-prime-two-ℕ =
  is-prime-is-prime-easy-ℕ 2 is-prime-easy-two-ℕ
```

<!-- rosetta-agda-block: theorem-8.5.6-infinitude-type -->

```agda
Infinitude-Of-Primes-ℕ : Type lzero
Infinitude-Of-Primes-ℕ = (n : ℕ) → Σ ℕ (λ p → is-prime-ℕ p × le-ℕ n p)
```

<!-- rosetta-agda-block: theorem-8.5.6-infinitude -->

```agda
minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n =
  well-ordering-principle-ℕ
    ( in-sieve-of-eratosthenes-ℕ n)
    ( is-decidable-in-sieve-of-eratosthenes-ℕ n)
    ( pair
      ( succ-ℕ (factorial-ℕ n))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕ n))

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = pr1 (minimal-element-in-sieve-of-eratosthenes-ℕ n)

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n =
  pr1 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n =
  pr2 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = pr1 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n =
  is-nonzero-le-ℕ n (larger-prime-ℕ n) (le-larger-prime-ℕ n)

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n =
  pr2 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ H
... | pair k refl =
  neq-le-ℕ {1} {larger-prime-ℕ n}
    ( concatenate-leq-le-ℕ {1} {succ-ℕ k} {larger-prime-ℕ n} star
      ( le-larger-prime-ℕ (succ-ℕ k)))
    ( inv p)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K =
  ex-falso
    ( contradiction-le-ℕ x (larger-prime-ℕ n)
      ( le-is-proper-divisor-ℕ x (larger-prime-ℕ n)
        ( is-nonzero-larger-prime-ℕ n)
        ( H))
      ( is-lower-bound-larger-prime-ℕ n x K))

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) =
  is-one-is-divisor-below-larger-prime-ℕ n x
    ( leq-not-le-ℕ n x
      ( is-empty-left-factor-is-empty-product
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x
          ( pair f K))
        ( λ y l d →
          is-one-is-divisor-below-larger-prime-ℕ n y l
            ( transitive-div-ℕ y x (larger-prime-ℕ n) K d))))
    ( K)

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H =
  is-prime-is-prime-easy-ℕ
    ( larger-prime-ℕ n)
    ( pair
      ( is-not-one-larger-prime-ℕ n H)
      ( is-one-is-proper-divisor-larger-prime-ℕ n H))

infinitude-of-primes-ℕ : Infinitude-Of-Primes-ℕ
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = pair 2 (pair is-prime-two-ℕ star)
... | inr H =
  pair
    ( larger-prime-ℕ n)
    ( pair
      ( is-prime-larger-prime-ℕ n H)
      ( le-larger-prime-ℕ n))
```
<!-- rosetta-item-end: theorem-8.5.6 -->
