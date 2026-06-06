# Section 8.5 The infinitude of primes

```agda
module section-8-5-the-infinitude-of-primes where
```

When the natural numbers are ordered by the divisibility relation, the number
`1` is at the bottom.
Directly above `1` are the prime numbers.
Above the prime numbers are the multiples of two primes, then the multiples of
three primes, and so on.
At the top of this ordering we find `0`.
For any natural number `n`, the numbers strictly below `n` are the proper
divisors of `n`.
A prime number is therefore a number of which has exactly one proper divisor.

## Definition 8.5.1

1. Consider two natural numbers `d` and `n`.
Then `d` is said to be a **proper divisor** of `n` if it comes equipped with an
element of type

```text
  is-proper-divisor(n, d) := (d ≠ n) × (d | n).
```

2. A natural number `n` is said to be **prime** if it comes equipped with an
element of type

```text
  is-prime(n) := Π(x : ℕ) is-proper-divisor(n, x) ↔ (x = 1).
```

## Proposition 8.5.2

For any `n : ℕ`, the type `is-prime(n)` is decidable.

## Proof

We will first show that `is-prime(n) ↔ is-prime'(n)`, where

```text
  is-prime'(n) :=
    (n ≠ 1) × Π(x : ℕ) is-proper-divisor(n, x) → (x = 1).
```

For the forward direction, simply note that `1` is not a proper divisor of
itself, and therefore `1` is not a prime.
For the converse direction, suppose that `n ≠ 1` and that any proper divisor of
`n` is `1`.
Then it follows that `1` is a proper divisor of `n`, which implies that `n` is
prime.

Now we proceed by showing that the type `is-prime'(n)` is decidable for every
`n : ℕ`.
The proof is by case analysis on whether `n = 0` or `n ≠ 0`.
In the case where `n = 0`, note that any nonzero number is a proper divisor of
`0`, and therefore `is-prime'(0)` doesn't hold.
In particular, `is-prime'(0)` is decidable.

Now suppose that `n ≠ 0`.
In order to show that the type `is-prime'(n)` is decidable, note that the type
`n ≠ 1` is decidable since it is the negation of the decidable type `n = 1`.
Therefore it suffices to show that the type

```text
  Π(x : ℕ) is-proper-divisor(n, x) → (x = 1)
```

is decidable.
Since the types `(x ≠ n) × (x | n)` and `x = 1` are decidable, it follows from
Corollary 8.2.5 that it suffices to check that

```text
  ((x ≠ n) × (x | n)) → (x ≤ n)
```

for any `x : ℕ`.
This follows from the implication `(x | n) → (x ≤ n)`, which holds because we
have assumed that `n ≠ 0`.

The proof that there are infinitely many primes proceeds by constructing a prime
number larger than `n`, for any `n : ℕ`.
The number `n! + 1` is relatively prime with any number `x ≤ n`.
Therefore there is a least number `n < m` that is relatively prime with any
number `x ≤ n`, and it follows that this number `m` must be prime.

## Definition 8.5.3

For any two natural numbers `n` and `m`, we define the type

```text
  R(n, m) :=
    (n < m) × Π(x : ℕ) (x ≤ n) → ((x | m) → (x = 1)).
```

## Lemma 8.5.4

The type `R(n, m)` is decidable for each `n, m : ℕ`.

## Proof

The type `n < m` and, for each `x : ℕ`, both types `x ≤ n` and
`(x | m) → (x = 1)` are decidable, so it follows via Corollary 8.2.5 that the
product

```text
  Π(x : ℕ) (x ≤ n) → ((x | m) → (x = 1))
```

is decidable.

## Lemma 8.5.5

There is an element of type `R(n, n! + 1)` for each `n : ℕ`.

## Proof

The fact that `n < n! + 1` follows from the fact that `n ≤ n!`, which is shown
by induction.
We leave this to the reader, and focus on the second aspect of the claim: that
every `x ≤ n` that divides `n! + 1` must be equal to `1`.

To see this, note that any divisor of `n! + 1` is automatically nonzero, and
recall that any nonzero `x ≤ n` divides `n!` by Exercise 7.3.
Therefore it follows that any `x ≤ n` that divides `n! + 1` also divides `n!`,
and consequently it divides `1` as well.
Now we are done, because if `x` divides `1` then `x = 1`.

We finally show that there are infinitely many primes.

## Theorem 8.5.6

For each `n : ℕ`, there is a prime number `p : ℕ` such that `n < p`.

## Proof

It suffices to show that for each *nonzero* `n : ℕ`, there is a prime number
`p : ℕ` such that `n ≤ p`.
Let `n` be a nonzero natural number.

Since the type `R(n, m)` is decidable for each `m : ℕ`, and since
`R(n, n! + 1)` holds by Lemma 8.5.5, it follows by the well-ordering principle
of `ℕ` that there is a minimal `m : ℕ` such that `R(n, m)` holds.
In order to prove the theorem, we will show that this number `m` is prime, i.e.,
that there is an element of type

```text
  (m ≠ 1) × Π(x : ℕ) is-proper-divisor(m, x) → (x = 1).
```

First, we note that `m ≠ 1` because `n < m` holds by construction, and `n` is
assumed to be nonzero.
Therefore it suffices to show that `1` is the only proper divisor of `m`.
Let `x` be a proper divisor of `m`.
Since `R(n, m)` holds by construction, we will prove that `x = 1` by showing
that `x ≤ n` holds.

Since `m` is nonzero, it follows from the assumption that `x | m` that `x < m`.
By minimality of `m`, it therefore follows that `¬ R(n, x)` holds.
However, any divisor of `x` is also a divisor of `m` by transitivity of the
divisibility relation.
Therefore it follows that any `y ≤ n` that divides `x` must be `1`.
In other words:

```text
  Π(y : ℕ) (y ≤ n) → ((y | x) → (y = 1))
```

holds.
Since `¬ R(n, x)` holds, we conclude now that `n ≮ x`.
To finish the proof, it follows that `x ≤ n`.
