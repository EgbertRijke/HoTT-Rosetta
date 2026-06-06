# Section 8.4 The greatest common divisor

```agda
module section-8-4-the-greatest-common-divisor where
```

The greatest common divisor of two natural numbers `a` and `b` is a natural
number `gcd(a, b)` that satisfies the property that

```text
  x | a and x | b    if and only if    x | gcd(a, b)
```

for any `x : ℕ`.
In other words, any number `x : ℕ` that divides both `a` and `b` also divides
the greatest common divisor.
Moreover, since `gcd(a, b)` divides itself, it follows from the reverse
implication that `gcd(a, b)` divides both `a` and `b`.

This property can also be seen as the *specification* of what it means to be a
greatest common divisor of `a` and `b`.
In formal developments of mathematics, when you're about to construct an object
that satisfies a certain specification, it can be useful to start out with that
specification.
For example, there is more than one way to define the greatest common divisor.
We will define it here using the well-ordering principle, but an alternative
definition using Euclid's algorithm is of course just as good, since both
definitions satisfy the specification that uniquely characterizes it.
Hence we make the following specification of the greatest common divisor.

## Definition 8.4.1

Consider three natural numbers `a`, `b`, and `d`.
We say that `d` is a **greatest common divisor** of `a` and `b` if it comes
equipped with an element of type

```text
  is-gcd_(a,b)(d) :=
    Π(x : ℕ) (x | a) × (x | b) ↔ (x | d).
```

The property of being a greatest common divisor uniquely characterizes the
greatest common divisor, in the following sense.

## Proposition 8.4.2

Suppose `d` and `d'` are both a greatest common divisor of `a` and `b`.
Then `d = d'`.

## Proof

If both `d` and `d'` are a greatest common divisor of `a` and `b`, then both
`d` and `d'` divide both `a` and `b`, and hence it follows that `d | d'` and
`d' | d`.
Since the divisibility relation was shown to be a partial order in Exercise 7.2,
it follows by antisymmetry that `d = d'`.

Note that for any two natural numbers `a` and `b`, the type

```text
  Σ(n : ℕ) Π(x : ℕ) (x | a) × (x | b) → (x | n)        (*)
```

consists of all the multiples of the common divisors of `a` and `b`, including
`0`.
On the other hand, the type

```text
  Σ(n : ℕ) Π(x : ℕ) (x | n) → (x | a) × (x | b)        (**)
```

consists of all the common divisors of `a` and `b` except in the case where
`a = 0` and `b = 0`.
In this case, the type in `(**)` consists of all natural numbers.

The two displayed types provide us with two ways to define the greatest common
divisor.
We can either define the greatest common divisor of `a` and `b` as the greatest
natural number in the type in `(**)` or we can define it as the least *nonzero*
natural number of the type in `(*)`, provided that we make an exception in the
case where both `a = 0` and `b = 0`.
Since we already have established the well-ordering principle of `ℕ`, we will
opt for the second approach.
In Exercise 8.10 you will be asked to show that any *bounded* decidable family
over `ℕ` has a maximum as soon as it contains some natural number.

In order to correctly define the greatest common divisor using well-ordering
principle of `ℕ`, we need a slight modification of the type family in `(*)`.
We define this family as follows:

## Definition 8.4.3

Given `a, b : ℕ`, we define the type family `is-multiple-of-gcd(a, b)` over `ℕ`
by

```text
  is-multiple-of-gcd(a, b, n) :=
    (a + b ≠ 0) →
    (n ≠ 0) × (Π(x : ℕ) (x | a) × (x | b) → (x | n)).
```

In other words, if `a + b = 0` then the type
`Σ(n : ℕ) is-multiple-of-gcd(a, b, n)` consists of all the natural numbers.
On the other hand, if `a + b ≠ 0` it consists of the nonzero natural numbers `n`
with the property that any common divisor of `a` and `b` also divides `n`.
These are exactly the nonzero multiples of the greatest common divisor of `a`
and `b`.

Since we intend to apply the well-ordering principle, we must show that the
family `is-multiple-of-gcd(a, b)` is decidable.
This is a step that one can skip in classical mathematics, because all the
subsets of `ℕ` are decidable there.
However, in our current setting we have no choice but to prove it.

## Proposition 8.4.4

The type family `is-multiple-of-gcd(a, b)` is decidable for each `a, b : ℕ`.

## Proof

The type `a + b ≠ 0` is decidable because it is the negation of the type
`a + b = 0`, which is decidable by Proposition 8.1.7.
Therefore it suffices to show that the type

```text
  (n ≠ 0) × Π(x : ℕ) (x | a) × (x | b) → (x | n)
```

is decidable, and by Proposition 8.2.3 we also get to assume that
`a + b ≠ 0`.
The type `n ≠ 0` is again decidable by Proposition 8.1.7, so it suffices to show
that the type

```text
  Π(x : ℕ) (x | a) × (x | b) → (x | n)
```

is decidable.
The types `(x | a) × (x | b)` and `(x | n)` are decidable by Theorem 8.1.9, so
by Corollary 8.2.5 it suffices to check that the family of types
`(x | a) × (x | b)` indexed by `x : ℕ` has an upper bound.
If `x` is a common divisor of `a` and `b`, then it follows that `x` divides
`a + b`.
Furthermore, since we have assumed that `a + b ≠ 0`, it follows that
`x ≤ a + b`.
This provides the upper bound.

We are almost in position to apply the well-ordering principle of `ℕ` to define
the greatest common divisor.
It just remains to show that there is some `n : ℕ` for which
`is-multiple-of-gcd(a, b, n)` holds.
We prove this in the following lemma.

## Lemma 8.4.5

There is an element of type `is-multiple-of-gcd(a, b, a + b)`.

## Proof

To construct an element of type `is-multiple-of-gcd(a, b, a + b)`, assume that
`a + b ≠ 0`.
Then we have tautologically that `a + b ≠ 0`, and any common divisor of `a` and
`b` is also a divisor of `a + b`.

## Definition 8.4.6

We define the **greatest common divisor** `gcd : ℕ → (ℕ → ℕ)` by the
well-ordering principle of `ℕ` as the least natural number `n` for which
`is-multiple-of-gcd(a, b, n)` holds, using the fact that
`is-multiple-of-gcd(a, b)` is a decidable type family and that
`is-multiple-of-gcd(a, b, a + b)` always holds.

## Lemma 8.4.7

For any two natural numbers `a` and `b`, we have `gcd(a, b) = 0` if and only if
`a + b = 0`.

## Proof

To prove the forward direction, assume that `gcd(a, b) = 0`.
By definition of `gcd(a, b)` we have that
`is-multiple-of-gcd(a, b, gcd(a, b))` holds.
More explicitly, the implication

```text
  (a + b ≠ 0) →
  (gcd(a, b) ≠ 0) ×
  Π(x : ℕ) (x | a) × (x | b) → (x | gcd(a, b))
```

holds.
However, we have assumed that `gcd(a, b) = 0`, so it follows from the above
implication that `¬(a + b ≠ 0)`.
In other words, we have `¬ ¬ (a + b = 0)`.
The fact that equality on `ℕ` is decidable implies by Exercise 8.2 that
`¬ ¬ (a + b = 0) → (a + b = 0)`, so we conclude that `a + b = 0`.

For the converse direction, recall that the inequality `gcd(a, b) ≤ a + b`
holds by minimality, since `is-multiple-of-gcd(a, b, a + b)` holds by
Lemma 8.4.5.
If `a + b = 0`, it therefore follows that `gcd(a, b) ≤ 0`, which implies that
`gcd(a, b) = 0`.

## Theorem 8.4.8

For any two natural numbers `a` and `b`, the number `gcd(a, b)` is a greatest
common divisor of `a` and `b` in the sense of Definition 8.4.1.

## Proof

We give the proof by case analysis on whether `a + b = 0`.
If we assume that `a + b = 0`, then it follows that both `a = 0` and `b = 0`,
and by Lemma 8.4.7 it also follows that `gcd(a, b) = 0`.
Since any number divides `0`, the claim follows immediately.

In the case where `a + b ≠ 0`, it follows from Lemma 8.4.7 that also
`gcd(a, b) ≠ 0`.
From the fact that `is-multiple-of-gcd(a, b, gcd(a, b))` we therefore
immediately obtain that

```text
  Π(x : ℕ) (x | a) × (x | b) → (x | gcd(a, b)).
```

Therefore it remains to show that if `x` divides `gcd(a, b)`, then `x` divides
both `a` and `b`.
By transitivity of the divisibility relation it suffices to show that
`gcd(a, b)` divides both `a` and `b`.
We will show only that `gcd(a, b)` divides `a`, the proof that `gcd(a, b)`
divides `b` is similar.

Since `gcd(a, b)` is nonzero, it follows by Euclidean division that there are
numbers `q` and `r < gcd(a, b)` such that

```text
  a = q · gcd(a, b) + r.
```

From this equation and Proposition 7.1.5 it follows that any number `x` which
divides both `a` and `b` also divides `r`, because we have already noted that
any such `x` divides `gcd(a, b)`.
This observation implies that `r = 0`, because we have `r < gcd(a, b)` by
construction and `gcd(a, b)` is minimal.
Therefore we conclude that `gcd(a, b)` divides `a`.
