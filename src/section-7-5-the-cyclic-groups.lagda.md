# Section 7.5 The cyclic groups

```agda
module section-7-5-the-cyclic-groups where
```

We can now define the cyclic groups `ℤ/k` for each `k : ℕ`.
Note that `ℤ/k` must come equipped with the structure of a quotient `ℤ / ≡` of
`ℤ` by the congruence relation modulo `k`.
In the case where `k ≐ 0`, we have that `x ≡ y mod 0` if and only if `x = y`.
This motivates the following definition:

## Definition 7.5.1

We define the type `ℤ/k` for each `k : ℕ` by

```text
  ℤ/0       := ℤ
  ℤ/(k + 1) := Fin(k + 1).
```

Recall from Exercise 5.7 that `ℤ/0` already comes equipped with the structure of
a group, but the group structure on `ℤ/(k + 1)` remains to be defined.

## Definition 7.5.2

We define the **addition** operation on `ℤ/(k + 1)` by

```text
  x + y := [nat-Fin(x) + nat-Fin(y)]_(k + 1),
```

and we define the **additive inverse** operation on `ℤ/(k + 1)` by

```text
  -x := [dist-ℕ(nat-Fin(x), k + 1)]_(k + 1).
```

## Remark 7.5.3

The following congruences modulo `k + 1` follow immediately from
Proposition 7.4.5:

```text
  nat-Fin(0)     ≡ 0
  nat-Fin(x + y) ≡ nat-Fin(x) + nat-Fin(y)
  nat-Fin(-x)    ≡ dist-ℕ(nat-Fin(x), k + 1).
```

Before we show that addition on `ℤ/k` satisfies the group laws, we have to show
that addition on `ℕ` preserves the congruence relation.

## Proposition 7.5.4

Consider `x, y, x', y' : ℕ`.
If any two of the following three properties hold, then so does the third:

1. `x ≡ x' mod k`,
2. `y ≡ y' mod k`,
3. `x + y ≡ x' + y' mod k`.

## Proof

Recall that the distance function `dist-ℕ` is translation invariant by
Exercise 6.5.
Therefore it follows that

```text
  a ≡ b mod k ↔ a + c ≡ b + c mod k.    (*)
```

We will use this observation to prove the claim.

First, suppose that `x ≡ x'` and `y ≡ y'` modulo `k`.
Then it follows by `(*)` that

```text
  x + y ≡ x' + y ≡ x' + y'.
```

This shows that the first and second properties together imply the third.

Next, suppose that `x ≡ x'` and `x + y ≡ x' + y'` modulo `k`.
Then it follows that

```text
  x + y ≡ x' + y' ≡ x + y'.
```

Applying `(*)` once more in the reverse direction, we obtain that `y ≡ y'`
modulo `k`.
This shows that the first and third properties together imply the second.

The remaining claim, that the second and third properties together imply the
first, follows by commutativity of addition from the fact that the first and
third properties together imply the second.

## Theorem 7.5.5

The addition operation on `ℤ/k` satisfies the laws of an abelian group:

```text
  0 + x    = x        x + 0    = x
  (-x) + x = 0        x + (-x) = 0
  (x + y) + z = x + (y + z)
  x + y = y + x.
```

## Proof

The fact that the addition operation on `ℤ/0` satisfies the laws of an abelian
group was stated as Exercise 5.7.
Therefore we will only show that addition on `ℤ/(k + 1)` satisfies the laws of
an abelian group.

We first note that by commutativity of addition on `ℕ`, it follows immediately
that addition on `ℤ/(k + 1)` is commutative.

To prove associativity, note that by Theorem 7.4.7 it suffices to show that

```text
  nat-Fin(x + y) + nat-Fin(z) ≡
  nat-Fin(x) + nat-Fin(y + z) mod k + 1.
```

Since addition on `ℤ/(k + 1)` preserves the congruence relation, and since we
have the congruences

```text
  nat-Fin(x + y) ≡ nat-Fin(x) + nat-Fin(y) mod k + 1
  nat-Fin(y + z) ≡ nat-Fin(y) + nat-Fin(z) mod k + 1,
```

it suffices to show that

```text
  (nat-Fin(x) + nat-Fin(y)) + nat-Fin(z) ≡
  nat-Fin(x) + (nat-Fin(y) + nat-Fin(z)) mod k + 1.
```

This follows immediately by associativity of addition on `ℕ`.

To show that addition on `ℤ/(k + 1)` satisfies the right unit law, we first
observe that it suffices to show that

```text
  [nat-Fin(x) + nat-Fin(0)]_(k + 1) = [nat-Fin(x)]_(k + 1)
```

because there is an identification `[nat-Fin(x)]_(k + 1) = x` by
Theorem 7.4.8.
By Theorem 7.4.7 it now suffices to show that

```text
  nat-Fin(x) + nat-Fin(0) ≡ nat-Fin(x) mod k + 1.
```

This follows immediately from the fact that `nat-Fin(0) = 0`.
The left unit law now follows from the right unit law by commutativity.
We leave the inverse laws as an exercise.
