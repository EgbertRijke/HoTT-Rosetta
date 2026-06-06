# Section 7.4 The natural numbers modulo k + 1

```agda
module section-7-4-the-natural-numbers-modulo-k-plus-one where
```

Given an equivalence relation `~` on a set `A` in classical mathematics, the
quotient `A / ~` comes equipped with a quotient map `q : A → A / ~` that
satisfies two important properties.
First, the map `q` satisfies the condition

```text
  q(x) = q(y) ↔ x ~ y,
```

and second, the map `q` is surjective.
The first condition is called the **effectiveness** of the quotient map.

In classical mathematics, a map `f : A → B` is said to be surjective if for
every `b ∈ B` there exists an element `a ∈ A` such that `f(a) = b`.
Following the Curry-Howard interpretation, a map `f : A → B` is therefore
surjective if it comes equipped with a dependent function

```text
  Π(b : B) Σ(a : A) f(a) = b.
```

However, there is a subtle issue with this interpretation of surjectivity.
It is somewhat stronger than the classical notion of surjectivity, because a
dependent function `Π(b : B) Σ(a : A) f(a) = b` provides for every element
`b : B` an *explicit* element `a : A` equipped with an explicit identification
`p : f(a) = b`, whereas in the classical notion of surjectivity such an element
`a ∈ A` is merely asserted to exist.
To emphasize that the Curry-Howard interpretation of surjectivity is stronger
than intended we make the following definition, and we will properly introduce
surjective maps later.

## Definition 7.4.1

Consider a function `f : A → B`.
We say that `f` is **split surjective** if it comes equipped with an element of
type

```text
  is-split-surjective(f) := Π(b : B) Σ(a : A) f(a) = b.
```

Martin-Löf's dependent type theory doesn't have a general way of forming
quotients of types.
However, in the specific case of the congruence relations on `ℕ` we can define
the type of natural numbers modulo `k + 1` as the standard finite type
`Fin(k + 1)`.
We will show that `Fin(k + 1)` comes equipped with a map

```text
  [_]_(k + 1) : ℕ → Fin(k + 1)
```

for each `k : ℕ`, and we will show that this map is effective and split
surjective.

To prepare for the definition of the quotient map `[_]_(k + 1)`, we will first
define a zero element of `Fin(k + 1)` and successor function on each `Fin(k)`.
We will also define an auxiliary function
`skip-zero-Fin_k : Fin(k) → Fin(k + 1)`, which is used in the definition of the
successor function.
The map `[_]_(k + 1)` is then defined by iterating the successor function.

## Definition 7.4.2

We define the following objects:

1. We define the **zero element** `zero-Fin_k : Fin(k + 1)` recursively by

```text
  zero-Fin_0       := ⋆
  zero-Fin_(k + 1) := i(zero-Fin_k).
```

Since there is a mismatch between the index of `zero-Fin_k` and the index of
its type, we will often simply write `zero-Fin` or `0` for the zero element of
`Fin(k + 1)`.

2. We define the function `skip-zero-Fin_k : Fin(k) → Fin(k + 1)` recursively by

```text
  skip-zero-Fin_(k + 1)(i(x)) := i(skip-zero-Fin_k(x))
  skip-zero-Fin_(k + 1)(⋆)    := ⋆.
```

3. We define the **successor function** `succ-Fin_k : Fin(k) → Fin(k)`
recursively by

```text
  succ-Fin_(k + 1)(i(x)) := skip-zero-Fin_k(x)
  succ-Fin_(k + 1)(⋆)    := zero-Fin_k.
```

## Definition 7.4.3

For any `k : ℕ`, we define the map `[_]_(k + 1) : ℕ → Fin(k + 1)` recursively
on `x` by

```text
  [0]_(k + 1)     := 0
  [x + 1]_(k + 1) := succ-Fin_(k + 1)([x]_(k + 1)).
```

Our next intermediate goal is to show that
`x ≡ nat-Fin([x]_(k + 1)) mod k + 1` for any natural number `x`.
This fact is a consequence of the following simple lemma, that will help us
compute with the maps `nat-Fin : Fin(k) → ℕ`.

## Lemma 7.4.4

We make three claims:

1. For any `k : ℕ` there is an identification

```text
  nat-Fin(zero-Fin_k) = 0.
```

2. For any `k : ℕ` and any `x : Fin(k)`, we have

```text
  nat-Fin(skip-zero-Fin_k(x)) = nat-Fin(x) + 1.
```

3. For any `k : ℕ` and any `x : Fin(k)`, we have

```text
  nat-Fin(succ-Fin_k(x)) ≡ nat-Fin(x) + 1 mod k.
```

## Proof

For the first claim, we define an identification
`α_k : nat-Fin(zero-Fin_k) = 0` recursively by

```text
  α_0       := refl
  α_(k + 1) := α_k.
```

For the second claim, we define an identification
`β_k(x) : nat-Fin(skip-zero-Fin_k(x)) = nat-Fin(x) + 1` recursively by

```text
  β_(k + 1)(i(x)) := β_k(x)
  β_(k + 1)(⋆)    := refl.
```

For the third claim, we again define an element
`γ_k(x) : nat-Fin(succ-Fin_k(x)) ≡ nat-Fin(x) + 1 mod k` recursively.
To obtain the case for `i(x)`, we calculate

```text
  nat-Fin(succ-Fin_(k + 1)(i(x))) ≐ nat-Fin(skip-zero-Fin(x))
                                      = nat-Fin(x) + 1.
```

Since the congruence relation modulo `k + 1` is reflexive, we obtain
`γ_(k + 1)(i(x))` from the identification of the above calculation.
To obtain the case for `⋆`, we calculate

```text
  nat-Fin(succ-Fin_(k + 1)(⋆)) ≐ nat-Fin(0)
                                  = 0
                                  ≡ k + 1
                                  ≐ nat-Fin(⋆) + 1.
```

## Proposition 7.4.5

For any `x : ℕ` we have

```text
  nat-Fin([x]_(k + 1)) ≡ x mod k + 1.
```

## Proof

The proof is by induction on `x`.
The fact that

```text
  nat-Fin([0]_(k + 1)) ≡ 0 mod k + 1
```

is immediate from the fact that
`nat-Fin([0]_(k + 1)) ≐ nat-Fin(0) = 0`, which was shown in Lemma 7.4.4.
In the inductive step, we have to show that

```text
  nat-Fin([x + 1]_(k + 1)) ≡ x + 1 mod k + 1.
```

This follows from the computation

```text
  nat-Fin([x + 1]_(k + 1))
    ≐ nat-Fin(succ-Fin_(k + 1)([x]_(k + 1)))
    ≡ nat-Fin([x]_(k + 1)) + 1
    ≡ x + 1.
```

We need one more fact before we can prove effectiveness and split surjectivity.

## Proposition 7.4.6

For any natural number `x < d` we have

```text
  d | x ↔ x = 0.
```

Consequently, for any two natural numbers `x` and `y` such that
`dist-ℕ(x, y) < k`, we have

```text
  x ≡ y mod k ↔ x = y.
```

## Proof

Note that the implication `x = 0 → d | x` is trivial, so it suffices to prove
the forward implication

```text
  d | x → x = 0.
```

This implication clearly holds if `x ≐ 0`.
Therefore we only have to show that `d | x + 1` implies `x + 1 = 0`, if we
assume that `x + 1 < d`.
In other words, we will derive a contradiction from the hypotheses that
`x + 1 < d` and `d | x + 1`.
To reach a contradiction we use Exercise 6.4, by which it suffices to show that
`d ≤ x + 1`.

We proceed by `Σ`-induction on the unnamed variable of type `d | x + 1`, so we
get to assume a natural number `k` equipped with an identification
`p : dk = x + 1`.
In the case where `k ≐ 0` we reach an immediate contradiction by Theorem 6.4.2,
because we obtain that `0 = d · 0 = x + 1`.
In the case where `k ≐ succ(k')` it follows that

```text
  d ≤ dk' + d ≐ dk = x + 1.
```

## Theorem 7.4.7

Consider a natural number `k`.
Then we have

```text
  [x]_(k + 1) = [y]_(k + 1) ↔ x ≡ y mod k + 1,
```

for any `x, y : ℕ`.

## Proof

First note that, since `nat-Fin` is injective by Proposition 7.3.6, we have

```text
  [x]_(k + 1) = [y]_(k + 1)
    ↔ nat-Fin([x]_(k + 1)) = nat-Fin([y]_(k + 1)).
```

Since the inequalities `nat-Fin([x]_(k + 1)) < k + 1` and
`nat-Fin([y]_(k + 1)) < k + 1` hold by Lemma 7.3.5, it follows by
Proposition 7.4.6 that

```text
  nat-Fin([x]_(k + 1)) = nat-Fin([y]_(k + 1))
    ↔ nat-Fin([x]_(k + 1)) ≡ nat-Fin([y]_(k + 1)) mod k + 1.
```

The latter condition is by Proposition 7.4.5 equivalent to the condition that
`x ≡ y mod k + 1`.

## Theorem 7.4.8

For any `x : Fin(k + 1)` there is an identification

```text
  [nat-Fin(x)]_(k + 1) = x.
```

In other words, the map `[_]_(k + 1) : ℕ → Fin(k + 1)` is split surjective.

## Proof

Since `nat-Fin : Fin(k + 1) → ℕ` is injective by Proposition 7.3.6, it suffices
to show that

```text
  nat-Fin([nat-Fin(x)]_(k + 1)) = nat-Fin(x).
```

Now observe that `nat-Fin([nat-Fin(x)]_(k + 1)) < k + 1` and
`nat-Fin(x) < k + 1`.
By Proposition 7.4.6 it therefore suffices to show that

```text
  nat-Fin([nat-Fin(x)]_(k + 1)) ≡ nat-Fin(x) mod k + 1.
```

This fact is an instance of Proposition 7.4.5.
