# Section 13.5 The strong induction principle of the natural numbers

```agda
module section-13-5-the-strong-induction-principle-of-the-natural-numbers where
```

In the final application of the function extensionality principle we prove the
strong induction principle for the type of natural numbers.
Function extensionality is used to derive the computation rules of the strong
induction principle.

## Theorem 13.5.1

Consider a type family `P` over `ℕ` equipped with

```text
  p_0 : P(0)
  p_S : Π(n : ℕ) (Π(m : ℕ) (m ≤ n) → P(m)) → P(n + 1).
```

Then there is a dependent function

```text
  strong-ind-ℕ(p_0, p_S) : Π(n : ℕ) P(n)
```

that satisfies the following computation rules

```text
  strong-ind-ℕ(p_0, p_S, 0) = p_0
  strong-ind-ℕ(p_0, p_S, n + 1) =
    p_S(n, λ m → λ p → strong-ind-ℕ(p_0, p_S, m)).
```

In order to construct `strong-ind-ℕ(p_0, p_S)`, we first define the type family
`P~` over `ℕ` by

```text
  P~(n) := Π(m : ℕ) (m ≤ n) → P(m).
```

The idea is then to first use `p_0` and `p_S` to construct

```text
  p~_0 : P~(0)
  p~_S : Π(n : ℕ) P~(n) → P~(n + 1).
```

The ordinary induction principle of `ℕ` then gives a function

```text
  ind-ℕ(p~_0, p~_S) : Π(n : ℕ) P~(n),
```

which can be used to define a function `Π(n : ℕ) P(n)`.

Before we start by the proof of Theorem 13.5.1 we state two lemmas in which we
construct `p~_0` and `p~_S` with computation rules of their own.
We will assume a type family `P` over `ℕ` equipped with

```text
  p_0 : P(0)
  p_S : Π(n : ℕ) P~(n) → P(n + 1),
```

as in the hypotheses of Theorem 13.5.1.

## Lemma 13.5.2

There is an element `p~_0 : P~(0)` that satisfies the judgmental equality

```text
  p~_0(0, p) ≐ p_0
```

for any `p : 0 ≤ 0`.

## Proof

The fact that we have such a dependent function `p~_0` follows immediately by
induction on `m` and `p : m ≤ 0`.

## Lemma 13.5.3

There is a function

```text
  p~_S : Π(n : ℕ) P~(n) → P~(n + 1)
```

equipped with:

1. An identification

```text
  p~_S(n, H, m, p) = H(m, q)
```

for every `H : P~(n)` and every `p : m ≤ n + 1` and `q : m ≤ n`.

2. An identification

```text
  p~_S(n, H, n + 1, p) = p_S(n, H)
```

for every `p : n + 1 ≤ n + 1`.

## Proof

To define the function `p~_S(n, H)`, note that there is a function

```text
  f : (m ≤ n + 1) → (m ≤ n) + (m = n + 1)       (*)
```

which can be defined by induction on `n` and `m`.
Using the fact that the domain and codomain of this map are both propositions,
this function is easily seen to be an equivalence.
Therefore we define first a function

```text
  h(n, H) : Π(m : ℕ) ((m ≤ n) + (m = n + 1)) → P(m)
```

by case analysis on `x : (m ≤ n) + (m = n + 1)`.
There are two cases to consider: one where we have `q : m ≤ n`, and one where
we have `q : m = n + 1`.
Note that in the second case it suffices to make a definition for `q ≐ refl`.
Therefore we define

```text
  h(n, H, m, x) =
    H(m, q)     if x ≐ inl(q)
    p_S(n, H)   if x ≐ inr(refl).
```

Now we define `p~_S` by

```text
  p~_S(n, H, m, p) := h(n, H, m, f(p)),
```

where `f : (m ≤ n + 1) → (m ≤ n) + (m = n + 1)` is the map we mentioned in
`(*)`.

To construct the identifications claimed in (i) and (ii), note that there is
an equivalence

```text
  (p~_S(n, H, m, p) = y) ≃ (h(n, H, m, x) = y),
```

for any `y : P(m)`.
This equivalence is obtained from the fact that `f(p) = x` for any
`x : (m ≤ n) + (m = n + 1)`, i.e., the fact that
`(m ≤ n) + (m = n + 1)` is a proposition.
Now the identifications in (i) and (ii) are obtained as a simple consequence
of the computation rule for coproducts.

We are now ready to finish the proof of Theorem 13.5.1.

## Proof of Theorem 13.5.1

Using `p~_0` and `p~_S`, we obtain by induction on `n` a function

```text
  s~ : Π(n : ℕ) P~(n)
```

satisfying the computation rules

```text
  s~(0)     ≐ p~_0
  s~(n + 1) ≐ p~_S(n, s~(n)).
```

Now we define

```text
  strong-ind-ℕ(p_0, p_S, n) := s~(n, n, refl-≤-ℕ(n)),
```

where `refl-≤-ℕ(n) : n ≤ n` is the proof of reflexivity of `≤`.

It remains to show that `strong-ind-ℕ` satisfies the computation rules of the
strong induction principle.
The identification that computes `strong-ind-ℕ` at `0` is easy to obtain,
because we have the judgmental equalities

```text
  strong-ind-ℕ(p_0, p_S, 0)
    ≐ s~(0, 0, refl-≤-ℕ(0))
    ≐ p~_0(0, refl-≤-ℕ(0))
    ≐ p_0.
```

To construct the identification that computes `strong-ind-ℕ` at a successor,
we start by a similar computation:

```text
  strong-ind-ℕ(p_0, p_S, n + 1)
    ≐ s~(n + 1, n + 1, refl-≤-ℕ(n + 1))
    ≐ p~_S(n, s~(n), n + 1, refl-≤-ℕ(n + 1))
     = p_S(n, s~(n)).
```

The last identification is obtained from Lemma 13.5.3 (ii).
Therefore we see that, in order to show that

```text
  p_S(n, s~(n)) =
  p_S(n, λ m → λ p → s~(m, m, refl-≤-ℕ(m))),
```

we need to prove that

```text
  s~(n) = λ m → λ p → s~(m, m, refl-≤-ℕ(m)).
```

Here we apply function extensionality, so it suffices to show that

```text
  s~(n, m, p) = s~(m, m, refl-≤-ℕ(m))
```

for every `m : ℕ` and `p : m ≤ n`.
We proceed by induction on `n : ℕ`.
The base case is trivial.
For the inductive step, we note that

```text
  s~(n + 1, m, p) = p~_S(n, s~(n), m, p)
                  = s~(n, m, p)  if m ≤ n
                  = p_S(n, s~(n)) if m = n + 1.
```

Therefore it follows by the inductive hypothesis that

```text
  s~(n + 1, m, p) = s~(m, m, refl-≤-ℕ(m))
```

if `m ≤ n` holds.
In the remaining case, where `m = n + 1`, note that we have

```text
  s~(n + 1, n + 1, refl-≤-ℕ(n + 1))
    = p~_S(n, s~(n), n + 1, refl-≤-ℕ(n + 1))
    = p_S(n, s~(n)).
```

Therefore we see that we also have an identification

```text
  s~(n + 1, m, p) = s~(m, m, refl-≤-ℕ(m))
```

when `m = n + 1`.
This completes the proof of the computation rules for the strong induction
principle of `ℕ`.
