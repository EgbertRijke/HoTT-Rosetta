# Section 8.2 Constructions by case analysis

```agda
module section-8-2-constructions-by-case-analysis where
```

A common way to construct functions and to prove properties about them is by
case analysis.
For example, a famous function of Collatz is specified by case analysis on
whether `n` is even or odd:

```text
  collatz(n) =
    n / 2   if n is even
    3n + 1  if n is odd.
```

The Collatz function is of course uniquely determined by this specification,
but it is important to note that there is a bit of work to be done in order to
define the Collatz function according to the rules of dependent type theory.
First we note that, since the Collatz function is specified by case analysis on
whether `n` is even or odd, we will have to use a dependent function witnessing
the fact that every number is either even or odd.
In other words, we will make use of the dependent function

```text
  d : Π(n : ℕ) is-decidable(2 | n),
```

which we have by Theorem 8.1.9.
The type `is-decidable(2 | n)` is the coproduct `(2 | n) + (2 ∤ n)`, so the
idea is to proceed by case analysis on whether `d(n)` is of the form `inl(x)` or
`inr(x)`, i.e., by the induction principle of coproducts.
However, `d(n)` is not a free variable of type `is-decidable(2 | n)`.
Before we can proceed by induction, we must therefore first *generalize* the
element `d(n)` to a free variable `y : is-decidable(2 | n)`.
In other words, we will first define a function

```text
  h : Π(n : ℕ) (is-decidable(2 | n) → ℕ)
```

by the induction principle of coproducts, and then we obtain the Collatz
function by substituting `d(n)` for `y` in `h(n, y)`.
Putting these ideas together, we obtain the following type theoretical
definition of the Collatz function.

## Definition 8.2.1

Write `d : Π(n : ℕ) is-decidable(2 | n)` for the function deciding `2 | n`,
given in Theorem 8.1.9.

1. We define a function `h : Π(n : ℕ) (is-decidable(2 | n) → ℕ)` by

```text
  h(n, inl(m, p)) := m
  h(n, inr(f))    := 3n + 1.
```

2. We define the **collatz function** `collatz : ℕ → ℕ` by

```text
  collatz(n) := h(n, d(n)).
```

## Remark 8.2.2

The general ideas behind the formal construction of the Collatz function lead to
the type theoretic concept of *with-abstraction*.
With-abstraction is a type-theoretically precise generalization of case
analysis.

In full generality, if our goal is to define a dependent function
`f : Π(x : A) C(x)`, and we already have a function `g : Π(x : A) B(x)`, then it
suffices to define a dependent function

```text
  h : Π(x : A) B(x) → C(x).
```

Indeed, given `g` and `h` as above, we can define `f := λ x. h(x, g(x))`.
In other words, to define `f(x)` using `g(x) : B(x)`, we generalize `g(x)` to an
arbitrary element `y : B(x)` and proceed to define an element `h(x, y) : C(x)`.

With-abstraction is a concise way to present such a definition.
In a definition by with-abstraction, we may write

```text
  f(x) with [g(x) / y] := h(x, y),
```

to define a function `f : Π(x : A) C(x)` that satisfies the judgmental equality
`f ≐ λ x. h(x, g(x))`.
In other words, `f(x)` is defined to be `h(x, y)` with `g(x)` for `y`.

The definition of the Collatz function can therefore be given by
with-abstraction as

```text
  collatz(n) with [d(n) / y] := h(x, y).
```

However, recall that the function `h` was defined by pattern matching on `y`.
We can combine with-abstraction and pattern matching to obtain a *direct*
definition of the Collatz function that doesn't explicitly mention the function
`h` anymore.
This gives us the following concise way to define the Collatz function:

```text
  collatz(n) with [d(n) / inl(m, p)] := m
  collatz(n) with [d(n) / inr(f)]    := 3n + 1.
```

Notice that in addition to the information in the specification of the Collatz
function, the definition by with-abstraction also tells us which decision
procedure was used to decide whether `n` is even or not.
The combination of with-abstraction and pattern matching, which allows us to
skip the explicit definition of the function `h`, is what makes
with-abstraction so useful.

Using with-abstraction we can find a slight improvement of the decidability
results of `A → B` and `A × B` in Example 8.1.3, and we will use these improved
claims in the construction of the greatest common divisor.

## Proposition 8.2.3

Consider a decidable type `A`, and let `B` be a type equipped with a function

```text
  A → is-decidable(B).
```

Then the types `A × B` and `A → B` are also decidable.

## Proof

We only prove the claim about the decidability of `A → B`, since the claim about
the decidability of `A × B` is proven similarly.
Since `A` is assumed to be decidable, we proceed by case analysis on `A + ¬ A`.
In the case where we have `f : ¬ A`, we have the composite

```text
  A → ∅ → B.
```

Therefore we obtain the element `inl(ex-falso ∘ f) : is-decidable(A → B)`.
In the case where we have an element `a : A`, we have to construct a function

```text
  d : (A → is-decidable(B)) → is-decidable(A → B).
```

Given `H : A → is-decidable(B)`, we can use with-abstraction to proceed by case
analysis on `H(a) : B + ¬ B`.
The function `d` is therefore defined as

```text
  d(H) with [H(a) / inl(b)] := inl(λ x. b)
  d(H) with [H(a) / inr(g)] := inr(λ h. g(h(a))).
```

For a general family of decidable types `P` over `ℕ`, we cannot prove that the
type

```text
  Π(x : ℕ) P(x)
```

is decidable.
However, if we know in advance that `P(x)` holds for any `m ≤ x`, then we can
decide `Π(x : ℕ) P(x)` by checking the decidability of each `P(x)` until `m`.

## Proposition 8.2.4

Consider a decidable type family `P` over `ℕ` equipped with a natural number `m`
such that the type

```text
  Π(x : ℕ) (m ≤ x) → P(x)
```

is decidable.
Then the type `Π(x : ℕ) P(x)` is decidable.

## Proof

Our proof is by induction on `m`, but we will first make sure that the inductive
hypothesis will be strong enough by quantifying over all decidable type families
over `ℕ`.
Of course, we cannot do this directly.
However, by the assumption that there are enough universes, there is a universe
`𝕌` that contains `P`.
We fix this universe, and we will prove by induction on `m` that for every
decidable type family `Q : ℕ → 𝕌` for which the type

```text
  Π(x : ℕ) (m ≤ x) → Q(x)
```

is decidable, the type `Π(x : ℕ) Q(x)` is again decidable.

In the base case, it follows by assumption that the type `Π(x : ℕ) Q(x)` is
decidable.
For the inductive step, let `Q : ℕ → 𝕌` be a decidable type family for which the
type

```text
  Π(x : ℕ) (m + 1 ≤ x) → Q(x)
```

is decidable.
Since `Q` is assumed to be decidable, we can proceed by case analysis on
`Q(0) + ¬ Q(0)`.
In the case of `¬ Q(0)`, it follows that `¬ Π(x : ℕ) Q(x)`.
In the case where we have `q : Q(0)`, consider the type family `Q' : ℕ → 𝕌`
given by

```text
  Q'(x) := Q(x + 1).
```

Then `Q'` is decidable since `Q` is decidable, and moreover it follows that the
type `Π(x : ℕ) (m ≤ x) → Q'(x)` is decidable.
The inductive hypothesis implies therefore that the type `Π(x : ℕ) Q'(x)` is
decidable.
In the case where `¬ Π(x : ℕ) Q'(x)`, it follows that `¬ Π(x : ℕ) Q(x)`, and in
the case where we have a function `g : Π(x : ℕ) Q'(x)`, we can construct a
function `f : Π(x : ℕ) Q(x)` by

```text
  f(0)     := q
  f(x + 1) := g(x).
```

## Corollary 8.2.5

Consider two decidable families `P` and `Q` over `ℕ`, and suppose that `P` comes
equipped with an upper bound `m`.
Then the type

```text
  Π(n : ℕ) P(n) → Q(n)
```

is decidable.

## Proof

Since `m` is assumed to be an upper bound for `P`, it follows that
`P(n) → Q(n)` for any `m ≤ n`.
With this observation we apply Proposition 8.2.4.
