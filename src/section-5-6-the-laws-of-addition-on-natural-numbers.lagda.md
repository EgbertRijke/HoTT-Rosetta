# Section 5.6 The laws of addition on ℕ

```agda
module section-5-6-the-laws-of-addition-on-natural-numbers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
```

Now that we have introduced the identity type, we can start proving equations.
We will prove here that there are identifications

```text
          0 + n = n                        m + 0 = m
  succ-ℕ(m) + n = succ-ℕ(m + n)    m + succ-ℕ(n) = succ-ℕ(m + n)
    (m + n) + k = m + (n + k)              m + n = n + m.
```

The unit laws, associativity, and commutativity of addition are of course
familiar.
The successor laws will be useful to prove commutativity.
In Exercise 5.5 you will be asked to prove the laws of multiplication on `ℕ`.
There will again be *successor laws* as part of this exercise, because they are
useful intermediate steps in the more complicated laws.

Recall that addition on the natural numbers is defined in such a way that

```text
  m + 0 ≐ m,      m + succ-ℕ(n) ≐ succ-ℕ(m + n).
```

These two judgmental equalities are all we currently know about the function
`m,n ↦ m + n` on `ℕ`.
Consequently, we will have to find ways to apply these two judgmental equalities
in our proofs of the laws of addition.
Of course, the judgmental equalities coincide with two of the six laws.
For the remaining four laws, we will have to proceed by induction on `ℕ`.

## Proposition 5.6.1

For any natural number `n`, there are identifications

```text
   left-unit-law-add-ℕ(n) : 0 + n = n
  right-unit-law-add-ℕ(n) : n + 0 = n.
```

## Proof

We can define

```text
  right-unit-law-add-ℕ(n) ≔  refl,
```

because the computation rule for addition gives us that `n + 0 ≐ n`.

It remains to define the left unit law.
We proceed by induction on `n`.
In the base case we have to show that `0 + 0 = 0`, which holds by reflexivity.
For the inductive step, assume that we have an identification `p : 0 + n = n`.
Our goal is to show that `0 + succ-ℕ(n) = succ-ℕ(n)`.
However, it suffices to construct an identification

```text
  succ-ℕ(0 + n) = succ-ℕ(n),
```

because by the computation rule for addition we have that `0 + succ-ℕ(n) ≐
succ-ℕ(0 + n)`.
Now we use the action on paths of `succ-ℕ : ℕ → ℕ` to obtain

```text
  ap_(succ-ℕ)(p) : succ-ℕ(0 + n) = succ-ℕ(n).
```

The left unit law is therefore defined by

```text
  left-unit-law-add-ℕ(n) ≔ ind-ℕ(refl, λ p. ap_(succ-ℕ)(p)).
```

```agda
right-unit-law-add-ℕ :
  (x : ℕ) → x +ℕ zero-ℕ ＝ x
right-unit-law-add-ℕ x = refl

left-unit-law-add-ℕ :
  (x : ℕ) → zero-ℕ +ℕ x ＝ x
left-unit-law-add-ℕ zero-ℕ = refl
left-unit-law-add-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-add-ℕ x)
```

## Proposition 5.6.2

For any natural numbers `m` and `n`, there are identifications

```text
   left-successor-law-add-ℕ(m,n) : succ-ℕ(m) + n = succ-ℕ(m + n),
  right-successor-law-add-ℕ(m,n) : m + succ-ℕ(n) = succ-ℕ(m + n).
```

## Proof

We can define

```text
  right-successor-law-add-ℕ(m,n) ≔ refl
```

because we have a judgmental equality `m + succ-ℕ(n) ≐ succ-ℕ(m + n)` by
the computation rules for `add-ℕ`.

The left successor law is constructed by induction on `n`.
In the base case we have to construct an identification `succ-ℕ(m) + 0 =
succ-ℕ(m + 0)`, which is obtained by reflexivity.
For the inductive step, assume that we have an identification
`p : succ-ℕ(m) + n = succ-ℕ(m + n)`.
Our goal is to show that

```text
  succ-ℕ(m) + succ-ℕ(n) = succ-ℕ(m + succ-ℕ(n)).
```

Note that we have the judgmental equalities

```text
  succ-ℕ(m) + succ-ℕ(n) ≐ succ-ℕ(succ-ℕ(m) + n) \\
  succ-ℕ(m + succ-ℕ(n)) ≐ succ-ℕ(succ-ℕ(m + n))
```

Therefore it suffices to construct an identification

```text
  succ-ℕ(succ-ℕ(m) + n) = succ-ℕ(succ-ℕ(m + n)).
```

Such an identification is given by `ap_(succ-ℕ)(p)`.

```agda
abstract
  left-successor-law-add-ℕ :
    (x y : ℕ) → (succ-ℕ x) +ℕ y ＝ succ-ℕ (x +ℕ y)
  left-successor-law-add-ℕ x zero-ℕ = refl
  left-successor-law-add-ℕ x (succ-ℕ y) =
    ap succ-ℕ (left-successor-law-add-ℕ x y)

right-successor-law-add-ℕ :
  (x y : ℕ) → x +ℕ (succ-ℕ y) ＝ succ-ℕ (x +ℕ y)
right-successor-law-add-ℕ x y = refl
```

## Proposition 5.6.3

Addition on the natural numbers is associative, i.e., for any three natural
numbers `m`, `n`, and `k`, there is an identification

```text
  associative-add-ℕ(m, n, k) : (m + n) + k = m + (n + k).
```

## Proof

We construct `associative-add-ℕ(m, n, k)` by induction on `k`.
In the base case we have the judgmental equalities

```text
  (m + n) + 0 ≐ m + n ≐ m + (n + 0).
```

Therefore we define `associative-add-ℕ(m, n, 0) ≔  refl`.

For the inductive step, let `p : (m + n) + k = m + (n + k)`. Our goal is to show
that

```text
  (m + n) + succ-ℕ(k) = m + (n + succ-ℕ(k)).
```

Note that we have the judgmental equalities

```text
  (m + n) + succ-ℕ(k) ≐ succ-ℕ((m + n) + k)
  m + (n + succ-ℕ(k)) ≐ m + (succ-ℕ(n + k))
                      ≐ succ-ℕ(m + (n + k))
```

Therefore it suffices to construct an identification

```text
  succ-ℕ((m + n) + k) = succ-ℕ(m + (n + k)),
```

which we have by `ap_(succ-ℕ)(p)`.

```agda
abstract
  associative-add-ℕ :
    (x y z : ℕ) → (x +ℕ y) +ℕ z ＝ x +ℕ (y +ℕ z)
  associative-add-ℕ x y zero-ℕ = refl
  associative-add-ℕ x y (succ-ℕ z) = ap succ-ℕ (associative-add-ℕ x y z)
```

## Proposition 5.6.4

Addition on the natural numbers is commutative, i.e., for any two natural
numbers `m` and `n` there is an identification

```text
  commutative-add-ℕ(m,n) :  m+n=n+m.
```

## Proof

We construct `commutative-add-ℕ(m,n)` by induction on `m`.
In the base case we have to show that `0 + n = n + 0`, which holds by the unit
laws for `n`, proven in Proposition 5.6.1.

For the inductive step, let `p : m + n = n + m`. Our goal is to construct an
identification `succ-ℕ(m) + n = n + succ-ℕ(m)`.
Now it is clear why we first proved the successor laws: we compute

```text
  succ-ℕ(m) + n = succ-ℕ(m + n)
                = succ-ℕ(n + m)
                ≐ n + succ-ℕ(m).
```

The first identification is obtained by Proposition 5.6.2, and the
second identification is the identification `ap_(succ-ℕ)(p)`.

```agda
abstract
  commutative-add-ℕ : (x y : ℕ) → x +ℕ y ＝ y +ℕ x
  commutative-add-ℕ zero-ℕ y = left-unit-law-add-ℕ y
  commutative-add-ℕ (succ-ℕ x) y =
    (left-successor-law-add-ℕ x y) ∙ (ap succ-ℕ (commutative-add-ℕ x y))
```

## Agda-unimath sources

- The proofs of the unit laws, the succesor laws, and both associativity and commutativity of addition are given in `elementary-number-theory.addition-natural-numbers`