# Section 8.4 The greatest common divisor

```agda
module section-8-4-the-greatest-common-divisor where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
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
open import exercise-7-9-euclidean-division
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
open import section-8-3-the-well-ordering-principle-of-natural-numbers
open import exercise-4-3-negation
open import section-5-2-the-groupoidal-structure-of-types
open import exercise-7-10-k-ary-natural-numbers
```

<!-- rosetta-item: section-8.4 -->

The greatest common divisor of two natural numbers `a` and `b` is a natural number `gcd(a,b)` that satisfies the property that
```text
x| a\ and\ x| b if and only if x|gcd(a,b)
```
for any `x:ℕ`.
In other words, any number `x:ℕ` that divides both `a` and `b` also divides the greatest common divisor.
Moreover, since `gcd(a,b)` divides itself, it follows from the reverse implication that `gcd(a,b)` divides both `a` and `b`.

This property can also be seen as the *specification* of what it means to be a greatest common divisor of `a` and `b`.
In formal developments of mathematics, when you’re about to construct an object that satisfies a certain specification, it can be useful to start out with that specification.
For example, there is more than one way to define the greatest common divisor.
We will define it here in Definition 8.4.6 using the well-ordering principle, but an alternative definition using Euclid’s algorithm is of course just as good, since both definitions satisfy the specification that uniquely characterizes it.
Hence we make the following specification of the greatest common divisor.

## Definition 8.4.1

<!-- rosetta-item: definition-8.4.1; latex-label: defn:is-gcd -->

Consider three natural numbers `a`, `b`, and `d`.
We say that `d` is a **greatest common divisor** of `a` and `b` if it comes equipped with an element of type
```text
is-gcd_{a,b}(d) ≔ Π(x:ℕ) (x| a)× (x| b)↔ (x| d).
```

<!-- rosetta-agda-block: definition-8.4.1-common-divisor -->

```agda
is-common-divisor-ℕ : (a b x : ℕ) → Type lzero
is-common-divisor-ℕ a b x = (div-ℕ x a) × (div-ℕ x b)
```

<!-- rosetta-agda-block: definition-8.4.1-greatest-common-divisor -->

```agda
is-gcd-ℕ : (a b d : ℕ) → Type lzero
is-gcd-ℕ a b d = (x : ℕ) → (is-common-divisor-ℕ a b x) ↔ (div-ℕ x d)
```
<!-- rosetta-item-end: definition-8.4.1 -->

The property of being a greatest common divisor uniquely characterizes the greatest common divisor, in the following sense.

## Proposition 8.4.2

<!-- rosetta-item: proposition-8.4.2 -->

Suppose `d` and `d'` are both a greatest common divisor of `a` and `b`.
Then `d=d'`.

### Proof

<!-- rosetta-item: subheading-8.4-proof -->

*Proof.* If both `d` and `d'` are a greatest common divisor of `a` and `b`, then both `d` and `d'` divide both `a` and `b`, and hence it follows that `d| d'` and `d'| d`.
Since the divisibility relation was shown to be a partial order in Exercise 7.2, it follows by antisymmetry that `d=d'`. ◻

<!-- rosetta-agda-block: proposition-8.4.2-common-divisor-gcd -->

```agda
abstract
  refl-is-common-divisor-ℕ :
    (x : ℕ) → is-common-divisor-ℕ x x x
  pr1 (refl-is-common-divisor-ℕ x) = refl-div-ℕ x
  pr2 (refl-is-common-divisor-ℕ x) = refl-div-ℕ x
```

<!-- rosetta-agda-block: proposition-8.4.2-uniqueness-gcd -->

```agda
abstract
  is-common-divisor-is-gcd-ℕ :
    (a b d : ℕ) → is-gcd-ℕ a b d → is-common-divisor-ℕ a b d
  is-common-divisor-is-gcd-ℕ a b d H = pr2 (H d) (refl-div-ℕ d)

abstract
  uniqueness-is-gcd-ℕ :
    (a b d d' : ℕ) → is-gcd-ℕ a b d → is-gcd-ℕ a b d' → d ＝ d'
  uniqueness-is-gcd-ℕ a b d d' H H' =
    antisymmetric-div-ℕ d d'
      ( pr1 (H' d) (is-common-divisor-is-gcd-ℕ a b d H))
      ( pr1 (H d') (is-common-divisor-is-gcd-ℕ a b d' H'))
```
<!-- rosetta-item-end: proposition-8.4.2 -->

Note that for any two natural numbers `a` and `b`, the type
```text
Σ(n:ℕ) Π(x:ℕ) (x| a)× (x| b)→ (x| n)(*)
```
consists of all the multiples of the common divisors of `a` and `b`, including `0`.
On the other hand, the type
```text
Σ(n:ℕ) Π(x:ℕ) (x| n)→ (x| a)× (x| b)(**)
```
consists of all the common divisors of `a` and `b` except in the case where `a=0` and `b=0`.
In this case, the type in (\*\*) consists of all natural numbers.

The two displayed types provide us with two ways to define the greatest common divisor.
We can either define the greatest common divisor of `a` and `b` as the greatest natural number in the type in (\*\*) or we can define it as the least *nonzero* natural number of the type in (\*), provided that we make an exception in the case where both `a=0` and `b=0`.
Since we already have established the well-ordering principle of `ℕ`, we will opt for the second approach.
In Exercise 8.10 you will be asked to show that any *bounded* decidable family over `ℕ` has a maximum as soon as it contains some natural number.

In order to correctly define the greatest common divisor using well-ordering principle of `ℕ`, we need a slight modification of the type family in (\*).
We define this family as follows:

## Definition 8.4.3

<!-- rosetta-item: definition-8.4.3; latex-label: defn:fam-gcd -->

Given `a,b:ℕ`, we define the type family `M(a,b)` over `ℕ` by
```text
M(a,b,n) ≔ (a+b≠ 0) → (n≠ 0)× (Π(x:ℕ) (x| a)× (x| b) → (x| n)).
```

<!-- rosetta-agda-block: definition-8.4.3-multiple-gcd -->

```agda
is-multiple-of-gcd-ℕ : (a b n : ℕ) → Type lzero
is-multiple-of-gcd-ℕ a b n =
  is-nonzero-ℕ (a +ℕ b) →
  (is-nonzero-ℕ n) × ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x n)
```
<!-- rosetta-item-end: definition-8.4.3 -->

In other words, if `a+b=0` then the type `Σ(n:ℕ) M(a,b,n)` consist of all the natural numbers.
On the other hand, if `a+b≠ 0` it consists of the nonzero natural numbers `n` with the property that any common divisor of `a` and `b` also divides `n`.
These are exactly the nonzero multiples of the greatest common divisor of `a` and `b`.

Since we intend to apply the well-ordering principle, we must show that the family `M(a,b)` is decidable.
This is a step that one can skip in classical mathematics, because all the subsets of `ℕ` are decidable there.
However, in our current setting we have no choice but to prove it.

## Proposition 8.4.4

<!-- rosetta-item: proposition-8.4.4; latex-label: prp:is-decidable-is-multiple-of-gcd -->

The type family `M(a,b)` is decidable for each `a,b:ℕ`.

### Proof

<!-- rosetta-item: subheading-8.4-proof-2 -->

*Proof.* The type `a+b≠ 0` is decidable because it is the negation of the type `a+b=0`, which is decidable by Proposition 8.1.7.
Therefore it suffices to show that the type
```text
(n≠ 0)× Π(x:ℕ) (x| a)× (x| b)→ (x| n)
```
is decidable, and by Proposition 8.2.3 we also get to assume that `a+b≠ 0`.
The type `n≠ 0` is again decidable by Proposition 8.1.7, so it suffices to show that the type
```text
Π(x:ℕ) (x| a)× (x| b)→ (x| n)
```
is decidable.
The types `(x| a)×(x| b)` and `(x| n)` are decidable by Theorem 8.1.9, so by Corollary 8.2.5 it suffices to check that the family of types `(x| a)× (x| b)` indexed by `x:ℕ` has an upper bound.
If `x` is a common divisor of `a` and `b`, then it follows that `x` divides `a+b`.
Furthermore, since we have assumed that `a+b≠ 0`, it follows that `x≤ a+b`.
This provides the upper bound. ◻

<!-- rosetta-agda-block: proposition-8.4.4-common-divisor-decidable -->

```agda
abstract
  is-decidable-is-common-divisor-ℕ :
    (a b : ℕ) → is-decidable-family (is-common-divisor-ℕ a b)
  is-decidable-is-common-divisor-ℕ a b x =
    is-decidable-product
      ( is-decidable-div-ℕ x a)
      ( is-decidable-div-ℕ x b)
```

<!-- rosetta-agda-block: proposition-8.4.4-divisor-successor-bound -->

```agda
abstract
  leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
  leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
    concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p
```

<!-- rosetta-agda-block: proposition-8.4.4-common-divisor-bound -->

```agda
abstract
  leq-sum-is-common-divisor-ℕ' :
    (a b d : ℕ) →
    is-successor-ℕ (a +ℕ b) → is-common-divisor-ℕ a b d → leq-ℕ d (a +ℕ b)
  leq-sum-is-common-divisor-ℕ' a zero-ℕ d (pair k p) H =
    concatenate-leq-eq-ℕ d
      ( leq-div-succ-ℕ d k (concatenate-div-eq-ℕ (pr1 H) p))
      ( inv p)
  leq-sum-is-common-divisor-ℕ' a (succ-ℕ b) d (pair k p) H =
    leq-div-succ-ℕ d (a +ℕ b) (div-add-ℕ d a (succ-ℕ b) (pr1 H) (pr2 H))

  leq-sum-is-common-divisor-ℕ :
    (a b d : ℕ) →
    is-nonzero-ℕ (a +ℕ b) → is-common-divisor-ℕ a b d → leq-ℕ d (a +ℕ b)
  leq-sum-is-common-divisor-ℕ a b d H =
    leq-sum-is-common-divisor-ℕ' a b d (is-successor-is-nonzero-ℕ H)
```

<!-- rosetta-agda-block: proposition-8.4.4-multiple-gcd-decidable -->

```agda
abstract
  is-decidable-is-multiple-of-gcd-ℕ :
    (a b : ℕ) → is-decidable-family (is-multiple-of-gcd-ℕ a b)
  is-decidable-is-multiple-of-gcd-ℕ a b n =
    is-decidable-function-type'
      ( is-decidable-neg (is-decidable-is-zero-ℕ (a +ℕ b)))
      ( λ np →
        is-decidable-product
          ( is-decidable-neg (is-decidable-is-zero-ℕ n))
          ( is-decidable-bounded-Π-ℕ
            ( is-common-divisor-ℕ a b)
            ( λ x → div-ℕ x n)
            ( is-decidable-is-common-divisor-ℕ a b)
            ( λ x → is-decidable-div-ℕ x n)
            ( a +ℕ b)
            ( λ x → leq-sum-is-common-divisor-ℕ a b x np)))
```
<!-- rosetta-item-end: proposition-8.4.4 -->

We are almost in position to apply the well-ordering principle of `ℕ` to define the greatest common divisor.
It just remains to show that there is some `n:ℕ` for which `M(a,b,n)` holds.
We prove this in the following lemma.

## Lemma 8.4.5

<!-- rosetta-item: lemma-8.4.5; latex-label: lem:exists-multiple-of-gcd -->

There is an element of type `M(a,b,a+b)`.

### Proof

<!-- rosetta-item: subheading-8.4-proof-3 -->

*Proof.* To construct an element of type `M(a,b,a+b)`, assume that `a+b≠ 0`.
Then we have tautologically that `a+b≠ 0`, and any common divisor of `a` and `b` is also a divisor of `a+b`. ◻

<!-- rosetta-agda-block: lemma-8.4.5-sum-multiple-gcd -->

```agda
abstract
  sum-is-multiple-of-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (a +ℕ b)
  pr1 (sum-is-multiple-of-gcd-ℕ a b np) = np
  pr2 (sum-is-multiple-of-gcd-ℕ a b np) x H = div-add-ℕ x a b (pr1 H) (pr2 H)
```
<!-- rosetta-item-end: lemma-8.4.5 -->

## Definition 8.4.6

<!-- rosetta-item: definition-8.4.6; latex-label: defn:gcd -->

We define the **greatest common divisor** `gcd:ℕ→ (ℕ→ℕ)` by the well-ordering principle of `ℕ` (Theorem 8.3.2) as the least natural number `n` for which `M(a,b,n)` holds, using the fact that `M(a,b)` is a decidable type family (Proposition 8.4.4) and that `M(a,b,a+b)` always holds (Lemma 8.4.5).

<!-- rosetta-agda-block: definition-8.4.6-gcd -->

```agda
abstract
  GCD-ℕ : (a b : ℕ) → minimal-element-ℕ (is-multiple-of-gcd-ℕ a b)
  GCD-ℕ a b =
    well-ordering-principle-ℕ
      ( is-multiple-of-gcd-ℕ a b)
      ( is-decidable-is-multiple-of-gcd-ℕ a b)
      ( pair (a +ℕ b) (sum-is-multiple-of-gcd-ℕ a b))

gcd-ℕ : ℕ → ℕ → ℕ
gcd-ℕ a b = pr1 (GCD-ℕ a b)

is-multiple-of-gcd-gcd-ℕ : (a b : ℕ) → is-multiple-of-gcd-ℕ a b (gcd-ℕ a b)
is-multiple-of-gcd-gcd-ℕ a b = pr1 (pr2 (GCD-ℕ a b))

is-lower-bound-gcd-ℕ :
  (a b : ℕ) → is-lower-bound-ℕ (is-multiple-of-gcd-ℕ a b) (gcd-ℕ a b)
is-lower-bound-gcd-ℕ a b = pr2 (pr2 (GCD-ℕ a b))
```
<!-- rosetta-item-end: definition-8.4.6 -->

## Lemma 8.4.7

<!-- rosetta-item: lemma-8.4.7; latex-label: lem:is-zero-gcd -->

For any two natural numbers `a` and `b`, we have `gcd(a,b)=0` if and only if `a+b=0`.

### Proof

<!-- rosetta-item: subheading-8.4-proof-4 -->

*Proof.* To prove the forward direction, assume that `gcd(a,b)=0`.
By definition of `gcd(a,b)` we have that `M(a,b,gcd(a,b))` holds.
More explicitly, the implication
```text
(a+b≠ 0)→ (gcd(a,b)≠ 0)× Π(x:ℕ) (x| a)×(x| b)→ (x|gcd(a,b))
```
holds.
However, we have assumed that `gcd(a,b)=0`, so it follows from the above implication that `¬(a+b≠ 0)`.
In other words, we have `¬¬(a+b=0)`.
The fact that equality on `ℕ` is decidable implies via Exercise 4.3 that `¬¬(a+b=0)→ (a+b=0)`, so we conclude that `a+b=0`.

For the converse direction, recall that the inequality `gcd(a,b)≤ a+b` holds by minimality, since `M(a,b,a+b)` holds by Lemma 8.4.5.
If `a+b=0`, it therefore follows that `gcd(a,b)≤ 0`, which implies that `gcd(a,b)=0`. ◻

<!-- rosetta-agda-block: lemma-8.4.7-double-negation-elimination -->

```agda
double-negation-elim-is-decidable :
  {l : Level} {P : Type l} → is-decidable P → (¬¬ P → P)
double-negation-elim-is-decidable (inl x) p = x
double-negation-elim-is-decidable (inr x) p = ex-falso (p x)
```

<!-- rosetta-agda-block: lemma-8.4.7-zero-gcd -->

```agda
abstract
  is-zero-gcd-ℕ :
    (a b : ℕ) → is-zero-ℕ (a +ℕ b) → is-zero-ℕ (gcd-ℕ a b)
  is-zero-gcd-ℕ a b p =
    is-zero-leq-zero-ℕ
      ( gcd-ℕ a b)
      ( concatenate-leq-eq-ℕ
        ( gcd-ℕ a b)
        ( is-lower-bound-gcd-ℕ a b
          ( a +ℕ b)
          ( sum-is-multiple-of-gcd-ℕ a b))
        ( p))

  is-zero-gcd-zero-zero-ℕ : is-zero-ℕ (gcd-ℕ zero-ℕ zero-ℕ)
  is-zero-gcd-zero-zero-ℕ = is-zero-gcd-ℕ zero-ℕ zero-ℕ refl

  is-zero-add-is-zero-gcd-ℕ :
    (a b : ℕ) → is-zero-ℕ (gcd-ℕ a b) → is-zero-ℕ (a +ℕ b)
  is-zero-add-is-zero-gcd-ℕ a b H =
    double-negation-elim-is-decidable
      ( is-decidable-is-zero-ℕ (a +ℕ b))
      ( λ f → pr1 (is-multiple-of-gcd-gcd-ℕ a b f) H)
```
<!-- rosetta-item-end: lemma-8.4.7 -->

## Theorem 8.4.8

<!-- rosetta-item: theorem-8.4.8 -->

For any two natural numbers `a` and `b`, the number `gcd(a,b)` is a greatest common divisor of `a` and `b` in the sense of Definition 8.4.1.

### Proof

<!-- rosetta-item: subheading-8.4-proof-5 -->

*Proof.* We give the proof by case analysis on whether `a+b=0`.
If we assume that `a+b=0`, then it follows that both `a=0` and `b=0`, and by Lemma 8.4.7 it also follows that `gcd(a,b)=0`.
Since any number divides `0`, the claim follows immediately.

In the case where `a+b≠ 0`, it follows from Lemma 8.4.7 that also `gcd(a,b)≠ 0`.
From the fact that `M(a,b,gcd(a,b))` we therefore immediately obtain that
```text
Π(x:ℕ) (x| a)× (x| b)→ (x| gcd(a,b)).
```
Therefore it remains to show that if `x` divides `gcd(a,b)`, then `x` divides both `a` and `b`.
By transitivity of the divisibility relation it suffices to show that `gcd(a,b)` divides both `a` and `b`.
We will show only that `gcd(a,b)` divides `a`, the proof that `gcd(a,b)` divides `b` is similar.

Since `gcd(a,b)` is nonzero, it follows by Euclidean division (Exercise 7.9) that there are numbers `q` and `r<gcd(a,b)` such that
```text
a = q·gcd(a,b)+r.
```
From this equation and Proposition 7.1.5 it follows that any number `x` which divides both `a` and `b` also divides `r`, because we have already noted that any such `x` divides `gcd(a,b)`.
This observation implies that `r=0`, because we have `r<gcd(a,b)` by construction and `gcd(a,b)` is minimal.
Therefore we conclude that `gcd(a,b)` divides `a`. ◻

<!-- rosetta-agda-block: theorem-8.4.8-nonzero-and-common-divisor -->

```agda
abstract
  is-nonzero-gcd-ℕ :
    (a b : ℕ) → is-nonzero-ℕ (a +ℕ b) → is-nonzero-ℕ (gcd-ℕ a b)
  is-nonzero-gcd-ℕ a b ne = pr1 (is-multiple-of-gcd-gcd-ℕ a b ne)

  is-successor-gcd-ℕ :
    (a b : ℕ) → is-nonzero-ℕ (a +ℕ b) → is-successor-ℕ (gcd-ℕ a b)
  is-successor-gcd-ℕ a b ne =
    is-successor-is-nonzero-ℕ (is-nonzero-gcd-ℕ a b ne)

div-gcd-is-common-divisor-ℕ :
  (a b x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x (gcd-ℕ a b)
div-gcd-is-common-divisor-ℕ a b x H with
  is-decidable-is-zero-ℕ (a +ℕ b)
... | inl p = concatenate-div-eq-ℕ (div-zero-ℕ x) (inv (is-zero-gcd-ℕ a b p))
... | inr np = pr2 (is-multiple-of-gcd-gcd-ℕ a b np) x H
```

<!-- rosetta-agda-block: theorem-8.4.8-divisor-multiple -->

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (k *ℕ y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (k *ℕ y) (pair k refl) H
```

<!-- rosetta-agda-block: theorem-8.4.8-small-common-multiple-zero -->

```agda
abstract
  is-zero-is-common-divisor-le-gcd-ℕ :
    (a b r : ℕ) → le-ℕ r (gcd-ℕ a b) →
    ((x : ℕ) → is-common-divisor-ℕ a b x → div-ℕ x r) → is-zero-ℕ r
  is-zero-is-common-divisor-le-gcd-ℕ a b r l d with is-decidable-is-zero-ℕ r
  ... | inl H = H
  ... | inr x =
    ex-falso
      ( contradiction-le-ℕ r (gcd-ℕ a b) l
        ( is-lower-bound-gcd-ℕ a b r (λ np → pair x d)))
```

<!-- rosetta-agda-block: theorem-8.4.8-divisor-gcd-common-divisor -->

```agda
opaque
  div-left-factor-div-gcd-ℕ :
    (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x a
  div-left-factor-div-gcd-ℕ a b x d with
    is-decidable-is-zero-ℕ (a +ℕ b)
  ... | inl p =
    concatenate-div-eq-ℕ (div-zero-ℕ x) (inv (is-zero-left-is-zero-add-ℕ a b p))
  ... | inr np =
    transitive-div-ℕ x (gcd-ℕ a b) a
      ( pair q
        ( ( ( α) ∙
            ( ap
              ( dist-ℕ a)
              ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                ( λ x H →
                  div-right-summand-ℕ x (q *ℕ (gcd-ℕ a b)) r
                    ( div-mul-ℕ q x (gcd-ℕ a b)
                      ( div-gcd-is-common-divisor-ℕ a b x H))
                    ( concatenate-div-eq-ℕ (pr1 H) (inv β)))))) ∙
          ( right-unit-law-dist-ℕ a)))
      ( d)
    where
    r : ℕ
    r = remainder-euclidean-division-ℕ (gcd-ℕ a b) a
    q : ℕ
    q = quotient-euclidean-division-ℕ (gcd-ℕ a b) a
    α : (q *ℕ gcd-ℕ a b) ＝ dist-ℕ a r
    α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) a
    B : le-ℕ r (gcd-ℕ a b)
    B =
      strict-upper-bound-remainder-euclidean-division-ℕ
        (gcd-ℕ a b) a (is-nonzero-gcd-ℕ a b np)
    β : q *ℕ gcd-ℕ a b +ℕ r ＝ a
    β = eq-euclidean-division-ℕ (gcd-ℕ a b) a

  div-right-factor-div-gcd-ℕ :
    (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → div-ℕ x b
  div-right-factor-div-gcd-ℕ a b x d with
    is-decidable-is-zero-ℕ (a +ℕ b)
  ... | inl p =
    concatenate-div-eq-ℕ
      ( div-zero-ℕ x)
      ( inv (is-zero-right-is-zero-add-ℕ a b p))
  ... | inr np =
    transitive-div-ℕ x (gcd-ℕ a b) b
      ( pair q
        ( ( α ∙
            ( ap
              ( dist-ℕ b)
              ( is-zero-is-common-divisor-le-gcd-ℕ a b r B
                ( λ x H →
                  div-right-summand-ℕ x (q *ℕ (gcd-ℕ a b)) r
                    ( div-mul-ℕ q x (gcd-ℕ a b)
                      ( div-gcd-is-common-divisor-ℕ a b x H))
                    ( concatenate-div-eq-ℕ (pr2 H) (inv β)))))) ∙
          ( right-unit-law-dist-ℕ b)))
      ( d)
    where
    r : ℕ
    r = remainder-euclidean-division-ℕ (gcd-ℕ a b) b
    q : ℕ
    q = quotient-euclidean-division-ℕ (gcd-ℕ a b) b
    α : q *ℕ gcd-ℕ a b ＝ dist-ℕ b r
    α = eq-quotient-euclidean-division-ℕ (gcd-ℕ a b) b
    B : le-ℕ r (gcd-ℕ a b)
    B =
      strict-upper-bound-remainder-euclidean-division-ℕ
        (gcd-ℕ a b) b (is-nonzero-gcd-ℕ a b np)
    β : q *ℕ gcd-ℕ a b +ℕ r ＝ b
    β = eq-euclidean-division-ℕ (gcd-ℕ a b) b

is-common-divisor-div-gcd-ℕ :
  (a b x : ℕ) → div-ℕ x (gcd-ℕ a b) → is-common-divisor-ℕ a b x
pr1 (is-common-divisor-div-gcd-ℕ a b x d) =
  div-left-factor-div-gcd-ℕ a b x d
pr2 (is-common-divisor-div-gcd-ℕ a b x d) =
  div-right-factor-div-gcd-ℕ a b x d
```

<!-- rosetta-agda-block: theorem-8.4.8-gcd-is-gcd -->

```agda
is-gcd-gcd-ℕ : (a b : ℕ) → is-gcd-ℕ a b (gcd-ℕ a b)
pr1 (is-gcd-gcd-ℕ a b x) = div-gcd-is-common-divisor-ℕ a b x
pr2 (is-gcd-gcd-ℕ a b x) = is-common-divisor-div-gcd-ℕ a b x
```
<!-- rosetta-item-end: theorem-8.4.8 -->
