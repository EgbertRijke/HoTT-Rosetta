# Section 8.3 The well-ordering principle of ℕ

```agda
module section-8-3-the-well-ordering-principle-of-natural-numbers where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-6-3-order-natural-numbers
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
```

<!-- rosetta-item: section-8.3 -->

The well-ordering principle of the natural numbers in classical mathematics asserts that any nonempty subset of `ℕ` has a least element.
To formulate the well-ordering principle in type theory, we will use type families over `ℕ` instead of subsets of `ℕ`.
Moreover, the classical well-ordering principle tacitly assumes that subsets are decidable.
The type theoretic well-ordering principle of `ℕ` is therefore formulated using *decidable* families over `ℕ`.

## Definition 8.3.1

<!-- rosetta-item: definition-8.3.1 -->

Let `P` be a family over `ℕ`, not necessarily decidable.

1.  We say that a natural number `n` is a **lower bound** for `P` if it comes equipped with an element of type
```text
is-lower-bound_P(n)≔ Π(x:ℕ) P(x)→ (n≤ x).
```

2.  We say that a natural number `n` is an **upper bound** for `P` if it comes equipped with an element of type
```text
is-upper-bound_P(n)≔ Π(x:ℕ) P(x)→ (x≤ n).
```

<!-- rosetta-agda-block: definition-8.3.1-lower-bound -->

```agda
is-lower-bound-ℕ :
  {l : Level} (P : ℕ → Type l) (n : ℕ) → Type l
is-lower-bound-ℕ P n = (m : ℕ) → P m → leq-ℕ n m
```

<!-- rosetta-agda-block: definition-8.3.1-minimal-element -->

```agda
minimal-element-ℕ :
  {l : Level} (P : ℕ → Type l) → Type l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))
```
<!-- rosetta-item-end: definition-8.3.1 -->

A minimal element of `P` is therefore a natural number `n` for which `P(n)` holds, and which is also a lower bound for `P`.
The well-ordering principle of `ℕ` asserts that such an element exists for any decidable family `P`, as soon as `P(n)` holds for some `n`.

## Theorem 8.3.2

<!-- rosetta-item: theorem-8.3.2; latex-label: thm:well-ordering-principle-N -->

Let `P` be a decidable family over `ℕ`, where `d` witnesses that `P` is decidable.
Then there is a function
```text
w(P,d):(Σ(n:ℕ) P(n))→(Σ(m:ℕ) P(m)×is-lower-bound_P(m)).
```

### Proof

<!-- rosetta-item: subheading-8.3-proof -->

*Proof.* By the assumption that there are enough universes (Postulate 6.2.1), there is a universe `𝒰` that contains `P`.
Instead of proving the claim for the given type family `P`, we will show by induction on `n:ℕ` that there is a function
```text
Q(n)→ (Σ(m:ℕ) Q(m)×is-lower-bound_Q(m))(*)
```
for every decidable family `Q:ℕ→𝒰`.
Note that we are now also quantifying over the decidable families `Q:ℕ→𝒰`.
This slightly strengthens the inductive hypothesis, which we will be able to exploit.

The base case is trivial, since `0` is a lower bound of every type family over `ℕ`.
For the inductive step, assume that (\*) holds for every decidable type family `Q:ℕ→ 𝒰`.
Furthermore, let `Q:ℕ→𝒰` be a decidable type family equipped with an element `q:Q(succ-ℕ(n))`.
Our goal is to construct an element of type
```text
Σ(m:ℕ) Q(m)×is-lower-bound_Q(m).
```
Since `Q(0)` is assumed to be decidable, it suffices to construct a function
```text
(Q(0)+¬ Q(0))→ Σ(m:ℕ) Q(m)×is-lower-bound_Q(m).
```
Therefore we can proceed by case analysis on `Q(0)+¬ Q(0)`.
In the case where we have an element of type `Q(0)`, it follows immediately that `0` must be minimal.
In the case where `¬ Q(0)`, we consider the decidable subset `Q'` of `ℕ` given by
```text
Q'(n)≔ Q(succ-ℕ(n)).
```
Since we have `q:Q'(n)`, we obtain a minimal element in `Q'` by the inductive hypothesis.
Of course, by the assumption that `Q(0)` doesn’t hold, the minimal element of `Q'` is also the minimal element of `Q`. ◻

<!-- rosetta-agda-block: theorem-8.3.2-well-ordering -->

```agda
is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → Type l) (d : is-decidable-family P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ex-falso (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-lower-bound-m n psuccn

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → Type l) (d : is-decidable-family P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) u =
  ( 0 , p0 , λ m q → leq-zero-ℕ m)
well-ordering-principle-succ-ℕ P d n p (inr neg-p0) (m , pm , is-min-m) =
  ( succ-ℕ m , pm , is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0)

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → Type l) (d : is-decidable-family P) →
  Σ ℕ P → minimal-element-ℕ P
pr1 (well-ordering-principle-ℕ P d (pair zero-ℕ p)) = zero-ℕ
pr1 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) = p
pr2 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) m q = leq-zero-ℕ m
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))
```
<!-- rosetta-item-end: theorem-8.3.2 -->
