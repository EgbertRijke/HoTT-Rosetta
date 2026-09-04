# Section 8.1 Decidability and decidable equality

```agda
module section-8-1-decidability-and-decidable-equality where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-3-negation
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import exercise-7-5-observational-equality-finite-types
open import section-6-3-observational-equality-of-the-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-7-2-divisibility-poset
open import exercise-6-5-distance-natural-numbers
open import exercise-7-1-divisibility-three-for-two
```

<!-- rosetta-item: section-8.1 -->

## Definition 8.1.1

<!-- rosetta-item: definition-8.1.1 -->

A type `A` is said to be **decidable** if it comes equipped with an element of type
```text
is-decidable(A)≔ A+¬ A.
```
A family `P` over a type `A` is said to be **decidable** if `P(x)` is decidable for every `x:A`.

<!-- rosetta-agda-block: definition-8.1.1-decidable -->

```agda
is-decidable : {l : Level} (A : Type l) → Type l
is-decidable A = A + (¬ A)
```
<!-- rosetta-item-end: definition-8.1.1 -->

## Example 8.1.2

<!-- rosetta-item: example-8.1.2 -->

The principal way to show that a type `A` is decidable is to either construct an element `a:A`, or to construct a function `A→empty`.
For example, the types `unit` and `empty` are decidable.
Indeed, we have
```text
inl(⋆) :is-decidable(unit)
inr(id) : is-decidable(empty).
```
Furthermore, any type `A` equipped with an element `a:A` is decidable because we have `inl(a):is-decidable(A)` for such `A`.

<!-- rosetta-agda-block: example-8.1.2-unit-empty-decidable -->

```agda
is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id
```
<!-- rosetta-item-end: example-8.1.2 -->

## Example 8.1.3

<!-- rosetta-item: example-8.1.3; latex-label: eg:decidability-closure -->

The principal way to use a hypothesis that `A` is decidable is to proceed by the induction principle of coproducts, i.e., to proceed by case analysis.

For example, if `A` and `B` are decidable types, then the types `A+B`, `A× B`, and `A→ B` are also decidable.
This is straightforward to prove directly by pattern-matching on the variables of type `is-decidable(A)` and `is-decidable(B)`.
When we go through these proofs, the familiar truth table emerges:

<!-- unsupported LaTeX environment: center -->

| `1-5 A` | `B` | `A + B` | `A × B` | `A → B` |
| --- | --- | --- | --- | --- |
| `inl(a)` | `inl(b)` | `inl(inl(a))` | `inl(a,b)` | `inl(λ x. b)` |
| `inl(a)` | `inr(g)` | `inl(inl(a))` | `inr(g∘ pr 2)` | `inr(λ h. g(h(a)))` |
| `inr(f)` | `inl(b)` | `inl(inr(b))` | `inr(f∘pr 1)` | `inl(ex-falso∘ f)` |
| `inr(f)` | `inr(g)` | `inr[f,g]` | `inr(f∘pr 1)` | `inl(ex-falso∘ f)` |

Since `A→ B` is decidable whenever both `A` and `B` are decidable, it also follows that the negation `¬ A` of any decidable type `A` is decidable.

<!-- rosetta-agda-block: example-8.1.3-coproduct-decidable -->

```agda
is-decidable-coproduct :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} →
  is-decidable A → is-decidable B → is-decidable (A + B)
is-decidable-coproduct (inl a) y = inl (inl a)
is-decidable-coproduct (inr na) (inl b) = inl (inr b)
is-decidable-coproduct (inr na) (inr nb) = inr (rec-coproduct na nb)
```

<!-- rosetta-agda-block: example-8.1.3-product-decidable -->

```agda
is-decidable-product :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-product (inl a) (inl b) = inl (a , b)
is-decidable-product (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-product (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-product (inr f) (inr g) = inr (f ∘ pr1)
```

<!-- rosetta-agda-block: example-8.1.3-evaluation -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (a : A)
  where

  ev : ((x : A) → B x) → B a
  ev f = f a
```

<!-- rosetta-agda-block: example-8.1.3-function-decidable -->

```agda
is-decidable-function-type :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ _ → b)
is-decidable-function-type (inl a) (inr nb) = inr (map-neg (ev a) nb)
is-decidable-function-type (inr f) _ = inl (ex-falso ∘ f)
```

<!-- rosetta-agda-block: example-8.1.3-negation-decidable -->

```agda
is-decidable-neg :
  {l : Level} {A : Type l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty
```
<!-- rosetta-item-end: example-8.1.3 -->

## Example 8.1.4

<!-- rosetta-item: example-8.1.4; latex-label: eg:is-decidable-EqN -->

Since the empty type and the unit type are both decidable types, it also follows that the types `Eq-ℕ(m,n)`, `m≤ n` and `m<n` are decidable for each `m,n:ℕ`.
The proofs in each of the three cases is by induction on `m` and `n`.

For instance, to show that `Eq-ℕ(m,n)` is decidable for each `m,n:ℕ`, we simply note that the types
```text
Eq-ℕ(0,0) ≐ unit
Eq-ℕ(0,succ-ℕ(n)) ≐ empty
Eq-ℕ(succ-ℕ(m),0) ≐ empty
```
are all decidable, and that the type `Eq-ℕ(succ-ℕ(m),succ-ℕ(n))≐ Eq-ℕ(m,n)` is decidable by the inductive hypothesis.

<!-- rosetta-agda-block: example-8.1.4-equality-natural-decidable -->

```agda
is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n
```

<!-- rosetta-agda-block: example-8.1.4-inequality-natural-decidable -->

```agda
is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n
```

<!-- rosetta-agda-block: example-8.1.4-strict-inequality-natural-decidable -->

```agda
is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (le-ℕ m n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n
```
<!-- rosetta-item-end: example-8.1.4 -->

The fact that `ℕ` has decidable observational equality also implies that equality itself is decidable on `ℕ`.
This leads to the general concept of decidable equality, which is important in many results about decidability.

## Definition 8.1.5

<!-- rosetta-item: definition-8.1.5 -->

We say that a type `A` has **decidable equality** if the identity type `x=y` is decidable for every `x,y:A`.
We will write
```text
has-decidable-eq(A)≔ Π(x,y:A) is-decidable(x=y).
```

<!-- rosetta-agda-block: definition-8.1.5-decidable-equality -->

```agda
has-decidable-equality : {l : Level} → Type l → Type l
has-decidable-equality A = (x y : A) → is-decidable (x ＝ y)
```
<!-- rosetta-item-end: definition-8.1.5 -->

Before we show that `ℕ` has decidable equality, let us show that if `A↔ B` and `A` is decidable, then `B` must be decidable.

## Lemma 8.1.6

<!-- rosetta-item: lemma-8.1.6; latex-label: lem:is-decidable-iff -->

Consider two types `A` and `B`, and suppose that `A↔ B`.
Then `A` is decidable if and only if `B` is decidable.

### Proof

<!-- rosetta-item: subheading-8.1-proof -->

*Proof.* Since we have functions `f:A→ B` and `g:B→ A` by assumption, we obtain by Proposition 4.3.4 the functions
```text
f̃ : ¬ B→¬ A
g̃ : ¬ A → ¬ B.
```
By Remark 4.4.2 we have therefore the functions
```text
f+g̃ : (A+¬ A) → (B+¬ B)
g+f̃ : (B+¬ B) → (A+¬ A).
```
 ◻

<!-- rosetta-agda-block: proposition-8.5.2-logical-equivalence-projections -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (H : A ↔ B)
  where

  forward-implication : A → B
  forward-implication = pr1 H

  backward-implication : B → A
  backward-implication = pr2 H
```

<!-- rosetta-agda-block: lemma-8.1.6-inverse-logical-equivalence -->

```agda
inv-iff :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A ↔ B) → (B ↔ A)
pr1 (inv-iff (f , g)) = g
pr2 (inv-iff (f , g)) = f
```

<!-- rosetta-agda-block: lemma-8.1.6-decidability-logical-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-decidable-iff :
    (A → B) → (B → A) → is-decidable A → is-decidable B
  is-decidable-iff f g (inl a) = inl (f a)
  is-decidable-iff f g (inr na) = inr (na ∘ g)

  is-decidable-iff' :
    A ↔ B → is-decidable A → is-decidable B
  is-decidable-iff' (f , g) = is-decidable-iff f g

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  iff-is-decidable : A ↔ B → is-decidable A ↔ is-decidable B
  iff-is-decidable e = is-decidable-iff' e , is-decidable-iff' (inv-iff e)
```
<!-- rosetta-item-end: lemma-8.1.6 -->

## Proposition 8.1.7

<!-- rosetta-item: proposition-8.1.7; latex-label: prp:has-decidable-equality-N -->

Equality on the natural numbers is decidable.

### Proof

<!-- rosetta-item: subheading-8.1-proof-2 -->

*Proof.* Recall from Proposition 6.3.3 that we have
```text
(m=n)↔ Eq-ℕ(m,n).
```
The claim therefore follows by Lemma 8.1.6, since we have observed in Example 8.1.4 that `Eq-ℕ(m,n)` is decidable for every `m,n:ℕ`. ◻

<!-- rosetta-agda-block: proposition-8.1.7-natural-decidable-equality -->

```agda
has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)
```

<!-- rosetta-agda-block: proposition-8.5.2-one-decidable -->

```agda
is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n 1
```
<!-- rosetta-item-end: proposition-8.1.7 -->

It is certainly not provable with the given rules of type theory that every type has decidable equality.
In fact, we will show in Theorem 12.3.5 that if a type has decidable equality, then it is a *set*.
However, it is also not provable that every set has decidable equality unless one assumes the *law of excluded middle*.
We will discuss this principle in Section 14.3.
For now, it is important to remember that in order to use decidability, we must first *prove that it holds*, and many familiar types do indeed have decidable equality.

## Proposition 8.1.8

<!-- rosetta-item: proposition-8.1.8; latex-label: prp:has-decidable-equality-Fin -->

The standard finite type `Fin{k}` has decidable equality for each `k:ℕ`.

### Proof

<!-- rosetta-item: subheading-8.1-proof-3 -->

*Proof.* Recall from Exercise 7.5 that we constructed an observational equality relation `Eq-Fin_k` on `Fin{k}` for each `k:ℕ`, which satisfies
```text
(x=y)↔ Eq-Fin_k(x,y).
```
The type `Eq-Fin_k(x,y)` is decidable, since it is recursively defined using the decidable types `empty` and `unit`. ◻

<!-- rosetta-agda-block: proposition-8.1.8-finite-decidable-equality -->

```agda
is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-decidable-unit

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (x ＝ y)
has-decidable-equality-Fin k x y =
  map-coproduct
    ( eq-Eq-Fin k)
    ( map-neg (Eq-Fin-eq k))
    ( is-decidable-Eq-Fin k x y)
```
<!-- rosetta-item-end: proposition-8.1.8 -->

We can use the fact that the finite types `Fin{k}` have decidable equality to show that the divisibility relation on `ℕ` is decidable.

## Theorem 8.1.9

<!-- rosetta-item: theorem-8.1.9; latex-label: thm:is-decidable-div-N -->

For any `d,x:ℕ`, the type `d| x` is decidable.

### Proof

<!-- rosetta-item: subheading-8.1-proof-4 -->

*Proof.* Note that `0| x` is decidable because `0| x` if and only if `x=0`, which is decidable by Proposition 8.1.7.
Therefore it suffices to show that `d+1| x` is decidable.

By Theorem 7.4.7 it follows that `d+1| x` holds if and only if we have an identification `[x]_{d+1}=0` in `Fin{d+1}`.
Therefore the claim follows from the fact that `Fin{d+1}` has decidable equality. ◻

<!-- rosetta-agda-block: theorem-8.1.9-natural-zero-decidable -->

```agda
is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n
```

<!-- rosetta-agda-block: theorem-8.1.9-finite-zero-decidable -->

```agda
is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin k x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (zero-Fin k)
```

<!-- rosetta-agda-block: theorem-8.1.9-zero-divisor -->

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H
```

<!-- rosetta-agda-block: theorem-8.1.9-divisibility-modulo -->

```agda
is-zero-mod-succ-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x)
is-zero-mod-succ-ℕ k x d =
  eq-mod-succ-cong-ℕ k x zero-ℕ
    ( concatenate-div-eq-ℕ d (inv (right-unit-law-dist-ℕ x)))

div-is-zero-mod-succ-ℕ :
  (k x : ℕ) → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-is-zero-mod-succ-ℕ k x p =
  concatenate-div-eq-ℕ
    ( cong-eq-mod-succ-ℕ k x zero-ℕ p)
    ( right-unit-law-dist-ℕ x)
```

<!-- rosetta-agda-block: theorem-8.1.9-divisibility-decidable -->

```agda
is-decidable-div-ℕ : (d x : ℕ) → is-decidable (div-ℕ d x)
is-decidable-div-ℕ zero-ℕ x =
  is-decidable-iff
    ( div-eq-ℕ zero-ℕ x)
    ( inv ∘ (is-zero-div-zero-ℕ x))
    ( is-decidable-is-zero-ℕ' x)
is-decidable-div-ℕ (succ-ℕ d) x =
  is-decidable-iff
    ( div-is-zero-mod-succ-ℕ d x)
    ( is-zero-mod-succ-ℕ d x)
    ( is-decidable-is-zero-Fin (mod-succ-ℕ d x))
```
<!-- rosetta-item-end: theorem-8.1.9 -->
