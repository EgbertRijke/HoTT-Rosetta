# Section 16.1 Counting in type theory

```agda
module section-16-1-counting-in-type-theory where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import exercise-7-5-observational-equality-finite-types
open import section-8-1-decidability-and-decidable-equality
open import exercise-8-6-decidable-equality-products
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-6-coproduct-functor-equivalences
open import exercise-9-7-product-functor-equivalences
open import exercise-9-8-finite-type-arithmetic-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-4-finite-types-not-contractible
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import exercise-10-8-fiber-replacement
open import section-11-1-families-of-equivalences
open import section-12-1-propositions
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-4-coproduct-truncation
open import exercise-12-8-retracts-of-truncated-types
open import section-13-2-identity-systems-on-pi-types
```

When someone counts the elements of a finite set `A`, they go through the elements of `A` one by one, at each stage keeping track of how many elements have been counted so far.
This process results in the number `|A|` of elements of the set `A`, and moreover it gives a bijection from the standard finite set with `|A|` elements.
In other words, to count the elements of `A` is to give an equivalence from one of the standard finite sets to the set `A`.
We turn this into a definition.

## Definition 16.1.1

For each type `A`, we define the type

```text
  count(A) ≔ Σ(k : ℕ) (Fin_{k} ≃ A).
```

The elements of `count(A)` are called **countings** of `A`.
When we have `(k,e) : count(A)`, we also say that `A` **has `k` elements**.

```agda
count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

module _
  {l : Level} {X : UU l} (e : count X)
  where

  number-of-elements-count : ℕ
  number-of-elements-count = pr1 e

  equiv-count : Fin number-of-elements-count ≃ X
  equiv-count = pr2 e

  map-equiv-count : Fin number-of-elements-count → X
  map-equiv-count = map-equiv equiv-count

  map-inv-equiv-count : X → Fin number-of-elements-count
  map-inv-equiv-count = map-inv-equiv equiv-count

  is-section-map-inv-equiv-count : (map-equiv-count ∘ map-inv-equiv-count) ~ id
  is-section-map-inv-equiv-count = is-section-map-inv-equiv equiv-count

  is-retraction-map-inv-equiv-count :
    (map-inv-equiv-count ∘ map-equiv-count) ~ id
  is-retraction-map-inv-equiv-count = is-retraction-map-inv-equiv equiv-count

  inv-equiv-count : X ≃ Fin number-of-elements-count
  inv-equiv-count = inv-equiv equiv-count

  is-set-type-count : is-set X
  is-set-type-count =
    is-set-equiv'
      ( Fin number-of-elements-count)
      ( equiv-count)
      ( is-set-Fin number-of-elements-count)

  set-type-count : Set l
  set-type-count = (X , is-set-type-count)
```

Note that the type `count(A)` is often not a proposition.
For instance, different equivalences of type `Fin_{k} ≃ Fin_{k}` induce different elements of type `count(Fin_{k})`.

## Example 16.1.2

It follows immediately from the definition of countings that every standard finite type can be counted in a canonical way: For any `k : ℕ` we have `(k,id) : count(Fin_{k})`.
It also follows immediately from the definition of countings that types equipped with countings are closed under equivalences.

```agda
count-Fin : (k : ℕ) → count (Fin k)
pr1 (count-Fin k) = k
pr2 (count-Fin k) = id-equiv

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  abstract
    equiv-count-equiv :
      (e : X ≃ Y) (f : count X) → Fin (number-of-elements-count f) ≃ Y
    equiv-count-equiv e f = e ∘e (equiv-count f)

  count-equiv : X ≃ Y → count X → count Y
  pr1 (count-equiv e f) = number-of-elements-count f
  pr2 (count-equiv e f) = equiv-count-equiv e f

  abstract
    equiv-count-equiv' :
      (e : X ≃ Y) (f : count Y) → Fin (number-of-elements-count f) ≃ X
    equiv-count-equiv' e f = inv-equiv e ∘e (equiv-count f)

  count-equiv' : X ≃ Y → count Y → count X
  pr1 (count-equiv' e f) = number-of-elements-count f
  pr2 (count-equiv' e f) = equiv-count-equiv' e f

  count-is-equiv : {f : X → Y} → is-equiv f → count X → count Y
  count-is-equiv H = count-equiv (_ , H)

  count-is-equiv' :
    {f : X → Y} → is-equiv f → count Y → count X
  count-is-equiv' H = count-equiv' (_ , H)
```

## Example 16.1.3

Suppose `A` comes equipped with a counting `(k,e) : count(A)`.
Then `k = 0` if and only if `A` is empty.
Indeed, the inverse of `e` is a map `e⁻¹ : A → empty`.
Conversely, if we have `f : is-empty(A)`, then the map `f : A → empty` is automatically an equivalence.
This shows that `Fin_{k} ≃ empty`, and a short argument by induction on `k` yields that `k = 0`.

```agda
abstract
  is-empty-is-zero-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-zero-ℕ (number-of-elements-count e) → is-empty X
  is-empty-is-zero-number-of-elements-count (.0 , e) refl x =
    map-inv-equiv e x

abstract
  is-zero-number-of-elements-count-is-empty :
    {l : Level} {X : UU l} (e : count X) →
    is-empty X → is-zero-ℕ (number-of-elements-count e)
  is-zero-number-of-elements-count-is-empty (0 , e) H = refl
  is-zero-number-of-elements-count-is-empty (succ-ℕ k , e) H =
    ex-falso (H (map-equiv e (zero-Fin k)))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
pr1 (count-is-empty H) = 0
pr2 (count-is-empty H) = inv-equiv (H , is-equiv-is-empty' H)

count-empty : count empty
count-empty = count-Fin 0
```

## Example 16.1.4

A type `A` has one element if and only if it is contractible.
Indeed, the type `Fin_{1}` is contractible, so it follows from the 3-for-2 property of contractible types (Exercise 10.2) that there is an equivalence `Fin_{1} ≃ A` if and only if `A` is contractible.

```agda
count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
pr1 (count-is-contr H) = 1
pr2 (count-is-contr H) = equiv-is-contr is-contr-Fin-1 H

abstract
  is-contr-is-one-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-one-ℕ (number-of-elements-count e) → is-contr X
  is-contr-is-one-number-of-elements-count (.1 , e) refl =
    is-contr-equiv' (Fin 1) e is-contr-Fin-1

abstract
  is-one-number-of-elements-count-is-contr :
    {l : Level} {X : UU l} (e : count X) →
    is-contr X → is-one-ℕ (number-of-elements-count e)
  is-one-number-of-elements-count-is-contr (0 , e) H =
    ex-falso (map-inv-equiv e (center H))
  is-one-number-of-elements-count-is-contr (1 , e) H =
    refl
  is-one-number-of-elements-count-is-contr (succ-ℕ (succ-ℕ k) , e) H =
    ex-falso
      ( Eq-Fin-eq (succ-ℕ (succ-ℕ k))
        ( is-injective-equiv e
          ( eq-is-contr' H
            ( map-equiv e (zero-Fin (succ-ℕ k)))
            ( map-equiv e (neg-one-Fin (succ-ℕ k))))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit
```

## Example 16.1.5

A proposition `P` comes equipped with a counting if and only if it is decidable.
To see this, note that for any type `X`, if we have `(k,e) : count(X)`, then it follows that `X` is decidable.
This is shown by induction on `k`.
In the case where `k = 0`, it follows that `X` is empty, and hence that `X` is decidable.
In the case where `k` is a successor, the bijection `e : Fin_{k} ≃ X` gives us the element `e(⋆) : X`.
Again we conclude that `X` is decidable.

Conversely, if `P` is decidable, then we can construct a counting of `P` by case analysis on `d : P + ¬ P`.
If `P` holds, then it is contractible and hence equivalent to `Fin_{1}`.
If `¬ P` holds, then `P` is equivalent to `Fin_{0}`.

```agda
is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e (zero-Fin k))

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-type-Decidable-Prop :
  {l1 : Level} (P : Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-type-Decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-type-Decidable-Prop P (inr f) = count-is-empty f
```

## Remark 16.1.6

We also note that any type `A` equipped with a counting `e : Fin_{k} ≃ A` has decidable equality.
This follows from Proposition 8.1.8, where we showed that `Fin_{k}` has decidable equality, for any `k : ℕ`.

```agda
abstract
  has-decidable-equality-injection :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    injection A B →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-injection (f , H) d x y =
    is-decidable-iff H (ap f) (d (f x) (f y))

abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-retract-of (i , r , R) =
    has-decidable-equality-injection
      ( i , is-injective-has-retraction i r R)

abstract
  has-decidable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-equiv e =
    has-decidable-equality-retract-of (retract-equiv e)

abstract
  has-decidable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality A →
    has-decidable-equality B
  has-decidable-equality-equiv' e =
    has-decidable-equality-retract-of (retract-inv-equiv e)

has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (k , e) =
  has-decidable-equality-equiv' e (has-decidable-equality-Fin k)

cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (x ＝ y)) → count (x ＝ y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (x ＝ y)
count-eq d x y = cases-count-eq d (d x y)

cases-number-of-elements-count-eq' :
  {l : Level} {X : UU l} {x y : X} →
  is-decidable (x ＝ y) → ℕ
cases-number-of-elements-count-eq' (inl p) = 1
cases-number-of-elements-count-eq' (inr f) = 0

number-of-elements-count-eq' :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) → ℕ
number-of-elements-count-eq' d x y =
  cases-number-of-elements-count-eq' (d x y)

cases-number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (x ＝ y)) →
  number-of-elements-count (cases-count-eq d e) ＝
  cases-number-of-elements-count-eq' e
cases-number-of-elements-count-eq d (inl p) = refl
cases-number-of-elements-count-eq d (inr f) = refl

abstract
  number-of-elements-count-eq :
    {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) →
    number-of-elements-count (count-eq d x y) ＝
    number-of-elements-count-eq' d x y
  number-of-elements-count-eq d x y =
    cases-number-of-elements-count-eq d (d x y)
```

## Theorem 16.1.7

We make the following claims about countings:

1. Consider two types `A` and `B`.
The following are equivalent:

   1. Both `A` and `B` come equipped with a counting.

   2. The coproduct `A + B` comes equipped with a counting.

2. Consider a type family `B` indexed by a type `A`.
Consider the following three conditions:

   1. The type `A` comes equipped with a counting.

   2. The type `B(x)` comes equipped with a counting, for each `x : A`.

   3. The type `Σ(x : A) B(x)` comes equipped with a counting.

   If (a) holds, then (b) holds if and only if (c) holds.
   Furthermore, if both (b) and (c) hold and if `B` comes equipped with a section `f : Π(x : A) B(x)`, then (a) holds.

   Consequently, if `P` is a subtype of a type `A` equipped with a counting, then we have

   ```text
     count(Σ(x : A) P(x))↔ Π(x : A) is-decidable(P(x)).
   ```

### Proof

We will first prove the forward direction of (1).
Then we will prove both claims in (2), and we will prove the reverse direction of claim (1) last.

For the forward direction of claim (1), suppose we have equivalences `e : Fin_{k} ≃ A` and `f : Fin_{l} ≃ B`.
The equivalences `e` and `f` induce via Exercises 9.6 and 9.8 a composite equivalence

```text
          ≃                       ≃
  A + B ----> Fin_{k} + Fin_{l} ----> Fin_{k+l}
```

from which we obtain an element of type `count(A + B)`.

Next, we will prove the forward direction in the first claim of (2), i.e., we will prove that if `A` comes equipped with an equivalence `e : Fin_{k} ≃ A`, and if `B` is a family of types over `A` equipped with

```text
  f : Π(x : A) count(B(x)),
```

then the total space `Σ(x : A) B(x)` also has a counting.
The proof is by induction on `k`.
Note that in the base case, where `k = 0`, the type `Σ(x : A) B(x)` is empty, so it has a counting.
For the inductive step, note `Σ` distributes from the right over coproducts.
This gives an equivalence

```text
  Σ(x : A) B(x) ≃ Σ(x : Fin_{k+1}) B(e(x))
                ≃ (Σ(x : Fin_{k}) B(e(inl(x)))) + B(e(inr(⋆))).
```

The type `Σ(x : Fin_{k}) B(e(inl(x)))` has a counting by the inductive hypothesis, and the type `B(e(inr(⋆)))` has a counting by assumption.
Therefore, it follows that the total space `Σ(x : A) B(x)` has a counting.

Now we will prove the converse direction of the first claim in (2).
Suppose that `A` comes equipped with `e : Fin_{k} ≃ A`, and that `Σ(x : A) B(x)` comes equipped with `f : Fin_{l} ≃ Σ(x : A) B(x)`.
By Example 16.1.5 it suffices to show that, for `a : A`, the type `B(a)` is a decidable subtype of `Σ(x : A) B(x)`.
Consider the map

```text
  i : B(a) → Σ(x : A) B(x)
```

given by `b ↦ (a,b)`.
For `(x,y) : Σ(x : A) B(x)`, we have the equivalences

```text
  fib_i(x,y) ≃ Σ(b : B(a)) (a,b) = (x,y)
             ≃ Σ(b : B(a)) Σ(p : a = x) tr_B(p,b) = y
             ≃ Σ(p : a = x) fib(tr_B(p), y)
             ≃ a = x.
```

Here we used that `tr_B(p)` is an equivalence, and therefore has contractible fibers.
Now note that the type `a = x` is a decidable proposition by Remark 16.1.6.

Next, we will prove the second claim in (2).
Suppose that `B` is a family over `A` that comes equipped with a section `b : Π(x : A) B(x)`, and suppose that each `B(x)` has a counting, and that the total space `Σ(x : A) B(x)` has a counting.
Then we have a map

```text
  g : A → Σ(x : A) B(x)
```

given by `a ↦ (a,b(a))`.
The fibers of `g` can be computed by the following equivalences:

```text
  fib_g(x,y) ≃ Σ(a : A) (a,b(a)) = (x,y)
             ≃ Σ(a : A) Σ(p : a = x) tr_B(p,b(a)) = y
             ≃ tr_B(p,b(x)) = y.
```

Note that the type `tr_B(p,b(x)) = y` is a decidable proposition by Remark 16.1.6.
Now it follows by the forward direction of the first claim in (2) that `A` has a counting.

It remains to prove the converse direction of (1).
Note that the forward direction of the first claim in (2) implies that countings on a type `X` induce countings on any decidable subtype of `X`.
Note that both `A` and `B` are decidable subtypes of the coproduct `A + B`.
Any counting of `A + B` therefore induces countings of `A` and of `B`. ◻

```agda
count-coproduct :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (X + Y)
pr1 (count-coproduct (pair k e) (pair l f)) = k +ℕ l
pr2 (count-coproduct (pair k e) (pair l f)) =
  (equiv-coproduct e f) ∘e (inv-equiv (compute-coproduct-Fin k l))

abstract
  number-of-elements-count-coproduct :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    number-of-elements-count (count-coproduct e f) ＝
    (number-of-elements-count e) +ℕ (number-of-elements-count f)
  number-of-elements-count-coproduct (pair k e) (pair l f) = refl

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (cA : count A) (cB : count B)
  where

  map-equiv-count-coproduct-inl-coproduct-Fin :
    map-equiv-count (count-coproduct cA cB) ∘
    inl-coproduct-Fin
      ( number-of-elements-count cA)
      ( number-of-elements-count cB) ~
    inl ∘ map-equiv-count cA
  map-equiv-count-coproduct-inl-coproduct-Fin a =
    ap
      ( map-coproduct _ _)
      ( is-retraction-map-inv-equiv
        ( compute-coproduct-Fin
          ( number-of-elements-count cA)
          ( number-of-elements-count cB))
        ( inl a))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (cA : count A) (cB : count B)
  where

  map-equiv-count-coproduct-inr-coproduct-Fin :
    map-equiv-count (count-coproduct cA cB) ∘
    inr-coproduct-Fin
      ( number-of-elements-count cA)
      ( number-of-elements-count cB) ~
    inr ∘ map-equiv-count cB
  map-equiv-count-coproduct-inr-coproduct-Fin b =
    ap
      ( map-coproduct _ _)
      ( is-retraction-map-inv-equiv
        ( compute-coproduct-Fin
          ( number-of-elements-count cA)
          ( number-of-elements-count cB))
        ( inr b))

count-Σ-Fin :
  {l : Level} (k : ℕ) {B : Fin k → UU l} →
  ((x : Fin k) → count (B x)) → count (Σ (Fin k) B)
count-Σ-Fin 0 f = count-is-empty pr1
count-Σ-Fin (succ-ℕ k) {B} f =
  count-equiv'
    ( ( equiv-coproduct id-equiv (left-unit-law-Σ (B ∘ inr))) ∘e
      ( right-distributive-Σ-coproduct B))
    ( count-coproduct (count-Σ-Fin k (f ∘ inl)) (f (inr star)))

count-Σ' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' k {B = B} e f =
  count-equiv (equiv-Σ-equiv-base B e) (count-Σ-Fin k (f ∘ map-equiv e))

abstract
  equiv-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
    Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

fin-sequence : {l : Level} → UU l → ℕ → UU l
fin-sequence A n = Fin n → A

module _
  {l : Level} {A : UU l}
  where

  empty-fin-sequence : fin-sequence A 0
  empty-fin-sequence ()

  head-fin-sequence : (n : ℕ) → fin-sequence A (succ-ℕ n) → A
  head-fin-sequence n v = v (neg-one-Fin n)

  last-fin-sequence : (n : ℕ) → fin-sequence A (succ-ℕ n) → A
  last-fin-sequence n v = v (zero-Fin n)

  tail-fin-sequence :
    (n : ℕ) → fin-sequence A (succ-ℕ n) → fin-sequence A n
  tail-fin-sequence n v = v ∘ (inl-Fin n)

  init-fin-sequence :
    (n : ℕ) → fin-sequence A (succ-ℕ n) → fin-sequence A n
  init-fin-sequence n v = v ∘ skip-zero-Fin n

  cons-fin-sequence :
    (n : ℕ) → A → fin-sequence A n → fin-sequence A (succ-ℕ n)
  cons-fin-sequence n a v (inl x) = v x
  cons-fin-sequence n a v (inr x) = a

  snoc-fin-sequence :
    (n : ℕ) → fin-sequence A n → A → fin-sequence A (succ-ℕ n)
  snoc-fin-sequence zero-ℕ v a i = a
  snoc-fin-sequence (succ-ℕ n) v a (inl x) =
    snoc-fin-sequence n (tail-fin-sequence n v) a x
  snoc-fin-sequence (succ-ℕ n) v a (inr x) = head-fin-sequence n v

  in-fin-sequence : (n : ℕ) → A → fin-sequence A n → UU l
  in-fin-sequence n a v = Σ (Fin n) (λ k → a ＝ v k)

  index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) →
    in-fin-sequence n x v → Fin n
  index-in-fin-sequence n x v I = pr1 I

  eq-component-fin-sequence-index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) (I : in-fin-sequence n x v) →
    x ＝ v (index-in-fin-sequence n x v I)
  eq-component-fin-sequence-index-in-fin-sequence n x v I = pr2 I

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
pr1 (count-Σ (pair k e) f) = number-of-elements-count (count-Σ' k e f)
pr2 (count-Σ (pair k e) f) = equiv-count-Σ' k e f

module _
  {l : Level} (M : Monoid l)
  where

  fin-sequence-type-Monoid : ℕ → UU l
  fin-sequence-type-Monoid = fin-sequence (type-Monoid M)

  head-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid (succ-ℕ n) → type-Monoid M
  head-fin-sequence-type-Monoid n v = head-fin-sequence n v

  tail-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid (succ-ℕ n) → fin-sequence-type-Monoid n
  tail-fin-sequence-type-Monoid = tail-fin-sequence

  cons-fin-sequence-type-Monoid :
    (n : ℕ) → type-Monoid M →
    fin-sequence-type-Monoid n → fin-sequence-type-Monoid (succ-ℕ n)
  cons-fin-sequence-type-Monoid = cons-fin-sequence

  snoc-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid n → type-Monoid M →
    fin-sequence-type-Monoid (succ-ℕ n)
  snoc-fin-sequence-type-Monoid = snoc-fin-sequence

product-fin-sequence-type-Monoid :
  {l : Level} (M : Monoid l) (n : ℕ) →
  ( fin-sequence-type-Monoid M n) → type-Monoid M
product-fin-sequence-type-Monoid M zero-ℕ f = unit-Monoid M
product-fin-sequence-type-Monoid M (succ-ℕ n) f =
  mul-Monoid M
    ( product-fin-sequence-type-Monoid M n (f ∘ inl-Fin n))
    ( f (inr star))

sum-fin-sequence-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
sum-fin-sequence-ℕ = product-fin-sequence-type-Monoid ℕ-Monoid

sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (k , Fin-k≃A) f = sum-fin-sequence-ℕ k (f ∘ map-equiv Fin-k≃A)

abstract
  number-of-elements-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
    (f : (x : A) → count (B x)) →
    number-of-elements-count (count-Σ' k e f) ＝
    sum-fin-sequence-ℕ k (λ x → number-of-elements-count (f (map-equiv e x)))
  number-of-elements-count-Σ' zero-ℕ e f = refl
  number-of-elements-count-Σ' (succ-ℕ k) e f =
    ( number-of-elements-count-coproduct
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star)))) ∙
    ( ap
      ( _+ℕ (number-of-elements-count (f (map-equiv e (inr star)))))
      ( number-of-elements-count-Σ' k id-equiv (λ x → f (map-equiv e (inl x)))))

abstract
  number-of-elements-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : (x : A) → count (B x)) →
    number-of-elements-count (count-Σ e f) ＝
    sum-count-ℕ e (λ x → number-of-elements-count (f x))
  number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f

count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  has-decidable-equality A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} d f x =
  count-equiv
    ( equiv-fiber-pr1 B x)
    ( count-Σ f
      ( λ z → count-eq d (pr1 z) x))

count-fiber-count-Σ-count-base :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ-count-base e f x =
  count-fiber-count-Σ (has-decidable-equality-count e) f x

count-fiber-map-section-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fiber (map-section-family b) t)
count-fiber-map-section-family {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-torsorial-Id' y)
            ( pair y refl)) ∘e
        ( inv-associative-Σ)) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fiber (map-section-family b))
    ( count-Σ e (count-fiber-map-section-family b e f))

section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → (B x) + (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) (zero-Fin k)))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coproduct)
      ( count-coproduct e g))
    ( λ x →
      count-coproduct
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))
```

### If `A` can be counted and `Σ A P` can be counted for a subtype of `A`, then `P` is decidable

```agda
is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ-count-base e f x)
```

## Corollary 16.1.8

Consider two types `A` and `B`.
We make two claims:

1. If both `A` and `B` come equipped with a counting, then the product `A × B` has a counting.

2. If the product `A × B` comes equipped with a counting, then we have two functions

```text
  B → count(A)
  A → count(B).
```

### Proof

The first claim follows from condition (2a) in Theorem 16.1.7, and the second claim follows from condition (2b) in Theorem 16.1.7. ◻

```agda
count-product :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-product (pair k e) (pair l f)) = k *ℕ l
pr2 (count-product (pair k e) (pair l f)) =
  (equiv-product e f) ∘e (inv-equiv (product-Fin k l))

abstract
  number-of-elements-count-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    number-of-elements-count (count-product count-A count-B) ＝
    number-of-elements-count count-A *ℕ number-of-elements-count count-B
  number-of-elements-count-product (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → pr2 t ＝ y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-product) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-torsorial-Id' y) is-contr-unit))) ∘e
  ( associative-Σ)

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-product e) x
```
