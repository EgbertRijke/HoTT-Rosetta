# Section 16.1 Counting in type theory

```agda
module section-16-1-counting-in-type-theory where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import exercise-7-5-observational-equality-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-4-finite-types-not-contractible
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-4-coproduct-truncation
open import exercise-12-8-retracts-of-truncated-types
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
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = (n ＝ zero-ℕ)

is-zero-ℕ' : ℕ → UU lzero
is-zero-ℕ' n = (zero-ℕ ＝ n)

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

## Remark 16.1.6

We also note that any type `A` equipped with a counting `e : Fin_{k} ≃ A` has decidable equality.
This follows from Proposition 8.1.8, where we showed that `Fin_{k}` has decidable equality, for any `k : ℕ`.

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

