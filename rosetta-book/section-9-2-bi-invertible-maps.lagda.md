# Section 9.2 Bi-invertible maps

```agda
module section-9-2-bi-invertible-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-2-boolean-operations
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-6-successor-predecessor-integers
open import exercise-5-7-group-laws-integers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import exercise-7-4-successor-finite-types-addition
open import exercise-7-6-predecessor-finite-types
open import section-9-1-homotopies
```

We use homotopies to define sections and retractions of a map `f`, and to define what it means for a map `f` to be an equivalence.

## Definition 9.2.1

Let `f : A → B` be a function.

1. The type of **sections** of `f` is defined to be the type

   ```text
     sec(f) ≔ Σ(g : B → A) f ∘ g ~ id.
   ```

   In other words, a **section** of `f` is a map `g : B → A` equipped with a homotopy `f ∘ g ~ id`.

2. The type of **retractions** of `f` is defined to be the type

   ```text
     retr(f) ≔ Σ(h : B → A) h ∘ f ~ id.
   ```

   If a map `f : A → B` has a retraction, we also say that `A` is a **retract** of `B`.

3. We say that a function `f : A → B` is an **equivalence** if it has both a section and a retraction, i.e., if it comes equipped with an element of type

   ```text
     is-equiv(f) ≔ sec(f) × retr(f).
   ```

   We will write `A ≃ B` for the type `Σ(f : A → B) is-equiv(f)` of all equivalences from `A` to `B`.
   For any equivalence `e : A ≃ B` we define `e⁻¹` to be the section of `e`.

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B)
  where

  is-section : (B → A) → Type l2
  is-section g = f ∘ g ~ id

  section : Type (l1 ⊔ l2)
  section = Σ (B → A) is-section

  map-section : section → B → A
  map-section = pr1

  is-section-map-section : (s : section) → is-section (map-section s)
  is-section-map-section = pr2

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-retraction : (f : A → B) (g : B → A) → Type l1
  is-retraction f g = g ∘ f ~ id

  retraction : (f : A → B) → Type (l1 ⊔ l2)
  retraction f = Σ (B → A) (is-retraction f)

  map-retraction : (f : A → B) → retraction f → B → A
  map-retraction f = pr1

  is-retraction-map-retraction :
    (f : A → B) (r : retraction f) → map-retraction f r ∘ f ~ id
  is-retraction-map-retraction f = pr2

retract : {l1 l2 : Level} → Type l1 → Type l2 → Type (l1 ⊔ l2)
retract B A = Σ (A → B) (retraction)

infix 6 _retract-of_

_retract-of_ :
  {l1 l2 : Level} → Type l1 → Type l2 → Type (l1 ⊔ l2)
A retract-of B = retract B A

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-equiv : (A → B) → Type (l1 ⊔ l2)
  is-equiv f = section f × retraction f

module _
  {l1 l2 : Level} (A : Type l1) (B : Type l2)
  where

  equiv : Type (l1 ⊔ l2)
  equiv = Σ (A → B) is-equiv

infix 6 _≃_

_≃_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
A ≃ B = equiv A B
```

## Remark 9.2.2

An equivalence, as we defined it here, can be thought of as a *bi-invertible map*, since it comes equipped with a separate left and right inverse.
Explicitly, if `f` is an equivalence, then there are

```text
  g : B → A
  h : B → A
  G : f ∘ g ~ id
  H : h ∘ f ~ id.
```

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (H : is-equiv f)
  where

  section-is-equiv : section f
  section-is-equiv = pr1 H

  retraction-is-equiv : retraction f
  retraction-is-equiv = pr2 H

  map-section-is-equiv : B → A
  map-section-is-equiv = map-section f section-is-equiv

  map-retraction-is-equiv : B → A
  map-retraction-is-equiv = map-retraction f retraction-is-equiv

  is-section-map-section-is-equiv : is-section f map-section-is-equiv
  is-section-map-section-is-equiv = is-section-map-section f section-is-equiv

  is-retraction-map-retraction-is-equiv :
    is-retraction f map-retraction-is-equiv
  is-retraction-map-retraction-is-equiv =
    is-retraction-map-retraction f retraction-is-equiv

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (e : A ≃ B)
  where

  map-equiv : A → B
  map-equiv = pr1 e

  is-equiv-map-equiv : is-equiv map-equiv
  is-equiv-map-equiv = pr2 e

  section-map-equiv : section map-equiv
  section-map-equiv = section-is-equiv is-equiv-map-equiv

  map-section-map-equiv : B → A
  map-section-map-equiv = map-section map-equiv section-map-equiv

  is-section-map-section-map-equiv :
    is-section map-equiv map-section-map-equiv
  is-section-map-section-map-equiv =
    is-section-map-section map-equiv section-map-equiv

  retraction-map-equiv : retraction map-equiv
  retraction-map-equiv = retraction-is-equiv is-equiv-map-equiv

  map-retraction-map-equiv : B → A
  map-retraction-map-equiv = map-retraction map-equiv retraction-map-equiv

  is-retraction-map-retraction-map-equiv :
    is-retraction map-equiv map-retraction-map-equiv
  is-retraction-map-retraction-map-equiv =
    is-retraction-map-retraction map-equiv retraction-map-equiv
```

## Example 9.2.3

For any type `A`, the identity function `id : A → A` is an equivalence, since it is its own section and its own retraction

```agda
module _
  {l : Level} {A : Type l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy

  id-equiv : A ≃ A
  pr1 id-equiv = id
  pr2 id-equiv = is-equiv-id
```

## Example 9.2.4

Since we have seen in Remark 9.1.1 that the negation function `neg-bool:bool→bool` on the booleans is its own inverse, it follows that `neg-bool` is an equivalence.

```agda
is-involution :
  {l : Level} {A : Type l} (f : A → A) → Type l
is-involution f = f ∘ f ~ id

is-equiv-is-involution :
  {l : Level} {A : Type l} {f : A → A} → is-involution f → is-equiv f
pr1 (pr1 (is-equiv-is-involution {f = f} H)) = f
pr2 (pr1 (is-equiv-is-involution {f = f} H)) = H
pr1 (pr2 (is-equiv-is-involution {f = f} H)) = f
pr2 (pr2 (is-equiv-is-involution {f = f} H)) = H

abstract
  is-equiv-neg-bool : is-equiv neg-bool
  is-equiv-neg-bool = is-equiv-is-involution is-involution-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
```

## Example 9.2.5

The successor and predecessor functions on `ℤ` are equivalences by Exercise 5.6.
Furthermore, the function

```text
  x ↦ x + k
```

is an equivalence from `ℤ` to `ℤ`, for each `k : ℤ`.
This follows from the group laws on `ℤ`, proven in Exercise 5.7.
Indeed, the inverse of `x ↦ x + k` is the map `x ↦ x + (-k)`.
Finally, it also follows from the group laws on `ℤ` that the map `x ↦ -x` is an equivalence.

```agda
abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  pr1 (pr1 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr1 is-equiv-succ-ℤ) = is-section-pred-ℤ
  pr1 (pr2 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr2 is-equiv-succ-ℤ) = is-retraction-pred-ℤ

equiv-succ-ℤ : ℤ ≃ ℤ
pr1 equiv-succ-ℤ = succ-ℤ
pr2 equiv-succ-ℤ = is-equiv-succ-ℤ

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  pr1 (pr1 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr1 is-equiv-pred-ℤ) = is-retraction-pred-ℤ
  pr1 (pr2 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr2 is-equiv-pred-ℤ) = is-section-pred-ℤ

equiv-pred-ℤ : ℤ ≃ ℤ
pr1 equiv-pred-ℤ = pred-ℤ
pr2 equiv-pred-ℤ = is-equiv-pred-ℤ

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  is-equiv-neg-ℤ = is-equiv-is-involution neg-neg-ℤ

equiv-neg-ℤ : ℤ ≃ ℤ
pr1 equiv-neg-ℤ = neg-ℤ
pr2 equiv-neg-ℤ = is-equiv-neg-ℤ
```

The same holds for the finite types: the maps `succ-Fin_{k}`, `pred-Fin_{k}`, `add-Fin_{k}(x)` and `neg-Fin_{k}` are all equivalences on `Fin{k}`.

```agda
is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
pr1 (pr1 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr1 (is-equiv-succ-Fin k)) = is-section-pred-Fin k
pr1 (pr2 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr2 (is-equiv-succ-Fin k)) = is-retraction-pred-Fin k

equiv-succ-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-succ-Fin k) = succ-Fin k
pr2 (equiv-succ-Fin k) = is-equiv-succ-Fin k

is-equiv-pred-Fin : (k : ℕ) → is-equiv (pred-Fin k)
pr1 (pr1 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr1 (is-equiv-pred-Fin k)) = is-retraction-pred-Fin k
pr1 (pr2 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr2 (is-equiv-pred-Fin k)) = is-section-pred-Fin k

equiv-pred-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-pred-Fin k) = pred-Fin k
pr2 (equiv-pred-Fin k) = is-equiv-pred-Fin k
```

## Remark 9.2.6

More generally, if `f` **has an inverse** in the sense that we have a function `g : B → A` equipped with homotopies `f ∘ g ~ id` and `g ∘ f ~ id`, then `f` is an equivalence.
We write

```text
  has-inverse(f) ≔ Σ(g : B → A) (f ∘ g ~ id) × (g ∘ f ~ id).
```

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-inverse : (A → B) → (B → A) → Type (l1 ⊔ l2)
  is-inverse f g = ((f ∘ g) ~ id) × ((g ∘ f) ~ id)

  is-section-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → f ∘ g ~ id
  is-section-is-inverse = pr1

  is-retraction-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → g ∘ f ~ id
  is-retraction-is-inverse = pr2

is-invertible :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → Type (l1 ⊔ l2)
is-invertible {A = A} {B} f = Σ (B → A) (is-inverse f)

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-equiv-is-invertible' : is-invertible f → is-equiv f
  is-equiv-is-invertible' (g , H , K) = ((g , H) , (g , K))

  is-equiv-is-invertible :
    (g : B → A) (H : f ∘ g ~ id) (K : g ∘ f ~ id) → is-equiv f
  is-equiv-is-invertible g H K = is-equiv-is-invertible' (g , H , K)
```

However, we did *not* define equivalences to be functions that have inverses.
The reason is that we would like that being an equivalence is a *property*, not a non-trivial structure on the map `f`.
This fact requires the function extensionality axiom, but we can already say that if a map `f` is an equivalence, then it has up to homotopy only one section and only one retraction (see Exercise 13.4).

The type `has-inverse(f)` on the other hand, turns out to be homotopically complicated.
In Exercise 22.5 we will see that the identity function `id : S¹ → S¹` on the circle is an example of a map for which

```text
  has-inverse(id_{S¹}) ≃ ℤ.
```

Even though `is-equiv(f)` and `has-inverse(f)` can be wildly different types, there are maps back and forth between the two.
We have already observed in Remark 9.2.6 that there is a map

```text
  has-inverse(f) → is-equiv(f).
```

The following proposition gives the converse implication.

## Proposition 9.2.7

Any map `f : A → B` which is an equivalence, can be given the structure of an invertible map i.e., there is a map

```text
  is-equiv(f) → has-inverse(f).
```

### Proof

First we construct for any equivalence `f` with right inverse `g` and left inverse `h` a homotopy `K : g ~ h`.
For any `y : B`, we have

```text
        H(g(y))⁻¹          ap_h(G(y))
  g(y) =========== hfg(y) ============ h(y)
```

In other words, the homotopy `K : g ~ h` is defined to be `(H · g)⁻¹ ∙ (h · G)`.
Using the homotopy `K` we are able to show that `g` is also a left inverse of `f`.
For `x : A` we have the identification

```text
         K(f(x))         H(x)
  gf(x) ========= hf(x) ====== x. □
```

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-retraction-map-section-is-equiv :
    (H : is-equiv f) → is-retraction f (map-section-is-equiv H)
  is-retraction-map-section-is-equiv H =
    ( ( inv-htpy
        ( ( is-retraction-map-retraction-is-equiv H) ·r
          ( map-section-is-equiv H ∘ f))) ∙h
      ( map-retraction-is-equiv H ·l is-section-map-section-is-equiv H ·r f)) ∙h
    ( is-retraction-map-retraction-is-equiv H)

  is-invertible-is-equiv : is-equiv f → is-invertible f
  pr1 (is-invertible-is-equiv H) = map-section-is-equiv H
  pr1 (pr2 (is-invertible-is-equiv H)) = is-section-map-section-is-equiv H
  pr2 (pr2 (is-invertible-is-equiv H)) = is-retraction-map-section-is-equiv H
```

## Corollary 9.2.8

The inverse of an equivalence is again an equivalence.

### Proof

Let `f : A → B` be an equivalence.
By Proposition 9.2.7 it follows that the section of `f` is also a retraction.
Therefore it follows that the section is itself an invertible map, with inverse `f`.
Hence it is an equivalence. ◻

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (H : is-equiv f)
  where

  is-equiv-map-section-is-equiv : is-equiv (map-section-is-equiv H)
  is-equiv-map-section-is-equiv =
    is-equiv-is-invertible f
      ( is-retraction-map-section-is-equiv H)
      ( is-section-map-section-is-equiv H)
```

## Example 9.2.9

Types, just as sets in classical mathematics, satisfy the usual laws of coproducts and products, such as unit laws, commutativity, and associativity.
These laws are formulated as equivalences:

```text
        ∅ + B ≃ B
        A + ∅ ≃ A
        A + B ≃ B + A
  (A + B) + C ≃ A + (B + C)
        ∅ × B ≃ ∅
        A × ∅ ≃ ∅
        1 × B ≃ B
        A × 1 ≃ A
        A × B ≃ B × A
  (A × B) × C ≃ A × (B × C)
  A × (B + C) ≃ (A × B) + (A × C)
  (A + B) × C ≃ (A × C) + (B × C).
```

All of these equivalences are constructed in a similar way: the maps back and forth as well as the required homotopies are constructed using induction, or, more efficiently, using pattern matching.
For example, to show that cartesian products distribute from the left over coproducts, we construct maps

```text
  α : A × (B + C) → (A × B) + (A × C)
  β : (A × B) + (A × C) → A × (B + C)
```

as follows:

```text
  α(x,inl(y)) ≔ inl(x,y)
  α(x,inr(z)) ≔ inr(x,z)
  β(inl(x,y)) ≔ (x,inl(y))
  β(inr(x,z)) ≔ (x,inr(z)).
```

The homotopies `G : α ∘ β ~ id` and `H : β ∘ α ~ id` are then defined by

```text
  G(inl(x,y)) ≔ refl
  G(inr(x,z)) ≔ refl
  H(x,inl(y)) ≔ refl
  H(x,inr(z)) ≔ refl.
```

We encourage the reader to write out the definitions of at least a few of these equivalences.

### The equivalence `∅ + B ≃ B`

```agda
module _
  {l1 l2 : Level} (A : Type l1) (B : Type l2) (H : is-empty A)
  where

  map-inv-left-unit-law-coproduct-is-empty : B → A + B
  map-inv-left-unit-law-coproduct-is-empty = inr

  is-section-map-inv-left-unit-law-coproduct-is-empty :
    ( map-left-unit-law-coproduct-is-empty A B H ∘
      map-inv-left-unit-law-coproduct-is-empty) ~ id
  is-section-map-inv-left-unit-law-coproduct-is-empty = refl-htpy

  is-retraction-map-inv-left-unit-law-coproduct-is-empty :
    ( map-inv-left-unit-law-coproduct-is-empty ∘
      map-left-unit-law-coproduct-is-empty A B H) ~ id
  is-retraction-map-inv-left-unit-law-coproduct-is-empty (inl a) =
    ex-falso (H a)
  is-retraction-map-inv-left-unit-law-coproduct-is-empty (inr b) = refl

  is-equiv-map-left-unit-law-coproduct-is-empty :
    is-equiv (map-left-unit-law-coproduct-is-empty A B H)
  is-equiv-map-left-unit-law-coproduct-is-empty =
    is-equiv-is-invertible
      map-inv-left-unit-law-coproduct-is-empty
      is-section-map-inv-left-unit-law-coproduct-is-empty
      is-retraction-map-inv-left-unit-law-coproduct-is-empty

  left-unit-law-coproduct-is-empty : (A + B) ≃ B
  pr1 left-unit-law-coproduct-is-empty = map-left-unit-law-coproduct-is-empty A B H
  pr2 left-unit-law-coproduct-is-empty =
    is-equiv-map-left-unit-law-coproduct-is-empty

  is-equiv-inr-is-empty :
    is-equiv inr
  is-equiv-inr-is-empty =
    is-equiv-is-invertible
      ( map-left-unit-law-coproduct-is-empty A B H)
      ( is-retraction-map-inv-left-unit-law-coproduct-is-empty)
      ( is-section-map-inv-left-unit-law-coproduct-is-empty)

  inv-left-unit-law-coproduct-is-empty : B ≃ (A + B)
  pr1 inv-left-unit-law-coproduct-is-empty =
    map-inv-left-unit-law-coproduct-is-empty
  pr2 inv-left-unit-law-coproduct-is-empty = is-equiv-inr-is-empty

module _
  {l : Level} (B : Type l)
  where

  map-inv-left-unit-law-coproduct : B → empty + B
  map-inv-left-unit-law-coproduct = inr

  is-section-map-inv-left-unit-law-coproduct :
    ( map-left-unit-law-coproduct id ∘ map-inv-left-unit-law-coproduct) ~ id
  is-section-map-inv-left-unit-law-coproduct =
    is-section-map-inv-left-unit-law-coproduct-is-empty empty B id

  is-retraction-map-inv-left-unit-law-coproduct :
    ( map-inv-left-unit-law-coproduct ∘ map-left-unit-law-coproduct id) ~ id
  is-retraction-map-inv-left-unit-law-coproduct =
    is-retraction-map-inv-left-unit-law-coproduct-is-empty empty B id

  is-equiv-map-left-unit-law-coproduct : is-equiv (map-left-unit-law-coproduct id)
  is-equiv-map-left-unit-law-coproduct =
    is-equiv-map-left-unit-law-coproduct-is-empty empty B id

  left-unit-law-coproduct : (empty + B) ≃ B
  left-unit-law-coproduct = left-unit-law-coproduct-is-empty empty B id

  inv-left-unit-law-coproduct : B ≃ (empty + B)
  inv-left-unit-law-coproduct = inv-left-unit-law-coproduct-is-empty empty B id
```

### The equivalence `A + ∅ ≃ A`

```agda
module _
  {l1 l2 : Level} (A : Type l1) (B : Type l2) (H : is-empty B)
  where

  map-inv-right-unit-law-coproduct-is-empty : A → A + B
  map-inv-right-unit-law-coproduct-is-empty = inl

  is-section-map-inv-right-unit-law-coproduct-is-empty :
    ( map-right-unit-law-coproduct-is-empty A B H ∘
      map-inv-right-unit-law-coproduct-is-empty) ~ id
  is-section-map-inv-right-unit-law-coproduct-is-empty a = refl

  is-retraction-map-inv-right-unit-law-coproduct-is-empty :
    ( map-inv-right-unit-law-coproduct-is-empty ∘
      map-right-unit-law-coproduct-is-empty A B H) ~ id
  is-retraction-map-inv-right-unit-law-coproduct-is-empty (inl a) = refl
  is-retraction-map-inv-right-unit-law-coproduct-is-empty (inr b) =
    ex-falso (H b)

  is-equiv-map-right-unit-law-coproduct-is-empty :
    is-equiv (map-right-unit-law-coproduct-is-empty A B H)
  is-equiv-map-right-unit-law-coproduct-is-empty =
    is-equiv-is-invertible
      map-inv-right-unit-law-coproduct-is-empty
      is-section-map-inv-right-unit-law-coproduct-is-empty
      is-retraction-map-inv-right-unit-law-coproduct-is-empty

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty =
    is-equiv-is-invertible
      ( map-right-unit-law-coproduct-is-empty A B H)
      ( is-retraction-map-inv-right-unit-law-coproduct-is-empty)
      ( is-section-map-inv-right-unit-law-coproduct-is-empty)

  right-unit-law-coproduct-is-empty : (A + B) ≃ A
  pr1 right-unit-law-coproduct-is-empty = map-right-unit-law-coproduct-is-empty A B H
  pr2 right-unit-law-coproduct-is-empty =
    is-equiv-map-right-unit-law-coproduct-is-empty

  inv-right-unit-law-coproduct-is-empty : A ≃ (A + B)
  pr1 inv-right-unit-law-coproduct-is-empty = inl
  pr2 inv-right-unit-law-coproduct-is-empty = is-equiv-inl-is-empty

module _
  {l : Level} (A : Type l)
  where

  map-inv-right-unit-law-coproduct : A → A + empty
  map-inv-right-unit-law-coproduct = inl

  is-section-map-inv-right-unit-law-coproduct :
    ( map-right-unit-law-coproduct id ∘ map-inv-right-unit-law-coproduct) ~ id
  is-section-map-inv-right-unit-law-coproduct =
    is-section-map-inv-right-unit-law-coproduct-is-empty A empty id

  is-retraction-map-inv-right-unit-law-coproduct :
    ( map-inv-right-unit-law-coproduct ∘ map-right-unit-law-coproduct id) ~ id
  is-retraction-map-inv-right-unit-law-coproduct =
    is-retraction-map-inv-right-unit-law-coproduct-is-empty A empty id

  is-equiv-map-right-unit-law-coproduct : is-equiv (map-right-unit-law-coproduct id)
  is-equiv-map-right-unit-law-coproduct =
    is-equiv-map-right-unit-law-coproduct-is-empty A empty id

  right-unit-law-coproduct : (A + empty) ≃ A
  right-unit-law-coproduct = right-unit-law-coproduct-is-empty A empty id

  inv-right-unit-law-coproduct : A ≃ (A + empty)
  inv-right-unit-law-coproduct =
    inv-right-unit-law-coproduct-is-empty A empty id
```

### The equivalence `A + B ≃ B + A`

### The equivalence `(A + B) + C ≃ A + (B + C)`

### The equivalence `∅ × B ≃ ∅`

### The equivalence `A × ∅ ≃ ∅`

### The equivalence `1 × B ≃ B`

### The equivalence `A × 1 ≃ A`

### The equivalence `A × B ≃ B × A`

### The equivalence `(A × B) × C ≃ A × (B × C)`

### The equivalence `A × (B + C) ≃ (A × B) + (A × C)`

### The equivalence `(A + B) × C ≃ (A × C) + (B × C)`

## Example 9.2.10

The laws for cartesian products can be generalized to arbitrary `Σ`-types.
The absorption laws and unit laws, for instance, are as follows:

```text
  Σ(x : ∅) B(x) ≃ ∅
  Σ(x : 1) B(x) ≃ B(⋆)
     Σ(x : A) ∅ ≃ ∅
     Σ(x : A) 1 ≃ A.
```

Note that the right absorption law and the right unit law are exactly the same as the right absorption and unit laws for cartesian products.
The left absorption and unit laws are, however, formulated with a type family `B` over `∅` and over `1`, and therefore they are slightly more general.

Commutativity cannot be generalized to `Σ`-types.
Associativity, on the other hand, can be expressed in two ways:

```text
  Σ(w : Σ(x : A) B(x)) C(w) ≃ Σ(x : A) Σ(y : B) C(x,y)
  Σ(w : Σ(x : A) B(x)) C(pr1(w),pr2(w)) ≃ Σ(x : A) Σ(y : B(x)) C(x,y).
```

In the first of these equivalences associativity is stated using a type family `C` over `Σ(x : A) B(x)` while in the second it is stated using a family of types `C(x,y)` indexed by `x : A` and `y : B(x)`.

Finally, we note that `Σ` also distributes over coproducts.
In other words, there are the following two equivalences:

```text
  Σ(x : A) B(x) + C(x) ≃ (Σ(x : A) B(x)) + (Σ(x : A) C(x))
  Σ(w : A + B) C(w) ≃ (Σ(x : A) C(inl(x))) + (Σ(y : B) C(inr(y))).
```

## Remark 9.2.11

We haven’t stated any laws involving function types or dependent function types, because it requires the function extensionality principle to prove them.
