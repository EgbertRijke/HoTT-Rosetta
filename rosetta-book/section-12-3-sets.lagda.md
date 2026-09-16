# Section 12.3 Sets

```agda
module section-12-3-sets where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-6-3-observational-equality-of-the-natural-numbers
open import section-8-1-decidability-and-decidable-equality
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-11-3-equality-on-the-natural-numbers
open import exercise-11-8-total-map-retractions
open import section-12-1-propositions
open import section-12-2-subtypes
```

## Definition 12.3.1

A type `A` is said to be a **set** if its identity types are propositions, i.e., if it comes equipped with a term of type

```text
  is-set(A) ≔ Π(x, y : A) is-prop(x = y).
```

```agda
is-set : {l : Level} → UU l → UU l
is-set A = (x y : A) → is-prop (x ＝ y)

Set : (l : Level) → UU (lsuc l)
Set l = Σ (UU l) is-set

module _
  {l : Level} (X : Set l)
  where

  type-Set : UU l
  type-Set = pr1 X

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = pr2 X

  Id-Prop : (x y : type-Set) → Prop l
  Id-Prop x y = (x ＝ y , is-set-type-Set x y)
```

## Example 12.3.2

The type of natural numbers is a set.
To see this, recall from Theorem 11.3.1 that we have an equivalence

```text
  (m = n) ≃ Eq-ℕ(m,n)
```

for every `m, n : ℕ`.
Therefore it suffices to show that each `Eq-ℕ(m,n)` is a proposition.
This follows easily by induction on both `m` and `n`.

Note: We will prove here that observational equality is a propositional relation.
The proof in agda-unimath that this implies that the natural numbers form a set
is proven using `is-set-prop-in-id`, which will be proven below.
This does not point at circularity in the book; a direct proof that the natural
numbers form a set could indeed be given as well.

```agda
abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m
```

## Proposition 12.3.3

Consider a type `A`.
The following are equivalent:

1. The type `A` is a set.

2. The type `A` satisfies **axiom K**, i.e., if and only if it comes equipped with a term of type

   ```text
     axiom-K(A) ≔ Π(x : A) Π(p : x = x) refl = p.
   ```

### Proof

If `A` is a set, then `x = x` is a proposition, so any two of its elements are equal.
This implies axiom K.

For the converse, if `A` satisfies axiom K, then for any `p, q : x = y` we have `p ∙ q⁻¹ = refl`, and hence `p = q`.
This shows that `x = y` is a proposition, and hence that `A` is a set. ◻

```agda
instance-axiom-K : {l : Level} → UU l → UU l
instance-axiom-K A = (x : A) (p : x ＝ x) → refl ＝ p

axiom-K-Level : (l : Level) → UU (lsuc l)
axiom-K-Level l = (A : UU l) → instance-axiom-K A

axiom-K : UUω
axiom-K = {l : Level} → axiom-K-Level l

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-axiom-K' :
      instance-axiom-K A → (x y : A) → all-elements-equal (x ＝ y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : instance-axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y)

  abstract
    axiom-K-is-set : is-set A → instance-axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)
```

## Theorem 12.3.4

Let `A` be a type, and let `R : A → A → 𝒰` be a binary relation on `A` satisfying

1. Each `R(x,y)` is a proposition,

2. `R` is reflexive, as witnessed by `ρ : Π(x : A) R(x,x)`,

3. There is a map

   ```text
     R(x,y) → (x = y)
   ```
   
   for each `x, y : A`.

Then any family of maps

```text
  Π(x, y : A) (x = y) → R(x,y)
```

is a family of equivalences.
Consequently, the type `A` is a set.

### Proof

Let `f : Π(x, y : A) R(x,y) → (x = y)`.
Since `R` is assumed to be reflexive, we also have a family of maps

```text
  path-ind_x(ρ(x)) : Π(y : A) (x = y) → R(x,y).
```

Since each `R(x,y)` is assumed to be a proposition, it therefore follows that each `R(x,y)` is a retract of `x = y`.
Therefore it follows that `Σ(y : A) R(x,y)` is a retract of `Σ(y : A) x = y`, which is contractible.
We conclude that `Σ(y : A) R(x,y)` is contractible, and therefore that any family of maps

```text
  Π(y : A) (x = y) → R(x,y)
```

is a family of equivalences.

Now it also follows that `A` is a set, since its identity types are equivalent to propositions, and therefore they are propositions by Lemma 12.2.2. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} (x : A) (R : A → UU l2)
  (p : (y : A) → is-prop (R y)) (ρ : R x)
  (i : (y : A) → R y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-based-id : (y : A) → is-equiv (i y)
    is-equiv-prop-in-based-id =
      fundamental-theorem-id-retraction x i
        ( λ y → (ind-Id x (λ z p → R z) ρ y) , (λ r → eq-is-prop (p y)))

  abstract
    is-torsorial-prop-in-based-id : is-torsorial R
    is-torsorial-prop-in-based-id =
      fundamental-theorem-id'
        ( λ y → map-inv-is-equiv (is-equiv-prop-in-based-id y))
        ( λ y → is-equiv-map-inv-is-equiv (is-equiv-prop-in-based-id y))

  abstract
    is-prop-based-Id-prop-in-based-id : (y : A) → is-prop (x ＝ y)
    is-prop-based-Id-prop-in-based-id y =
      is-prop-is-equiv' (is-equiv-prop-in-based-id y) (p y)

module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x = is-equiv-prop-in-based-id x (R x) (p x) (ρ x) (i x)

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x =
      is-prop-based-Id-prop-in-based-id x (R x) (p x) (ρ x) (i x)
```

## Theorem 12.3.5

Any type with decidable equality is a set.

### Proof

Let `A` be a type, and let `d : Π(x, y : A) (x = y) + (x ≠ y)` be the witness that `A` has decidable equality.
Furthermore, let `𝒰` be a universe containing the type `A`.
We will prove that `A` is a set by applying Theorem 12.3.4.

For every `x, y : A`, we first define a type family `R'(x,y) : ((x = y) + (x ≠ y)) → 𝒰` by

```text
  R'(x,y,inl(p)) ≔ unit
  R'(x,y,inr(p)) ≔ empty.
```

Note that `R'(x,y,q)` is a proposition for each `x, y : A` and `q : (x = y) + (x ≠ y)`.
Now we define `R(x,y) ≔ R'(x,y,d(x,y))`.
Then `R` is a reflexive binary relation on `A`, and furthermore each `R(x,y)` is a proposition.
In order to apply Theorem 12.3.4, it therefore it remains to show that `R` implies identity.

Since `R` is defined as an instance of `R'`, it suffices to construct a function

```text
  f(q) : R'(q) → (x = y).
```

for each `q : (x = y) + (x ≠ y)`.
Such a function is defined by

```text
  f(inl(p),r) := p
  f(inr(p),r) := ex-falso(r). ◻
```

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (x ＝ y) → UU lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → UU lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  is-prop-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    is-prop (Eq-has-decidable-equality' x y t)
  is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
  is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  is-prop-Eq-has-decidable-equality :
    (d : has-decidable-equality A)
    {x y : A} → is-prop (Eq-has-decidable-equality d x y)
  is-prop-Eq-has-decidable-equality d {x} {y} =
    is-prop-Eq-has-decidable-equality' x y (d x y)

  refl-Eq-has-decidable-equality :
    (d : has-decidable-equality A) (x : A) →
    Eq-has-decidable-equality d x x
  refl-Eq-has-decidable-equality d x with d x x
  ... | inl α = star
  ... | inr f = f refl

  Eq-has-decidable-equality-eq :
    (d : has-decidable-equality A) {x y : A} →
    x ＝ y → Eq-has-decidable-equality d x y
  Eq-has-decidable-equality-eq d {x} {.x} refl =
    refl-Eq-has-decidable-equality d x

  eq-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    Eq-has-decidable-equality' x y t → x ＝ y
  eq-Eq-has-decidable-equality' x y (inl p) t = p
  eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  eq-Eq-has-decidable-equality :
    (d : has-decidable-equality A) {x y : A} →
    Eq-has-decidable-equality d x y → x ＝ y
  eq-Eq-has-decidable-equality d {x} {y} =
    eq-Eq-has-decidable-equality' x y (d x y)

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)
```

## Supplementary definitions

### The type of natural numbers is a set

```agda
abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : Set lzero
pr1 ℕ-Set = ℕ
pr2 ℕ-Set = is-set-ℕ
```
