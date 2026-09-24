# Section 12.3 Sets

```agda
module section-12-3-sets where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
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

## Supplement

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

### The empty type is a set

```agda
is-set-empty : is-set empty
is-set-empty ()

empty-Set : Set lzero
pr1 empty-Set = empty
pr2 empty-Set = is-set-empty
```

### Unit laws

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) (e : A)
  where

  left-unit-law : UU l
  left-unit-law = (x : A) → μ e x ＝ x

  right-unit-law : UU l
  right-unit-law = (x : A) → μ x e ＝ x

  coh-unit-laws : left-unit-law → right-unit-law → UU l
  coh-unit-laws α β = (α e ＝ β e)

  unit-laws : UU l
  unit-laws = left-unit-law × right-unit-law

  coherent-unit-laws : UU l
  coherent-unit-laws =
    Σ left-unit-law (λ α → Σ right-unit-law (coh-unit-laws α))
```

### Unital binary operations

```agda
is-unital : {l : Level} {A : UU l} (μ : A → A → A) → UU l
is-unital {A = A} μ = Σ A (unit-laws μ)
```

### Semirings

```agda
has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul X =
  Σ (X → X → X) (λ μ → (x y z : X) → μ (μ x y) z ＝ μ x (μ y z))

has-associative-mul-Set :
  {l : Level} (X : Set l) → UU l
has-associative-mul-Set X =
  has-associative-mul (type-Set X)

Semigroup :
  (l : Level) → UU (lsuc l)
Semigroup l = Σ (Set l) has-associative-mul-Set

module _
  {l : Level} (G : Semigroup l)
  where

  set-Semigroup : Set l
  set-Semigroup = pr1 G

  type-Semigroup : UU l
  type-Semigroup = type-Set set-Semigroup

  is-set-type-Semigroup : is-set type-Semigroup
  is-set-type-Semigroup = is-set-type-Set set-Semigroup

  has-associative-mul-Semigroup : has-associative-mul type-Semigroup
  has-associative-mul-Semigroup = pr2 G

  mul-Semigroup : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup = pr1 has-associative-mul-Semigroup

  mul-Semigroup' : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup' x y = mul-Semigroup y x

  ap-mul-Semigroup :
    {x x' y y' : type-Semigroup} →
    x ＝ x' → y ＝ y' → mul-Semigroup x y ＝ mul-Semigroup x' y'
  ap-mul-Semigroup p q = ap-binary mul-Semigroup p q

  associative-mul-Semigroup :
    (x y z : type-Semigroup) →
    mul-Semigroup (mul-Semigroup x y) z ＝ mul-Semigroup x (mul-Semigroup y z)
  associative-mul-Semigroup =
    pr2 has-associative-mul-Semigroup

  inv-associative-mul-Semigroup :
    (x y z : type-Semigroup) →
    mul-Semigroup x (mul-Semigroup y z) ＝
    mul-Semigroup (mul-Semigroup x y) z
  inv-associative-mul-Semigroup x y z =
    inv (associative-mul-Semigroup x y z)

  left-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup x y ＝ mul-Semigroup y x →
    mul-Semigroup x (mul-Semigroup y z) ＝
    mul-Semigroup y (mul-Semigroup x z)
  left-swap-mul-Semigroup H =
    ( inv (associative-mul-Semigroup _ _ _)) ∙
    ( ap (mul-Semigroup' _) H) ∙
    ( associative-mul-Semigroup _ _ _)

  right-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) z ＝
    mul-Semigroup (mul-Semigroup x z) y
  right-swap-mul-Semigroup H =
    ( associative-mul-Semigroup _ _ _) ∙
    ( ap (mul-Semigroup _) H) ∙
    ( inv (associative-mul-Semigroup _ _ _))

  interchange-mul-mul-Semigroup :
    {x y z w : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) (mul-Semigroup z w) ＝
    mul-Semigroup (mul-Semigroup x z) (mul-Semigroup y w)
  interchange-mul-mul-Semigroup H =
    ( associative-mul-Semigroup _ _ _) ∙
    ( ap (mul-Semigroup _) (left-swap-mul-Semigroup H)) ∙
    ( inv (associative-mul-Semigroup _ _ _))
```

### Monoids

```agda
is-unital-Semigroup :
  {l : Level} → Semigroup l → UU l
is-unital-Semigroup G = is-unital (mul-Semigroup G)

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semigroup l) is-unital-Semigroup

module _
  {l : Level} (M : Monoid l)
  where

  semigroup-Monoid : Semigroup l
  semigroup-Monoid = pr1 M

  is-unital-Monoid : is-unital-Semigroup semigroup-Monoid
  is-unital-Monoid = pr2 M

  type-Monoid : UU l
  type-Monoid = type-Semigroup semigroup-Monoid

  set-Monoid : Set l
  set-Monoid = set-Semigroup semigroup-Monoid

  is-set-type-Monoid : is-set type-Monoid
  is-set-type-Monoid = is-set-type-Semigroup semigroup-Monoid

  mul-Monoid : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid = mul-Semigroup semigroup-Monoid

  mul-Monoid' : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid' y x = mul-Monoid x y

  ap-mul-Monoid :
    {x x' y y' : type-Monoid} →
    x ＝ x' → y ＝ y' → mul-Monoid x y ＝ mul-Monoid x' y'
  ap-mul-Monoid = ap-mul-Semigroup semigroup-Monoid

  associative-mul-Monoid :
    (x y z : type-Monoid) →
    mul-Monoid (mul-Monoid x y) z ＝ mul-Monoid x (mul-Monoid y z)
  associative-mul-Monoid =
    associative-mul-Semigroup semigroup-Monoid

  inv-associative-mul-Monoid :
    (x y z : type-Monoid) →
    mul-Monoid x (mul-Monoid y z) ＝ mul-Monoid (mul-Monoid x y) z
  inv-associative-mul-Monoid =
    inv-associative-mul-Semigroup semigroup-Monoid

  has-unit-Monoid : is-unital mul-Monoid
  has-unit-Monoid = pr2 M

  unit-Monoid : type-Monoid
  unit-Monoid = pr1 has-unit-Monoid

  is-unit-Monoid-Prop : type-Monoid → Prop l
  is-unit-Monoid-Prop x = Id-Prop set-Monoid x unit-Monoid

  is-unit-Monoid : type-Monoid → UU l
  is-unit-Monoid x = x ＝ unit-Monoid

  left-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid unit-Monoid x ＝ x
  left-unit-law-mul-Monoid = pr1 (pr2 has-unit-Monoid)

  right-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid x unit-Monoid ＝ x
  right-unit-law-mul-Monoid = pr2 (pr2 has-unit-Monoid)

  left-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid x y ＝ mul-Monoid y x →
    mul-Monoid x (mul-Monoid y z) ＝
    mul-Monoid y (mul-Monoid x z)
  left-swap-mul-Monoid =
    left-swap-mul-Semigroup semigroup-Monoid

  right-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) z ＝
    mul-Monoid (mul-Monoid x z) y
  right-swap-mul-Monoid =
    right-swap-mul-Semigroup semigroup-Monoid

  interchange-mul-mul-Monoid :
    {x y z w : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) (mul-Monoid z w) ＝
    mul-Monoid (mul-Monoid x z) (mul-Monoid y w)
  interchange-mul-mul-Monoid =
    interchange-mul-mul-Semigroup semigroup-Monoid
```

### The Semigroup of natural numbers

```agda
ℕ-Semigroup : Semigroup lzero
pr1 ℕ-Semigroup = ℕ-Set
pr1 (pr2 ℕ-Semigroup) = add-ℕ
pr2 (pr2 ℕ-Semigroup) = associative-add-ℕ
```

### The monoid of natural numbers

```agda
ℕ-Monoid : Monoid lzero
pr1 ℕ-Monoid = ℕ-Semigroup
pr1 (pr2 ℕ-Monoid) = 0
pr1 (pr2 (pr2 ℕ-Monoid)) = left-unit-law-add-ℕ
pr2 (pr2 (pr2 ℕ-Monoid)) = right-unit-law-add-ℕ
```
