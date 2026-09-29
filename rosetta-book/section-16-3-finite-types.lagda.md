# Section 16.3 Finite types

```agda
module section-16-3-finite-types where

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
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-8-1-decidability-and-decidable-equality
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
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
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-4-coproduct-truncation
open import exercise-12-13-fiber-inclusions-truncated
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-7-universal-property-contractible-types
open import exercise-13-8-universal-property-coproducts
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-14-4-mapping-propositional-truncations-into-sets
open import exercise-14-3-products-of-propositional-truncations
open import exercise-14-5-propositional-truncations-with-sections
open import section-16-1-counting-in-type-theory
open import section-16-2-double-counting-in-type-theory
```

The type of all finite types is the subtype of the base universe `𝒰₀` consisting of all types `X` for which there exists an unspecified equivalence `Fin_{k} ≃ X` for some `k : ℕ`.

## Definition 16.3.1

A type `X` is said to be **finite** if it comes equipped with an element of type

```text
  is-finite(X) ≔ ‖Σ(k : ℕ) Fin_{k} ≃ X‖
```

The type `𝔽` of all finite types is defined to be

```text
  𝔽 ≔ Σ(X : 𝒰₀) is-finite(X).
```

```agda
is-finite-Prop :
  {l : Level} → UU l → Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

abstract
  is-prop-is-finite :
    {l : Level} (X : UU l) → is-prop (is-finite X)
  is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

abstract
  is-finite-count :
    {l : Level} {X : UU l} → count X → is-finite X
  is-finite-count = unit-trunc-Prop

Finite-Type : (l : Level) → UU (lsuc l)
Finite-Type l = Σ (UU l) is-finite

type-Finite-Type : {l : Level} → Finite-Type l → UU l
type-Finite-Type = pr1

is-finite-type-Finite-Type :
  {l : Level} (X : Finite-Type l) → is-finite (type-Finite-Type X)
is-finite-type-Finite-Type = pr2
```


In other words, the type `𝔽` of finite types is the image of the map `Fin : ℕ → 𝒰₀`.
We also define the type `BS_k` of **`k`-element types** by

```text
  BS_k ≔ Σ(X : 𝒰₀) ‖Fin_{k} ≃ X‖.
```

```agda
mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

abstract
  is-prop-mere-equiv :
    {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
  is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)

abstract
  refl-mere-equiv : {l1 : Level} → is-reflexive (mere-equiv {l1})
  refl-mere-equiv X = unit-trunc-Prop id-equiv

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-trunc-mere-equiv : (k : 𝕋) → mere-equiv X Y → is-trunc k Y → is-trunc k X
  is-trunc-mere-equiv k e H =
    apply-universal-property-trunc-Prop
      ( e)
      ( is-trunc-Prop k X)
      ( λ f → is-trunc-equiv k Y f H)

  is-trunc-mere-equiv' : (k : 𝕋) → mere-equiv X Y → is-trunc k X → is-trunc k Y
  is-trunc-mere-equiv' k e H =
    apply-universal-property-trunc-Prop
      ( e)
      ( is-trunc-Prop k Y)
      ( λ f → is-trunc-equiv' k X f H)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-set-mere-equiv : mere-equiv X Y → is-set Y → is-set X
  is-set-mere-equiv = is-trunc-mere-equiv zero-𝕋

  is-set-mere-equiv' : mere-equiv X Y → is-set X → is-set Y
  is-set-mere-equiv' = is-trunc-mere-equiv' zero-𝕋

has-cardinality-ℕ-Prop :
  {l : Level} → ℕ → UU l → Prop l
has-cardinality-ℕ-Prop k = mere-equiv-Prop (Fin k)

has-cardinality-ℕ :
  {l : Level} → ℕ → UU l → UU l
has-cardinality-ℕ k = mere-equiv (Fin k)

Type-With-Cardinality-ℕ : (l : Level) → ℕ → UU (lsuc l)
Type-With-Cardinality-ℕ l k = Σ (UU l) (has-cardinality-ℕ k)

type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → Type-With-Cardinality-ℕ l k → UU l
type-Type-With-Cardinality-ℕ k = pr1

abstract
  has-cardinality-type-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
    mere-equiv (Fin k) (type-Type-With-Cardinality-ℕ k X)
  has-cardinality-type-Type-With-Cardinality-ℕ k = pr2

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (λ k → has-cardinality-ℕ k X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

abstract
  mere-equiv-has-finite-cardinality :
    {l : Level} {X : UU l} (c : has-finite-cardinality X) →
    type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
  mere-equiv-has-finite-cardinality = pr2

eq-cardinality :
  {l1 : Level} {k l : ℕ} {A : UU l1} →
  has-cardinality-ℕ k A → has-cardinality-ℕ l A → k ＝ l
eq-cardinality H K =
  apply-twice-universal-property-trunc-Prop H K
    ( Id-Prop ℕ-Set _ _)
    ( λ e f → is-equivalence-injective-Fin (inv-equiv f ∘e e))
```


## Remark 16.3.2

It follows directly from the definition of finiteness that any type `X` equipped with a counting is finite.
In particular, any `Fin_{k}` is finite.
Furthermore, it follows that if `X` is equivalent to a finite type `Y`, then `X` is also finite.
Indeed, we can use the functoriality of the propositional truncation to obtain a function

```text
  ‖Σ(k : ℕ) Fin_{k} ≃ Y‖ → ‖Σ(k : ℕ) Fin_{k} ≃ X‖
```

from a map `(Σ(k : ℕ) Fin_{k} ≃ Y) → (Σ(k : ℕ) Fin_{k} ≃ X)`.
Given an equivalence `e : X ≃ Y`, such a map is given as the map induced on total spaces from the family of maps `f ↦ e⁻¹ ∘ f`.

```agda
abstract
  is-finite-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite A → is-finite B
  is-finite-equiv e =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv e))

abstract
  is-finite-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-finite A → is-finite B
  is-finite-is-equiv is-equiv-f =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

abstract
  is-finite-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite B → is-finite A
  is-finite-equiv' e = is-finite-equiv (inv-equiv e)

abstract
  is-finite-mere-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-finite A → is-finite B
  is-finite-mere-equiv e H =
    apply-universal-property-trunc-Prop e
      ( is-finite-Prop _)
      ( λ e' → is-finite-equiv e' H)

abstract
  is-finite-empty : is-finite empty
  is-finite-empty = is-finite-count count-empty

empty-Finite-Type : Finite-Type lzero
pr1 empty-Finite-Type = empty
pr2 empty-Finite-Type = is-finite-empty

empty-Type-With-Cardinality-ℕ : Type-With-Cardinality-ℕ lzero zero-ℕ
pr1 empty-Type-With-Cardinality-ℕ = empty
pr2 empty-Type-With-Cardinality-ℕ = unit-trunc-Prop id-equiv

has-finite-cardinality-empty : has-finite-cardinality empty
pr1 has-finite-cardinality-empty = zero-ℕ
pr2 has-finite-cardinality-empty = unit-trunc-Prop id-equiv

abstract
  is-finite-is-empty :
    {l1 : Level} {X : UU l1} → is-empty X → is-finite X
  is-finite-is-empty H = is-finite-count (count-is-empty H)

has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
pr1 (has-finite-cardinality-is-empty f) = zero-ℕ
pr2 (has-finite-cardinality-is-empty f) =
  unit-trunc-Prop (equiv-count (count-is-empty f))

abstract
  is-finite-unit : is-finite unit
  is-finite-unit = is-finite-count count-unit

unit-Finite-Type : Finite-Type lzero
pr1 unit-Finite-Type = unit
pr2 unit-Finite-Type = is-finite-unit

unit-Type-With-Cardinality-ℕ : Type-With-Cardinality-ℕ lzero 1
pr1 unit-Type-With-Cardinality-ℕ = unit
pr2 unit-Type-With-Cardinality-ℕ =
  unit-trunc-Prop (left-unit-law-coproduct unit)

abstract
  is-finite-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → is-finite X
  is-finite-is-contr H = is-finite-count (count-is-contr H)

abstract
  has-cardinality-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → has-cardinality-ℕ 1 X
  has-cardinality-is-contr H =
    unit-trunc-Prop (equiv-is-contr is-contr-Fin-1 H)

abstract
  is-finite-Fin : (k : ℕ) → is-finite (Fin k)
  is-finite-Fin k = is-finite-count (count-Fin k)

Fin-Finite-Type : ℕ → Finite-Type lzero
pr1 (Fin-Finite-Type k) = Fin k
pr2 (Fin-Finite-Type k) = is-finite-Fin k

Fin-Type-With-Cardinality-ℕ :
  (k : ℕ) → Type-With-Cardinality-ℕ lzero k
pr1 (Fin-Type-With-Cardinality-ℕ k) = Fin k
pr2 (Fin-Type-With-Cardinality-ℕ k) = unit-trunc-Prop id-equiv
```

Similarly, it follows that any finite type has decidable equality, and that every finite type is a set.

```agda
has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv'
        ( equiv-count e)
        ( has-decidable-equality-Fin (number-of-elements-count e)))

has-decidable-equality-has-cardinality-ℕ :
  {l1 : Level} {X : UU l1} (k : ℕ) →
  has-cardinality-ℕ k X → has-decidable-equality X
has-decidable-equality-has-cardinality-ℕ {l1} {X} k H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e (has-decidable-equality-Fin k))

abstract
  is-finite-eq :
    {l : Level} {X : UU l} →
    has-decidable-equality X → {x y : X} → is-finite (x ＝ y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

is-finite-eq-is-finite :
    {l : Level} {X : UU l} → is-finite X → {x y : X} → is-finite (x ＝ y)
is-finite-eq-is-finite H = is-finite-eq (has-decidable-equality-is-finite H)

is-finite-eq-Finite-Type :
  {l : Level} → (X : Finite-Type l)
  {x y : type-Finite-Type X} → is-finite (x ＝ y)
is-finite-eq-Finite-Type X =
  is-finite-eq-is-finite (is-finite-type-Finite-Type X)

Id-Finite-Type :
  {l : Level} → (X : Finite-Type l) (x y : type-Finite-Type X) → Finite-Type l
pr1 (Id-Finite-Type X x y) = x ＝ y
pr2 (Id-Finite-Type X x y) = is-finite-eq-Finite-Type X

abstract
  is-set-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-set X
  is-set-is-finite {l} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-set-Prop X)
      ( λ e → is-set-type-count e)

is-set-type-Finite-Type :
  {l : Level} (X : Finite-Type l) → is-set (type-Finite-Type X)
is-set-type-Finite-Type X = is-set-is-finite (is-finite-type-Finite-Type X)

set-Finite-Type : {l : Level} → Finite-Type l → Set l
pr1 (set-Finite-Type X) = type-Finite-Type X
pr2 (set-Finite-Type X) = is-set-is-finite (is-finite-type-Finite-Type X)

is-set-has-cardinality-ℕ :
  {l1 : Level} {X : UU l1} (k : ℕ) → has-cardinality-ℕ k X → is-set X
is-set-has-cardinality-ℕ k H = is-set-mere-equiv' H (is-set-Fin k)

is-set-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
  is-set (type-Type-With-Cardinality-ℕ k X)
is-set-type-Type-With-Cardinality-ℕ k X =
  is-set-has-cardinality-ℕ k
    ( has-cardinality-type-Type-With-Cardinality-ℕ k X)

set-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ) → Type-With-Cardinality-ℕ l1 k → Set l1
pr1 (set-Type-With-Cardinality-ℕ k X) =
  type-Type-With-Cardinality-ℕ k X
pr2 (set-Type-With-Cardinality-ℕ k X) =
  is-set-type-Type-With-Cardinality-ℕ k X
```

In the following proposition we will show that each finite type can be assigned a unique cardinality.

## Theorem 16.3.3

For any type `X`, consider the type `is-finite'(X)` defined by

```text
  is-finite'(X) ≔ Σ(k : ℕ) ‖Fin_{k} ≃ X‖.
```

Then the type `is-finite'(X)` is a proposition, and there is an equivalence

```text
  is-finite(X) ↔ is-finite'(X).
```

If `X` is a finite type, then the unique number `k` such that `‖Fin_{k} ≃ X‖` is the **cardinality** of `X`.
We write `|X|` for the cardinality of `X`.

### Proof

We first prove the claim that the type `is-finite'(X)` is a proposition.
In other words, we need to show that any two natural numbers `k` and `k'` for which there are respective elements of the types `‖Fin_{k} ≃ X‖` and `‖Fin_{k'} ≃ X‖`, can be identified.

Since the type of natural numbers is a set, the type `k = k'` is a proposition.
Therefore, we may assume that we have equivalences `Fin_{k} ≃ X` and `Fin_{k'} ≃ X`.
Consequently, we have an equivalence `Fin_{k} ≃ Fin_{k'}`.
Now it follows from Theorem 16.2.2 that `k = k'`.

The second claim is that the propositions `is-finite(X)` and `is-finite'(X)` are equivalent, which we will show by constructing functions back and forth.
Since we have shown that the type `is-finite'(X)` is a proposition, we obtain a map `is-finite(X) → is-finite'(X)` via the universal property of the propositional truncation, from the map

```text
  (Σ(k : ℕ) Fin_{k} ≃ X) → Σ(k : ℕ) ‖Fin_{k} ≃ X‖
```

given by `(k,e) ↦ (k,η(e))`.

To construct a map `is-finite'(X) → is-finite(X)`, it suffices to construct a map

```text
  ‖Fin_{k'} ≃ X‖ → ‖Σ(k : ℕ) Fin_{k} ≃ X‖
```

for each `k' : ℕ`.
Again by the universal property of the propositional truncation, we obtain this map from the function

```text
  (Fin_{k'} ≃ X) → ‖Σ(k : ℕ) Fin_{k} ≃ X‖
```

given by `e ↦ η(k',e)`. ◻

```agda
abstract
  is-finite-type-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
    is-finite (type-Type-With-Cardinality-ℕ k X)
  is-finite-type-Type-With-Cardinality-ℕ k X =
    is-finite-mere-equiv
      ( has-cardinality-type-Type-With-Cardinality-ℕ k X)
      ( is-finite-Fin k)

finite-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → Type-With-Cardinality-ℕ l k → Finite-Type l
pr1 (finite-type-Type-With-Cardinality-ℕ k X) =
  type-Type-With-Cardinality-ℕ k X
pr2 (finite-type-Type-With-Cardinality-ℕ k X) =
  is-finite-type-Type-With-Cardinality-ℕ k X

abstract
  all-elements-equal-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
  all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
    eq-type-subtype
      ( λ k → mere-equiv-Prop (Fin k) X)
      ( apply-twice-universal-property-trunc-Prop K L
        ( Id-Prop ℕ-Set k l)
        ( λ (e : Fin k ≃ X) (f : Fin l ≃ X) →
          is-equivalence-injective-Fin (inv-equiv f ∘e e)))

abstract
  is-prop-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
  is-prop-has-finite-cardinality =
    is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → Prop l1
pr1 (has-finite-cardinality-Prop X) = has-finite-cardinality X
pr2 (has-finite-cardinality-Prop X) = is-prop-has-finite-cardinality

module _
  {l : Level} {X : UU l}
  where

  abstract
    is-finite-has-finite-cardinality : has-finite-cardinality X → is-finite X
    is-finite-has-finite-cardinality (pair k K) =
      apply-universal-property-trunc-Prop K
        ( is-finite-Prop X)
        ( is-finite-count ∘ pair k)

  abstract
    is-finite-has-cardinality-ℕ : (k : ℕ) → has-cardinality-ℕ k X → is-finite X
    is-finite-has-cardinality-ℕ k H =
      is-finite-has-finite-cardinality (pair k H)

  has-finite-cardinality-count : count X → has-finite-cardinality X
  pr1 (has-finite-cardinality-count e) = number-of-elements-count e
  pr2 (has-finite-cardinality-count e) = unit-trunc-Prop (equiv-count e)

  abstract
    has-finite-cardinality-is-finite : is-finite X → has-finite-cardinality X
    has-finite-cardinality-is-finite =
      map-universal-property-trunc-Prop
        ( has-finite-cardinality-Prop X)
        ( has-finite-cardinality-count)

  number-of-elements-is-finite : is-finite X → ℕ
  number-of-elements-is-finite =
    number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

  abstract
    mere-equiv-is-finite :
      (f : is-finite X) → mere-equiv (Fin (number-of-elements-is-finite f)) X
    mere-equiv-is-finite f =
      mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

  abstract
    compute-number-of-elements-is-finite :
      (e : count X) (f : is-finite X) →
      number-of-elements-count e ＝ number-of-elements-is-finite f
    compute-number-of-elements-is-finite e f =
      ind-trunc-Prop
        ( λ g →
          Id-Prop ℕ-Set
            ( number-of-elements-count e)
            ( number-of-elements-is-finite g))
        ( λ g →
          ( is-equivalence-injective-Fin
            ( inv-equiv (equiv-count g) ∘e equiv-count e)) ∙
          ( ap pr1
            ( eq-is-prop' is-prop-has-finite-cardinality
              ( has-finite-cardinality-count g)
              ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
        ( f)

  has-cardinality-is-finite :
    (H : is-finite X) → has-cardinality-ℕ (number-of-elements-is-finite H) X
  has-cardinality-is-finite H =
    pr2 (has-finite-cardinality-is-finite H)

number-of-elements-Finite-Type : {l : Level} → Finite-Type l → ℕ
number-of-elements-Finite-Type X =
  number-of-elements-is-finite (is-finite-type-Finite-Type X)

type-with-cardinality-Finite-Type :
  {l : Level} (X : Finite-Type l) →
  Type-With-Cardinality-ℕ l (number-of-elements-Finite-Type X)
type-with-cardinality-Finite-Type (X , is-finite-X) =
  ( X , has-cardinality-is-finite is-finite-X)
```

## Corollary 16.3.4

There is an equivalence

```text
  𝔽 ≃ Σ(k : ℕ) BS_k.
```

### Proof

*Proof.* This equivalence can be obtained by composing the equivalences
```text
Σ(X:𝒰₀) is-finite(X) ≃ Σ(X:𝒰₀) Σ(k:ℕ) ‖Fin_{k}≃ X‖
≃ Σ(k:ℕ) Σ(X:𝒰₀) ‖Fin_{k}≃ X‖.
```
 ◻

```agda
map-compute-total-Type-With-Cardinality-ℕ :
  {l : Level} → Σ ℕ (Type-With-Cardinality-ℕ l) → Finite-Type l
pr1 (map-compute-total-Type-With-Cardinality-ℕ (pair k (pair X e))) = X
pr2 (map-compute-total-Type-With-Cardinality-ℕ (pair k (pair X e))) =
  is-finite-has-finite-cardinality (pair k e)

compute-total-Type-With-Cardinality-ℕ :
  {l : Level} → Σ ℕ (Type-With-Cardinality-ℕ l) ≃ Finite-Type l
compute-total-Type-With-Cardinality-ℕ =
  ( equiv-tot
    ( λ X →
      equiv-iff-is-prop
        ( is-prop-has-finite-cardinality)
        ( is-prop-is-finite X)
        ( is-finite-has-finite-cardinality)
        ( has-finite-cardinality-is-finite))) ∘e
  ( equiv-left-swap-Σ)
```

We now aim to extend Theorem 16.1.7 to obtain some closure properties of finite types.
Before we do so, we prove the **principle of finite choice**.

## Proposition 16.3.5

Consider a type family `B` over a finite type `A`.
Then there is a **finite choice** map
```text
(Π(x:A) ‖B(x)‖)→‖Π(x:A) B(x)‖
```

### Proof

*Proof.* Note that the type `‖Π(x:A) B(x)‖` is a proposition.
Therefore we may assume that the type `A` comes equipped with a counting `e:Fin_{k}≃ A`.
By this equivalence, it suffices to show that for every type family `B` over `Fin_{k}`, there is a map
```text
(Π(x:Fin_{k}) ‖B(x)‖)→‖Π(x:Fin_{k}) B(x)‖.
```
We proceed by induction on `k`.
In the base case, `Fin_{k}` is empty and therefore the type `Π(x:Fin_{k}) B(x)` is contractible.
The asserted function therefore exists.

For the inductive step, note that by the dependent universal property of coproducts (Exercise 13.8) we have the equivalences
```text
(Π(x:Fin_{k+1}) ‖B(x)‖) ≃ (Π(x:Fin_{k}) ‖B(i(x))‖)× ‖B(⋆)‖
‖Π(x:Fin_{k}) B(x)‖ ≃ ‖(Π(x:Fin_{k}) B(i(x)))× B(⋆)‖.
```
Recall from Exercise 14.3 that `‖X× Y‖≃ ‖X‖×‖Y‖` for any two types `X` and `Y`.
This fact together with the inductive hypothesis finishes the proof. ◻

```agda
abstract
  finite-choice-Fin :
    {l1 : Level} (k : ℕ) {Y : Fin k → UU l1} →
    ((x : Fin k) → is-inhabited (Y x)) → is-inhabited ((x : Fin k) → Y x)
  finite-choice-Fin 0 H = unit-trunc-Prop ind-empty
  finite-choice-Fin (succ-ℕ k) {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coproduct Y)
      ( map-inv-distributive-trunc-product-Prop
        ( pair
          ( finite-choice-Fin k (λ x → H (inl x)))
          ( map-inv-equiv-trunc-Prop
            ( equiv-dependent-universal-property-unit (Y ∘ inr))
            ( H (inr star)))))

module _
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  where

  abstract
    finite-choice-count :
      count X →
      ((x : X) → is-inhabited (Y x)) → is-inhabited ((x : X) → Y x)
    finite-choice-count (k , e) H =
      map-inv-equiv-trunc-Prop
        ( equiv-precomp-Π e Y)
        ( finite-choice-Fin k (H ∘ map-equiv e))

  abstract
    finite-choice :
      is-finite X →
      ((x : X) → is-inhabited (Y x)) → is-inhabited ((x : X) → Y x)
    finite-choice is-finite-X H =
      apply-universal-property-trunc-Prop is-finite-X
        ( trunc-Prop ((x : X) → Y x))
        ( λ e → finite-choice-count e H)

ε-operator-count :
  {l : Level} {A : UU l} → count A → ε-operator-Hilbert A
ε-operator-count (0 , e) t =
  ex-falso
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (0 , e) refl)
      ( t))
ε-operator-count (succ-ℕ k , e) t = map-equiv e (zero-Fin k)

abstract
  ε-operator-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : decidable-subtype l2 A) →
    ε-operator-Hilbert (type-decidable-subtype P)
  ε-operator-decidable-subtype-count e P =
    ε-operator-equiv
      ( equiv-Σ-equiv-base (is-in-decidable-subtype P) (equiv-count e))
      ( ε-operator-decidable-subtype-Fin
        ( number-of-elements-count e)
        ( P ∘ map-equiv-count e))

count-type-subtype-is-finite-type-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : subtype l2 A) →
  is-finite (type-subtype P) → count (type-subtype P)
count-type-subtype-is-finite-type-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype
    ( λ x → pair (type-Prop (P x)) (pair (is-prop-type-Prop (P x)) (d x)))
    ( e)
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-subtype P e g x)

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fiber (map-emb f))
    ( count-type-subtype-is-finite-type-subtype e
      ( λ x → pair (fiber (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fiber (map-emb f))
        ( H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    choice-count-Σ-is-finite-fiber :
      is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
      ((x : A) → is-inhabited (B x)) → (x : A) → B x
    choice-count-Σ-is-finite-fiber K e g H x =
      ε-operator-count
        ( count-domain-emb-is-finite-domain-emb e
          ( fiber-inclusion-emb (A , K) B x)
          ( g x))
        ( H x)

  abstract
    choice-is-finite-Σ-is-finite-fiber :
      is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
      ((x : A) → is-inhabited (B x)) → is-inhabited ((x : A) → B x)
    choice-is-finite-Σ-is-finite-fiber K f g H =
      apply-universal-property-trunc-Prop f
        ( trunc-Prop ((x : A) → B x))
        ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))
```

## Theorem 16.3.6

1. For any two types `X` and `Y`, the following are equivalent:

    1. Both `X` and `Y` are finite.

    2. The coproduct `X+Y` is finite.

2. For any two types `X` and `Y`, we make two claims:

    1. If both `X` and `Y` are finite, then the cartesian product `X× Y` is finite.

    2. If the type `X× Y` is finite, then we have two functions
```text
Y → is-finite(X)
X → is-finite(Y).
```

3. Consider a type family `B` over `A`, and consider the following three conditions:

    1. The type `A` is finite.

    2. The type `B(x)` is finite for each `x:A`.

    3. The type `Σ(x:A) B(x)` is finite.

If (a) holds, then (b) is equivalent to (c).
Moreover, if (b) and (c) hold, then (a) holds if and only if `A` is a set and the type `Σ(x:A) ¬ B(x)` is finite.
Furthermore, if (b) and (c) hold and `B` has a section, then (a) holds.

### Proof

*Proof.* To prove claim Theorem 16.3.6, first suppose that both `X` and `Y` are finite.
Since the type `is-finite(X+Y)` is a proposition, we may assume that `X` and `Y` come equipped with countings.
It follows from Theorem 16.1.7 that `X+Y` has a counting, so it is finite.
Conversely, suppose that the type `X+Y` is finite.
Since the types `is-finite(X)` and `is-finite(Y)` are both propositions, we may assume that the coproduct `X+Y` comes equipped with a counting.
Again it follows from Theorem 16.1.7 that the types `X` and `Y` have countings, so they are finite.

The proof of claim (2) is similar to the proof of claim Theorem 16.3.6, hence we omit it.

It remains to prove claim (3).
First, suppose that the type `A` is finite, and that each `B(x)` is finite.
By Proposition 16.3.5 we have a map
```text
(Π(x:A) is-finite(B(x)))→ ‖Π(x:A) count(B(x))‖.
```
Since our goal is to construct an element of a proposition, we may therefore assume that each `B(x)` comes equipped with a counting.
We may also assume that `A` comes equipped with a counting.
It follows from Theorem 16.1.7 that the type `Σ(x:A) B(x)` has a counting, so it is finite.

Next, assume that `A` is finite and that the type `Σ(x:A) B(x)` is finite, and let `a:A`.
The type `is-finite(B(a))` is a proposition, so we may assume that the types `A` and `Σ(x:A) B(x)` come equipped with countings.
It follows from Theorem 16.1.7 that `B(a)` has a counting, so it is finite.

The final claim has two parts.
First, assume that each `B(x)` is finite, that the type `Σ(x:A) B(x)` is finite, and that the type family `B` has a section `f:Π(x:A) B(x)`.
It follows that the map
```text
A→Σ(x:A) B(x)
```
given by `x↦ (x,f(x))` is a decidable embedding, because the fiber at `(x,y)` of this map is equivalent to the identity type `f(x)=y` in `B(x)`, which is a decidable proposition.
It follows from the fact that (a) and (b) together imply (c) that `A` is finite.

For the remaining part of the final claim, assume that `A` is a set.
Note that the assumption that each `B(x)` is finite implies that each `B(x)` is either inhabited or empty.
It follows that we have an equivalence
```text
A≃ (Σ(x:A) ‖B(x)‖)+(Σ(x:A) ¬ B(x)).
```
We assume that the type `Σ(x:A) ¬ B(x)` is finite.
In order to show that `A` is finite, it therefore suffices to show that the type `Σ(x:A) ‖B(x)‖` is finite.
Without loss of generality, we assume that each `B(x)` is inhabited.
To finish the proof, it suffices to show that there is an element of type
```text
‖Π(x:A) B(x)‖
```
using the assumption that `Π(x:A) ‖B(x)‖`.
To construct such an element, we may assume a counting `e:Fin_{k}≃Σ(x:A) B(x)`.
We claim that there is a function
```text
‖B(a)‖→ B(a),
```
i.e., that the type `B(a)` satisfies the principle of global choice of Remark 14.4.2 for each `a:A`.
Recall from Example 14.4.1 that the decidable subtypes of `Fin_{k}` satisfy global choice.
Therefore it also follows that the decidable subtypes of `Σ(x:A) B(x)` satisfy global choice.
Thus, it suffices to show that `B(x)` is a decidable subtype of `Σ(x:A) B(x)`.

The assumption that `A` is a set implies by Exercise 12.13 that the fiber inclusion `i_a:B(a)→Σ(x:A) B(x)` is an embedding for each `a:A`.
Furthermore, we note that we have the following equivalence computing the fibers of `i_a` at `(x,y)`:
```text
(Σ(z:B(a)) (a,z)=(x,y))≃ (a=x).
```
The type on the left hand side is decidable, so it follows that the type `A` has decidable equality.
We conclude that each `B(a)` is a decidable subtype of `Σ(x:A) B(x)`. ◻

```agda
abstract
  is-finite-coproduct :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X + Y)
  is-finite-coproduct {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X + Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X + Y))
          ( is-finite-count ∘ (count-coproduct e)))

coproduct-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (coproduct-Finite-Type X Y) = (type-Finite-Type X) + (type-Finite-Type Y)
pr2 (coproduct-Finite-Type X Y) =
  is-finite-coproduct
    ( is-finite-type-Finite-Type X)
    ( is-finite-type-Finite-Type Y)

abstract
  is-finite-left-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (X + Y) →
    is-finite X
  is-finite-left-summand =
    map-trunc-Prop count-left-summand

abstract
  is-finite-right-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (X + Y) →
    is-finite Y
  is-finite-right-summand =
    map-trunc-Prop count-right-summand

coproduct-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k l : ℕ) →
  Type-With-Cardinality-ℕ l1 k → Type-With-Cardinality-ℕ l2 l →
  Type-With-Cardinality-ℕ (l1 ⊔ l2) (k +ℕ l)
pr1 (coproduct-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  X + Y
pr2 (coproduct-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coproduct e1 e2 ∘e inv-equiv (compute-coproduct-Fin k l))))

coproduct-eq-is-finite :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (P : is-finite X) (Q : is-finite Y) →
    number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q ＝
    number-of-elements-is-finite (is-finite-coproduct P Q)
coproduct-eq-is-finite {X = X} {Y = Y} P Q =
  ap
    ( number-of-elements-has-finite-cardinality)
    ( all-elements-equal-has-finite-cardinality
      ( pair
        ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
        ( has-cardinality-type-Type-With-Cardinality-ℕ
          ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
          ( coproduct-Type-With-Cardinality-ℕ
            ( number-of-elements-is-finite P)
            ( number-of-elements-is-finite Q)
            ( pair X
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite P)))
            ( pair Y
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite Q))))))
      ( has-finite-cardinality-is-finite (is-finite-coproduct P Q)))

abstract
  is-finite-product :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-product {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X × Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X × Y))
          ( is-finite-count ∘ (count-product e)))

product-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (product-Finite-Type X Y) = (type-Finite-Type X) × (type-Finite-Type Y)
pr2 (product-Finite-Type X Y) =
  is-finite-product
    ( is-finite-type-Finite-Type X)
    ( is-finite-type-Finite-Type Y)

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y =
    map-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    map-trunc-Prop (λ e → count-right-factor e x) f

product-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k l : ℕ) →
  Type-With-Cardinality-ℕ l1 k → Type-With-Cardinality-ℕ l2 l →
  Type-With-Cardinality-ℕ (l1 ⊔ l2) (k *ℕ l)
pr1 (product-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) = X × Y
pr2 (product-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k *ℕ l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k *ℕ l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-product e1 e2 ∘e inv-equiv (product-Fin k l))))

abstract
  is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((a : A) → is-finite (B a)) → is-finite (Σ A B)
  is-finite-Σ {A = A} {B} H K =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop (Σ A B))
      ( λ (e : count A) →
        apply-universal-property-trunc-Prop
          ( finite-choice H K)
          ( is-finite-Prop (Σ A B))
          ( is-finite-count ∘ (count-Σ e)))

Σ-Finite-Type :
  {l1 l2 : Level}
  (A : Finite-Type l1) (B : type-Finite-Type A → Finite-Type l2) →
  Finite-Type (l1 ⊔ l2)
pr1 (Σ-Finite-Type A B) = Σ (type-Finite-Type A) (λ a → type-Finite-Type (B a))
pr2 (Σ-Finite-Type A B) =
  is-finite-Σ
    ( is-finite-type-Finite-Type A)
    ( λ a → is-finite-type-Finite-Type (B a))

abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → is-finite (Σ A B) → (a : A) → is-finite (B a)
  is-finite-fiber-is-finite-Σ {l1} {l2} {A} {B} f g a =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop (B a))
      ( λ e → map-trunc-Prop (λ h → count-fiber-count-Σ-count-base e h a) g)

abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop A)
      ( λ e →
        is-finite-count
          ( count-equiv
            ( ( equiv-total-fiber (map-section-family b)) ∘e
              ( equiv-tot
                ( λ t →
                  ( equiv-tot
                    ( λ x → equiv-eq-pair-Σ (map-section-family b x) t)) ∘e
                  ( ( associative-Σ) ∘e
                    ( inv-left-unit-law-Σ-is-contr
                      ( is-torsorial-Id' (pr1 t))
                      ( pair (pr1 t) refl))))))
            ( count-Σ e
              ( λ t →
                count-eq
                  ( has-decidable-equality-is-finite (g (pr1 t)))
                  ( b (pr1 t))
                  ( pr2 t)))))

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop A)
      ( λ b → is-finite-base-is-finite-Σ-section b f g)

abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (a : A) → type-trunc-Prop (B a)) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
    is-finite-base-is-finite-Σ-mere-section
      ( choice-is-finite-Σ-is-finite-fiber K f g b)
      ( f)
      ( g)

is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)

abstract
  is-finite-type-trunc-Prop :
    {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
  is-finite-type-trunc-Prop = map-trunc-Prop count-type-trunc-Prop

trunc-prop-Finite-Type : {l : Level} → Finite-Type l → Finite-Type l
pr1 (trunc-prop-Finite-Type A) = type-trunc-Prop (type-Finite-Type A)
pr2 (trunc-prop-Finite-Type A) =
  is-finite-type-trunc-Prop (is-finite-type-Finite-Type A)

abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (a : A) → is-finite (B a)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-property-is-inhabited-or-empty (B x))
              ( is-inhabited-or-empty-is-finite (g x)))) ∘e
        ( inv-left-distributive-Σ-coproduct))
      ( is-finite-coproduct
        ( is-finite-base-is-finite-Σ-merely-inhabited
          ( is-set-type-subtype (λ x → trunc-Prop _) K)
          ( λ t → pr2 t)
          ( is-finite-equiv
            ( equiv-right-swap-Σ)
            ( is-finite-Σ
              ( f)
              ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
          ( λ x → g (pr1 x)))
        ( h))
```

## Supplement

### A finite type is empty if and only if it has 0 elements

```agda
abstract
  is-empty-is-zero-number-of-elements-is-finite :
    {l1 : Level} {X : UU l1} (f : is-finite X) →
    is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
  is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p =
    apply-universal-property-trunc-Prop f
      ( is-empty-Prop X)
      ( λ e →
        is-empty-is-zero-number-of-elements-count e
          ( compute-number-of-elements-is-finite e f ∙ p))
```

### A finite type is contractible if and only if it has one element

```agda
is-one-number-of-elements-is-finite-is-contr :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-contr X → is-one-ℕ (number-of-elements-is-finite H)
is-one-number-of-elements-is-finite-is-contr H K =
  eq-cardinality
    ( has-cardinality-is-finite H)
    ( has-cardinality-is-contr K)

is-contr-is-one-number-of-elements-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-one-ℕ (number-of-elements-is-finite H) → is-contr X
is-contr-is-one-number-of-elements-is-finite H p =
  apply-universal-property-trunc-Prop H
    ( is-contr-Prop _)
    ( λ e →
      is-contr-equiv'
        ( Fin 1)
        ( ( equiv-count e) ∘e
          ( equiv-tr Fin
            ( inv p ∙ inv (compute-number-of-elements-is-finite e H))))
        ( is-contr-Fin-1))

is-decidable-is-contr-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) → is-decidable (is-contr X)
is-decidable-is-contr-is-finite H =
  is-decidable-iff
    ( is-contr-is-one-number-of-elements-is-finite H)
    ( is-one-number-of-elements-is-finite-is-contr H)
    ( has-decidable-equality-ℕ (number-of-elements-is-finite H) 1)
```
