# Section 14.3 Logic in type theory

```agda
module section-14-3-logic-in-type-theory where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-8-1-decidability-and-decidable-equality
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-7-fibers-of-projections
open import exercise-10-8-fiber-replacement
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-4-coproduct-truncation
open import exercise-12-6-truncated-sigma-types
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-3-universal-properties
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-8-universal-property-coproducts
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
```

In Chapter 7 we interpreted logic in type theory via the Curry-Howard correspondence, which stipulates that disjunction (`∨`) is interpreted by coproducts and the existential quantifier (`∃`) is interpreted by `Σ`-types.
However, when the existential quantifier is interpreted by `Σ`-types, then it is not possible to express certain concepts correctly, such as finiteness of a type or being in the image a map, and therefore we will add a second interpretation of logic in type theory, where logical propositions are interpreted by type theoretic propositions, i.e., the types of truncation level `-1`.

We have seen that the propositions are closed under cartesian products, implication, and dependent products indexed by arbitrary types.
However, they are not closed under coproducts, and if `P` is a family of propositions over a type `A`, then it is not necessarily the case that `Σ(x : A) P(x)` is a proposition.
We will therefore use propositional truncations to interpret disjunctions and existential quantifiers in type theory.

## Definition 14.3.1

Given two propositions `P` and `Q`, we define their **disjunction**

```text
  P ∨ Q ≔ ‖P + Q‖.
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  disjunction-type-Prop : Prop (l1 ⊔ l2)
  disjunction-type-Prop = trunc-Prop (A + B)

  disjunction-type : UU (l1 ⊔ l2)
  disjunction-type = type-Prop disjunction-type-Prop

  is-prop-disjunction-type : is-prop disjunction-type
  is-prop-disjunction-type = is-prop-type-Prop disjunction-type-Prop

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  disjunction-Prop : Prop (l1 ⊔ l2)
  disjunction-Prop = disjunction-type-Prop (type-Prop P) (type-Prop Q)

  type-disjunction-Prop : UU (l1 ⊔ l2)
  type-disjunction-Prop = type-Prop disjunction-Prop

  abstract
    is-prop-disjunction-Prop : is-prop type-disjunction-Prop
    is-prop-disjunction-Prop = is-prop-type-Prop disjunction-Prop

  infixr 10 _∨_
  _∨_ : Prop (l1 ⊔ l2)
  _∨_ = disjunction-Prop
```

## Proposition 14.3.2

Consider two propositions `P` and `Q`.
Then the disjunction `P ∨ Q` comes equipped with maps `i : P → P ∨ Q` and `j : Q → P ∨ Q`.
Moreover, the proposition `P ∨ Q` satisfies the universal property of the disjunction: For any proposition `R`, we have

```text
  (P ∨ Q → R) ↔ ((P → R) × (Q → R)).
```

### Proof

The maps `i` and `j` are defined by

```text
  i ≔ η ∘ inl
  j ≔ η ∘ inr.
```

Now consider the following composition of maps, for an arbitrary proposition `R`:

```text
               - ∘ η                 h ↦ (h ∘ inl, h ∘ inr)
  (P ∨ Q → R) -------> (P + Q -> R) -----------------------> (P → R) × (Q → R)
```

The first map is an equivalence by the universal property of the propositional truncation, and the second map is an equivalence by the universal property of coproducts (Exercise 13.8). ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inl-disjunction : A → disjunction-type A B
  inl-disjunction = unit-trunc-Prop ∘ inl

  inr-disjunction : B → disjunction-type A B
  inr-disjunction = unit-trunc-Prop ∘ inr

ev-disjunction :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (disjunction-type A B → C) → (A → C) × (B → C)
pr1 (ev-disjunction h) = h ∘ inl-disjunction
pr2 (ev-disjunction h) = h ∘ inr-disjunction

universal-property-disjunction-type :
  {l1 l2 l3 : Level} → UU l1 → UU l2 → Prop l3 → UUω
universal-property-disjunction-type A B S =
  {l : Level} (R : Prop l) →
  (type-Prop S → type-Prop R) ↔ ((A → type-Prop R) × (B → type-Prop R))

universal-property-disjunction-Prop :
  {l1 l2 l3 : Level} → Prop l1 → Prop l2 → Prop l3 → UUω
universal-property-disjunction-Prop P Q =
  universal-property-disjunction-type (type-Prop P) (type-Prop Q)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  elim-disjunction' :
    {l : Level} (R : Prop l) →
    (A → type-Prop R) × (B → type-Prop R) →
    disjunction-type A B → type-Prop R
  elim-disjunction' R (f , g) =
    map-universal-property-trunc-Prop R (rec-coproduct f g)

  up-disjunction :
    universal-property-disjunction-type A B (disjunction-type-Prop A B)
  up-disjunction R = ev-disjunction , elim-disjunction' R

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : Prop l3)
  where

  elim-disjunction :
    (A → type-Prop R) → (B → type-Prop R) →
    disjunction-type A B → type-Prop R
  elim-disjunction f g = elim-disjunction' R (f , g)
```

## Definition 14.3.3

Given a family `P` of propositions over a type `A`, we define the **existential quantification**

```text
  ∃_{(x : A)}P(x) ≔ ‖Σ(x : A) P(x)‖.
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  exists-structure-Prop : Prop (l1 ⊔ l2)
  exists-structure-Prop = trunc-Prop (Σ A B)

  exists-structure : UU (l1 ⊔ l2)
  exists-structure = type-Prop exists-structure-Prop

  is-prop-exists-structure : is-prop exists-structure
  is-prop-exists-structure = is-prop-type-Prop exists-structure-Prop

module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  exists-Prop : Prop (l1 ⊔ l2)
  exists-Prop = exists-structure-Prop A (type-Prop ∘ P)

  exists : UU (l1 ⊔ l2)
  exists = type-Prop exists-Prop

  abstract
    is-prop-exists : is-prop exists
    is-prop-exists = is-prop-type-Prop exists-Prop

  ∃ : Prop (l1 ⊔ l2)
  ∃ = exists-Prop

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  intro-exists : (a : A) (b : B a) → exists-structure A B
  intro-exists a b = unit-trunc-Prop (a , b)
```

## Proposition 14.3.4

Consider a family `P` of propositions over a type `A`.
Then the existential quantification `∃_{(x : A)} P(x)` comes equipped with a dependent function

```text
  Π(a : A) (P(a) → ∃_{(x : A)} P(x)).
```

Furthermore, the proposition `∃_{(x : A)} P(x)` satisfies the universal property of the existential quantification: For any proposition `Q`, we have

```text
  ((∃_{(x : A)} P(x)) → Q) ↔ (Π(x : A) P(x) → Q).
```

### Proof

The dependent function `ε : Π(a : A) (P(a) → ∃_{(x : A)} P(x))` is given by `ε(a,p) ≔ η(a,p)`.

Now consider the following composition of maps:

```text
  ((∃_{(x : A)} P(x)) → Q) ---> ((Σ(x : A) P(x)) → Q) ---> ((x : A) → P x → Q)
```

The first map in this composite is an equivalence by the universal property of the propositional truncation, and the second map is an equivalence by the universal property of `Σ`-types (Theorem 13.3.1). ◻

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (S : Prop l3)
  where

  universal-property-exists-structure : UUω
  universal-property-exists-structure =
    {l : Level} (Q : Prop l) →
    (type-Prop S → type-Prop Q) ↔ ((x : A) → B x → type-Prop Q)

module _
  {l1 l2 l3 : Level} (A : UU l1) (P : A → Prop l2) (S : Prop l3)
  where

  universal-property-exists : UUω
  universal-property-exists =
    universal-property-exists-structure A (type-Prop ∘ P) S
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  ev-intro-exists :
    {C : UU l3} → (exists-structure A B → C) → (x : A) → B x → C
  ev-intro-exists H x p = H (intro-exists x p)

  elim-exists :
    (Q : Prop l3) →
    ((x : A) → B x → type-Prop Q) → (exists-structure A B → type-Prop Q)
  elim-exists Q f = map-universal-property-trunc-Prop Q (ind-Σ f)

  abstract
    is-equiv-ev-intro-exists :
      (Q : Prop l3) → is-equiv (ev-intro-exists {type-Prop Q})
    is-equiv-ev-intro-exists Q =
      is-equiv-has-converse
        ( function-Prop (exists-structure A B) Q)
        ( Π-Prop A (λ x → function-Prop (B x) Q))
        ( elim-exists Q)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  up-exists :
    universal-property-exists-structure A B (exists-structure-Prop A B)
  up-exists Q = (ev-intro-exists , elim-exists Q)
```

In the following table we give an overview of the interpretation of the logical connectives using the propositions in type theory.

| logical connective      | interpretation in type theory |
|:------------------------|:------------------------------|
| `⊤`                     | `unit`                        |
| `⊥`                     | `empty`                       |
| `P ⇒ Q`                 | `P → Q`                       |
| `P ∧ Q`                 | `P × Q`                       |
| `P ∨ Q`                 | `‖P + Q‖`                     |
| `P ⇔ Q`                 | `P ↔ Q`                       |
| `∃_{(x : A)} P(x)`      | `‖Σ(x : A) P(x)‖`             |
| `∀_{(x : A)} P(x)`      | `Π(x : A) P(x)`               |

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  conjunction-Prop : Prop (l1 ⊔ l2)
  conjunction-Prop =
    ( type-Prop P × type-Prop Q ,
      is-prop-product (is-prop-type-Prop P) (is-prop-type-Prop Q))

  type-conjunction-Prop : UU (l1 ⊔ l2)
  type-conjunction-Prop = type-Prop conjunction-Prop

  is-prop-conjunction-Prop :
    is-prop type-conjunction-Prop
  is-prop-conjunction-Prop = is-prop-type-Prop conjunction-Prop

  infixr 15 _∧_
  _∧_ : Prop (l1 ⊔ l2)
  _∧_ = conjunction-Prop

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-iff-Prop : UU (l1 ⊔ l2)
  type-iff-Prop = type-Prop P ↔ type-Prop Q

  is-prop-iff-Prop : is-prop type-iff-Prop
  is-prop-iff-Prop =
    is-prop-product
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop P))

  iff-Prop : Prop (l1 ⊔ l2)
  pr1 iff-Prop = type-iff-Prop
  pr2 iff-Prop = is-prop-iff-Prop

  infix 6 _⇔_

  _⇔_ : Prop (l1 ⊔ l2)
  _⇔_ = iff-Prop
```

## Supplement

### The property of a proposition of being decidable

```agda
is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coproduct intro-double-negation is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → Prop l → Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)

is-decidable-type-Prop : {l : Level} → Prop l → UU l
is-decidable-type-Prop P = is-decidable (type-Prop P)
```

### The subuniverse of decidable propositions

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

is-prop-is-decidable-prop :
  {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
is-prop-is-decidable-prop X =
  is-prop-has-element
    ( λ H →
      is-prop-product
        ( is-property-is-prop X)
        ( is-prop-is-decidable (pr1 H)))

is-decidable-prop-Prop :
  {l : Level} (A : UU l) → Prop l
pr1 (is-decidable-prop-Prop A) = is-decidable-prop A
pr2 (is-decidable-prop-Prop A) = is-prop-is-decidable-prop A

module _
  {l : Level} {A : UU l} (H : is-decidable-prop A)
  where

  is-prop-type-is-decidable-prop : is-prop A
  is-prop-type-is-decidable-prop = pr1 H

  is-decidable-type-is-decidable-prop : is-decidable A
  is-decidable-type-is-decidable-prop = pr2 H
```

### Decidable propositions

```agda
Decidable-Prop :
  (l : Level) → UU (lsuc l)
Decidable-Prop l = type-subtype is-decidable-prop-Prop

module _
  {l : Level} (P : Decidable-Prop l)
  where

  prop-Decidable-Prop : Prop l
  prop-Decidable-Prop = tot (λ x → pr1) P

  type-Decidable-Prop : UU l
  type-Decidable-Prop = type-Prop prop-Decidable-Prop

  abstract
    is-prop-type-Decidable-Prop : is-prop type-Decidable-Prop
    is-prop-type-Decidable-Prop = is-prop-type-Prop prop-Decidable-Prop

  is-decidable-Decidable-Prop : is-decidable type-Decidable-Prop
  is-decidable-Decidable-Prop = pr2 (pr2 P)

  is-decidable-prop-type-Decidable-Prop : is-decidable-prop type-Decidable-Prop
  is-decidable-prop-type-Decidable-Prop = pr2 P

  is-decidable-prop-Decidable-Prop : Prop l
  pr1 is-decidable-prop-Decidable-Prop =
    is-decidable type-Decidable-Prop
  pr2 is-decidable-prop-Decidable-Prop =
    is-prop-is-decidable is-prop-type-Decidable-Prop

  set-Decidable-Prop : Set l
  set-Decidable-Prop = set-Prop prop-Decidable-Prop
```

### Decidable subtypes

```agda
is-decidable-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-decidable-subtype-Prop {A = A} P =
  Π-Prop A (λ a → is-decidable-Prop (P a))

is-decidable-subtype : {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-decidable-subtype P = type-Prop (is-decidable-subtype-Prop P)

is-prop-is-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-decidable-subtype P)
is-prop-is-decidable-subtype P = is-prop-type-Prop (is-decidable-subtype-Prop P)

decidable-subtype : {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
decidable-subtype l X = X → Decidable-Prop l
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  subtype-decidable-subtype : subtype l2 A
  subtype-decidable-subtype a = prop-Decidable-Prop (P a)

  is-decidable-decidable-subtype :
    is-decidable-subtype subtype-decidable-subtype
  is-decidable-decidable-subtype a =
    is-decidable-Decidable-Prop (P a)

  is-in-decidable-subtype : A → UU l2
  is-in-decidable-subtype = is-in-subtype subtype-decidable-subtype

  is-prop-is-in-decidable-subtype :
    (a : A) → is-prop (is-in-decidable-subtype a)
  is-prop-is-in-decidable-subtype =
    is-prop-is-in-subtype subtype-decidable-subtype

  is-proof-irrelevant-is-in-decidable-subtype :
    (a : A) → is-proof-irrelevant (is-in-decidable-subtype a)
  is-proof-irrelevant-is-in-decidable-subtype a =
    is-proof-irrelevant-is-prop (is-prop-is-in-decidable-subtype a)
```

### The underlying decidable type family of a decidable subtype

```agda
decidable-family-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} → decidable-subtype l2 A → decidable-family l2 A
decidable-family-decidable-subtype P =
  ( is-in-decidable-subtype P , is-decidable-decidable-subtype P)
```

### The underlying logical equivalence associated to a retract

```agda
iff-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B → A ↔ B
iff-retract R = inclusion-retract R , map-retraction-retract R

iff-retract' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B → B ↔ A
iff-retract' = inv-iff ∘ iff-retract
```

### Decidable types are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of R = is-decidable-iff' (iff-retract' R)

  is-decidable-retract-of' :
    A retract-of B → is-decidable A → is-decidable B
  is-decidable-retract-of' R = is-decidable-iff' (inv-iff (iff-retract' R))
```

### Decidable types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} H =
    is-decidable-retract-of (retract-equiv (f , H))

  is-decidable-equiv :
    A ≃ B → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

  is-decidable-equiv' :
    A ≃ B → is-decidable A → is-decidable B
  is-decidable-equiv' e = is-decidable-iff (map-equiv e) (map-inv-equiv e)
```

### Equivalent types have equivalent decidability predicates

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv-is-decidable : is-decidable A → is-decidable B
  map-equiv-is-decidable = is-decidable-equiv' e

  map-inv-equiv-is-decidable : is-decidable B → is-decidable A
  map-inv-equiv-is-decidable = is-decidable-equiv e

  is-section-map-inv-equiv-is-decidable :
    is-section map-equiv-is-decidable map-inv-equiv-is-decidable
  is-section-map-inv-equiv-is-decidable (inl x) =
    ap inl (is-section-map-inv-equiv e x)
  is-section-map-inv-equiv-is-decidable (inr x) =
    ap inr eq-neg

  is-retraction-map-inv-equiv-is-decidable :
    is-retraction map-equiv-is-decidable map-inv-equiv-is-decidable
  is-retraction-map-inv-equiv-is-decidable (inl x) =
    ap inl (is-retraction-map-inv-equiv e x)
  is-retraction-map-inv-equiv-is-decidable (inr x) =
    ap inr eq-neg

  is-equiv-map-equiv-is-decidable : is-equiv map-equiv-is-decidable
  is-equiv-map-equiv-is-decidable =
    is-equiv-is-invertible
      map-inv-equiv-is-decidable
      is-section-map-inv-equiv-is-decidable
      is-retraction-map-inv-equiv-is-decidable

  equiv-is-decidable : is-decidable A ≃ is-decidable B
  equiv-is-decidable = map-equiv-is-decidable , is-equiv-map-equiv-is-decidable
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  type-decidable-subtype : UU (l1 ⊔ l2)
  type-decidable-subtype = type-subtype (subtype-decidable-subtype P)

  inclusion-decidable-subtype : type-decidable-subtype → A
  inclusion-decidable-subtype = inclusion-subtype (subtype-decidable-subtype P)

  is-emb-inclusion-decidable-subtype : is-emb inclusion-decidable-subtype
  is-emb-inclusion-decidable-subtype =
    is-emb-inclusion-subtype (subtype-decidable-subtype P)

  is-decidable-map-inclusion-decidable-subtype :
    is-decidable-map inclusion-decidable-subtype
  is-decidable-map-inclusion-decidable-subtype x =
    is-decidable-equiv
      ( equiv-fiber-pr1 (type-Decidable-Prop ∘ P) x)
      ( is-decidable-Decidable-Prop (P x))

  is-injective-inclusion-decidable-subtype :
    is-injective inclusion-decidable-subtype
  is-injective-inclusion-decidable-subtype =
    is-injective-inclusion-subtype (subtype-decidable-subtype P)

  emb-decidable-subtype : type-decidable-subtype ↪ A
  emb-decidable-subtype = emb-subtype (subtype-decidable-subtype P)

  is-decidable-emb-inclusion-decidable-subtype :
    is-decidable-emb inclusion-decidable-subtype
  is-decidable-emb-inclusion-decidable-subtype =
    ( is-emb-inclusion-decidable-subtype ,
      is-decidable-map-inclusion-decidable-subtype)

  decidable-emb-decidable-subtype : type-decidable-subtype ↪ᵈ A
  decidable-emb-decidable-subtype =
    ( inclusion-decidable-subtype ,
      is-decidable-emb-inclusion-decidable-subtype)
```

### Decidable propositional maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-decidable-prop-map : (X → Y) → UU (l1 ⊔ l2)
  is-decidable-prop-map f = (y : Y) → is-decidable-prop (fiber f y)

  is-prop-is-decidable-prop-map :
    (f : X → Y) → is-prop (is-decidable-prop-map f)
  is-prop-is-decidable-prop-map f =
    is-prop-Π (λ y → is-prop-is-decidable-prop (fiber f y))

  is-decidable-prop-map-Prop : (X → Y) → Prop (l1 ⊔ l2)
  is-decidable-prop-map-Prop f =
    ( is-decidable-prop-map f , is-prop-is-decidable-prop-map f)

  abstract
    is-prop-map-is-decidable-prop-map :
      {f : X → Y} → is-decidable-prop-map f → is-prop-map f
    is-prop-map-is-decidable-prop-map H y = pr1 (H y)

  is-decidable-map-is-decidable-prop-map :
    {f : X → Y} → is-decidable-prop-map f → is-decidable-map f
  is-decidable-map-is-decidable-prop-map H y = pr2 (H y)
```

### Any map of which the fibers are decidable propositions is a decidable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  where

  abstract
    is-decidable-emb-is-decidable-prop-map :
      is-decidable-prop-map f → is-decidable-emb f
    pr1 (is-decidable-emb-is-decidable-prop-map H) =
      is-emb-is-prop-map (is-prop-map-is-decidable-prop-map H)
    pr2 (is-decidable-emb-is-decidable-prop-map H) =
      is-decidable-map-is-decidable-prop-map H

  abstract
    is-prop-map-is-decidable-emb : is-decidable-emb f → is-prop-map f
    is-prop-map-is-decidable-emb H =
      is-prop-map-is-emb (is-emb-is-decidable-emb H)

  abstract
    is-decidable-prop-map-is-decidable-emb :
      is-decidable-emb f → is-decidable-prop-map f
    pr1 (is-decidable-prop-map-is-decidable-emb H y) =
      is-prop-map-is-decidable-emb H y
    pr2 (is-decidable-prop-map-is-decidable-emb H y) =
      is-decidable-map-is-decidable-emb H y
```

### The decidable subtype associated to a decidable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y)
  where

  decidable-subtype-decidable-emb : decidable-subtype (l1 ⊔ l2) Y
  pr1 (decidable-subtype-decidable-emb y) =
    fiber (map-decidable-emb f) y
  pr2 (decidable-subtype-decidable-emb y) =
    is-decidable-prop-map-is-decidable-emb
      ( is-decidable-emb-map-decidable-emb f)
      ( y)

  compute-type-decidable-subtype-decidable-emb :
    type-decidable-subtype decidable-subtype-decidable-emb ≃ X
  compute-type-decidable-subtype-decidable-emb =
    equiv-total-fiber (map-decidable-emb f)

  inv-compute-type-decidable-subtype-decidable-emb :
    X ≃ type-decidable-subtype decidable-subtype-decidable-emb
  inv-compute-type-decidable-subtype-decidable-emb =
    inv-equiv-total-fiber (map-decidable-emb f)
```
