# Section 14.3 Logic in type theory

```agda
module section-14-3-logic-in-type-theory where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-9-2-bi-invertible-maps
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-3-universal-properties
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import exercise-4-3-double-negation-logic
open import exercise-9-4-three-for-two-equivalences
open import exercise-12-6-truncated-sigma-types
open import exercise-12-7-truncated-products
open import exercise-13-8-universal-property-coproducts
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
