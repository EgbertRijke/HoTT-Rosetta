# Section 19.1 The type of all groups

```agda
module section-19-1-the-type-of-all-groups where

open import universe-levels
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import exercise-4-1-arithmetic-operations-integers
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-7-group-laws-integers
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import exercise-12-4-coproduct-truncation
open import exercise-12-6-truncated-sigma-types
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-17-2-propositional-extensionality
```

In order to efficiently characterize the identity type of the type of all groups in a universe `𝒰`, we introduce the type of groups in two stages: first we introduce the type of _semigroups_, and then we introduce groups as semigroups that possess a unit element and inverses.
Since semigroups can have at most one unit element and since elements of semigroups can have at most one inverse, it follows that the type of groups is a subtype of the type of semigroups, and this will help us with the characterization of the identity type of the type of all groups.

## Remark 19.1.1

In order to show that isomorphic (semi)groups can be identified, it has to be part of the definition of a (semi)group that its underlying type is a set.
This is an important observation: in many branches of algebra the objects of study are _set-level_ structures.

A notable exception is formed by categories, which are objects at truncation level `1`, i.e., at the level of _groupoids_.
We will not cover categories in this book.
For more about categories we recommend Chapter 9 of \[citation: `hottbook`\].

## Definition 19.1.2

A **semigroup** in a universe `𝒰` is a triple `(G,μ,α)` consisting of a set `G` in `𝒰` equipped with a binary operation `μ : G → (G → G)` and a homotopy

```text
α : Π(x,y,z : G) μ(μ(x,y),z) = μ(x,μ(y,z))
```

witnessing that `μ` is **associative**.
We write `Semigroup_𝒰` for the type of all semigroups in `𝒰`, i.e., for the type

```text
Σ(G : Set_𝒰) Σ(μ : G → (G → G)) Π(x,y,z : G) μ(μ(x,y),z) = μ(x,μ(y,z)).
```

## Definition 19.1.3

A semigroup `G` is said to be **unital** if it comes equipped with a **unit** `e : G` that satisfies the left and right unit laws

```text
left-unit : Π(y : G) μ(e,y) = y
right-unit : Π(x : G) μ(x,e) = x.
```

We write `is-unital(G)` for the type of such triples `(e,left-unit,right-unit)`.
Unital semigroups are also called **monoids**, so we define

```text
Monoid_𝒰 ≔ Σ(G : Semigroup_𝒰) is-unital(G).
```

The unit of a semigroup is of course unique once it exists.
In univalent mathematics we express this fact by asserting that the type `is-unital(G)` is a proposition for each semigroup `G`.
In other words, being unital is a _property_ of semigroups rather than additional structure.
This is typical for univalent mathematics: we express that a structure is a property by proving that this structure is a proposition.

## Lemma 19.1.4

For a semigroup `G` the type `is-unital(G)` is a proposition.

### Proof

_Proof._ Let `G` be a semigroup.
Note that since `G` is a set, it follows that the types of the left and right unit laws are propositions.
Therefore it suffices to show that any two elements `e,e' : G` satisfying the left and right unit laws can be identified.
This is easy:

```text
e = μ(e,e') = e'.
```

 ◻

```agda
abstract
  all-elements-equal-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital-Semigroup G)
  all-elements-equal-is-unital-Semigroup
    ( X , μ , associative-μ)
    ( e , left-unit-e , right-unit-e)
    ( e' , left-unit-e' , right-unit-e') =
    eq-type-subtype
      ( λ e →
        product-Prop
          ( Π-Prop (type-Set X) (λ y → Id-Prop X (μ e y) y))
          ( Π-Prop (type-Set X) (λ x → Id-Prop X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-unital-Semigroup G)
  is-prop-is-unital-Semigroup G =
    is-prop-all-elements-equal (all-elements-equal-is-unital-Semigroup G)

is-unital-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-unital-prop-Semigroup G) = is-unital-Semigroup G
pr2 (is-unital-prop-Semigroup G) = is-prop-is-unital-Semigroup G
```

## Definition 19.1.5

Let `G` be a unital semigroup.
We say that `G` **has inverses** if it comes equipped with an operation `x ↦ x⁻¹` of type `G → G`, satisfying the left and right inverse laws

```text
left-inv : Π(x : G) μ(x⁻¹,x) = e
right-inv : Π(x : G) μ(x,x⁻¹) = e.
```

We write `is-group'(G,e)` for the type of such triples `((_)⁻¹,left-inv,right-inv)`, and we write

```text
is-group(G) ≔ Σ(e : is-unital(G)) is-group'(G,e)
```

A **group** is a unital semigroup with inverses.
We write `Group` for the type of all groups in `𝒰`.

```agda
is-group-is-unital-Semigroup :
  {l : Level} (G : Semigroup l) → is-unital-Semigroup G → UU l
is-group-is-unital-Semigroup G is-unital-Semigroup-G =
  Σ ( type-Semigroup G → type-Semigroup G)
    ( λ i →
      ( (x : type-Semigroup G) →
        mul-Semigroup G (i x) x ＝ pr1 is-unital-Semigroup-G) ×
      ( (x : type-Semigroup G) →
        mul-Semigroup G x (i x) ＝ pr1 is-unital-Semigroup-G))

is-group-Semigroup :
  {l : Level} (G : Semigroup l) → UU l
is-group-Semigroup G =
  Σ (is-unital-Semigroup G) (is-group-is-unital-Semigroup G)

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group-Semigroup

module _
  {l : Level} (G : Group l)
  where

  semigroup-Group : Semigroup l
  semigroup-Group = pr1 G

  set-Group : Set l
  set-Group = pr1 semigroup-Group

  type-Group : UU l
  type-Group = pr1 set-Group

  is-set-type-Group : is-set type-Group
  is-set-type-Group = pr2 set-Group

  has-associative-mul-Group : has-associative-mul type-Group
  has-associative-mul-Group = pr2 semigroup-Group

  mul-Group : type-Group → type-Group → type-Group
  mul-Group = pr1 has-associative-mul-Group

  ap-mul-Group :
    {x x' y y' : type-Group} (p : x ＝ x') (q : y ＝ y') →
    mul-Group x y ＝ mul-Group x' y'
  ap-mul-Group p q = ap-binary mul-Group p q

  mul-Group' : type-Group → type-Group → type-Group
  mul-Group' x y = mul-Group y x

  associative-mul-Group :
    (x y z : type-Group) →
    mul-Group (mul-Group x y) z ＝ mul-Group x (mul-Group y z)
  associative-mul-Group = pr2 has-associative-mul-Group

  is-group-Group : is-group-Semigroup semigroup-Group
  is-group-Group = pr2 G

  is-unital-Group : is-unital-Semigroup semigroup-Group
  is-unital-Group = pr1 is-group-Group

  monoid-Group : Monoid l
  pr1 monoid-Group = semigroup-Group
  pr2 monoid-Group = is-unital-Group

  unit-Group : type-Group
  unit-Group = pr1 is-unital-Group

  is-unit-Group : type-Group → UU l
  is-unit-Group x = x ＝ unit-Group

  is-unit-Group' : type-Group → UU l
  is-unit-Group' x = unit-Group ＝ x

  is-prop-is-unit-Group : (x : type-Group) → is-prop (is-unit-Group x)
  is-prop-is-unit-Group x = is-set-type-Group x unit-Group

  is-prop-is-unit-Group' : (x : type-Group) → is-prop (is-unit-Group' x)
  is-prop-is-unit-Group' x = is-set-type-Group unit-Group x

  is-unit-prop-Group : type-Group → Prop l
  pr1 (is-unit-prop-Group x) = is-unit-Group x
  pr2 (is-unit-prop-Group x) = is-prop-is-unit-Group x

  is-unit-prop-Group' : type-Group → Prop l
  pr1 (is-unit-prop-Group' x) = is-unit-Group' x
  pr2 (is-unit-prop-Group' x) = is-prop-is-unit-Group' x

  left-unit-law-mul-Group :
    (x : type-Group) → mul-Group unit-Group x ＝ x
  left-unit-law-mul-Group = pr1 (pr2 is-unital-Group)

  right-unit-law-mul-Group :
    (x : type-Group) → mul-Group x unit-Group ＝ x
  right-unit-law-mul-Group = pr2 (pr2 is-unital-Group)

  coherence-unit-laws-mul-Group :
    left-unit-law-mul-Group unit-Group ＝ right-unit-law-mul-Group unit-Group
  coherence-unit-laws-mul-Group =
    eq-is-prop (is-set-type-Group _ _)
```

## Lemma 19.1.6

For any semigroup `G` the type `is-group(G)` is a proposition.

### Proof

_Proof._ We have already seen that the type `is-unital(G)` is a proposition.
Therefore it suffices to show that the type `is-group'(G,e)` is a proposition for any `e : is-unital(G)`.

Since a semigroup `G` is assumed to be a set, we note that the types of the inverse laws are propositions.
Therefore it suffices to show that any two inverse operations satisfying the inverse laws are homotopic.

Let `x ↦ x⁻¹` and `x ↦ x^{-1'}` be two inverse operations on a unital semigroup `G`, both satisfying the inverse laws.
Then we have the following identifications

```text
x⁻¹ = μ(e,x⁻¹)
= μ(μ(x^{-1'},x),x⁻¹)
= μ(x^{-1'},μ(x,x⁻¹))
= μ(x^{-1'},e)
= x^{-1'}
```

for any `x : G`.
Thus the two inverses of `x` are the same, and the claim follows. ◻

```agda
abstract
  all-elements-equal-is-group-Semigroup :
    {l : Level} (G : Semigroup l) (e : is-unital-Semigroup G) →
    all-elements-equal (is-group-is-unital-Semigroup G e)
  all-elements-equal-is-group-Semigroup
    ( pair G (pair μ associative-G))
    ( pair e (pair left-unit-G right-unit-G))
    ( pair i (pair left-inv-i right-inv-i))
    ( pair i' (pair left-inv-i' right-inv-i')) =
    eq-type-subtype
      ( λ i →
        product-Prop
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ (i x) x) e))
          ( Π-Prop (type-Set G) (λ x → Id-Prop G (μ x (i x)) e)))
      ( eq-htpy
        ( λ x →
          equational-reasoning
          i x
          ＝ μ e (i x)
            by inv (left-unit-G (i x))
          ＝ μ (μ (i' x) x) (i x)
            by ap (λ y → μ y (i x)) (inv (left-inv-i' x))
          ＝ μ (i' x) (μ x (i x))
            by associative-G (i' x) x (i x)
          ＝ μ (i' x) e
            by ap (μ (i' x)) (right-inv-i x)
          ＝ i' x
            by right-unit-G (i' x)))

abstract
  is-prop-is-group-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-group-Semigroup G)
  is-prop-is-group-Semigroup G =
    is-prop-Σ
      ( is-prop-is-unital-Semigroup G)
      ( λ e →
        is-prop-all-elements-equal (all-elements-equal-is-group-Semigroup G e))

is-group-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-group-prop-Semigroup G) = is-group-Semigroup G
pr2 (is-group-prop-Semigroup G) = is-prop-is-group-Semigroup G
```

## Example 19.1.7

The type `ℤ` of integers has the structure of a group, with the group operation being addition.
The fact that `ℤ` is a set was shown in Exercise 12.4, and the group laws were shown in Exercise 5.7.

```agda
abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coproduct is-set-ℕ (is-set-coproduct is-set-unit is-set-ℕ)

ℤ-Set : Set lzero
pr1 ℤ-Set = ℤ
pr2 ℤ-Set = is-set-ℤ

ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ
```

## Example 19.1.8

Given a set `X`, we define the **automorphism group** of `X` by

```text
Aut(X) ≔ (X ≃ X).
```

The group operation of `Aut(X)` is given by composition of equivalences, and the unit of the group is the identity function.

```agda
Aut : {l : Level} → UU l → UU l
Aut Y = Y ≃ Y

is-set-Aut : {l : Level} {A : UU l} → is-set A → is-set (Aut A)
is-set-Aut H = is-set-equiv-is-set H H

Aut-Set : {l : Level} → Set l → Set l
pr1 (Aut-Set A) = Aut (type-Set A)
pr2 (Aut-Set A) = is-set-Aut (is-set-type-Set A)

set-symmetric-Group : {l : Level} (X : Set l) → Set l
set-symmetric-Group X = Aut-Set X

type-symmetric-Group : {l : Level} (X : Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : Set l) → has-associative-mul-Set (Aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-Semigroup-symmetric-Semigroup :
  {l : Level} (X : Set l) → is-unital-Semigroup (symmetric-Semigroup X)
pr1 (is-unital-Semigroup-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : Set l) →
  is-group-is-unital-Semigroup
    ( symmetric-Semigroup X)
    ( is-unital-Semigroup-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-Semigroup-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X
```

An important special case of the automorphism groups is the **symmetric group**

```text
S_n ≔ Aut(Fin{n}).
```
