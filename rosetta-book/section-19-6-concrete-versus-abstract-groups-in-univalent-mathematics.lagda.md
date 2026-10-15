# Section 19.6 Concrete versus abstract groups in univalent mathematics

```agda
module section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-11-6-the-structure-identity-principle
open import exercise-11-2-paths-along-equivalences
open import exercise-11-3-homotopic-embeddings
open import exercise-11-4-embedding-triangles
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-16-3-finite-types
open import section-17-2-propositional-extensionality
open import section-17-4-maps-and-families-of-types
open import section-17-6-the-binomial-types
open import section-18-5-set-truncations
open import section-19-1-the-type-of-all-groups
open import section-19-2-group-homomorphisms
open import section-19-3-isomorphic-groups-are-equal
open import section-19-4-homotopy-groups-of-types
open import section-19-5-the-eckmann-hilton-argument
```

In univalent mathematics there is another exciting perspective on group theory.
We won’t be able to go into full detail here, but we can sketch some of the key ideas.
To learn more about this beautiful univalent perspective on group theory, I recommend the forthcoming [Symmetry](https://github.com/UniMath/SymmetryBook) book.

We saw in Example 19.4.3 that for every pointed connected `1`-type `X` we obtain a group with underlying type `Ω(X)`.
All groups can be constructed in this way.
In fact, for every group `G` in `𝒰` the type

```text
Σ(B : Pointed-Connected-1-Type_𝒰) G ≅ Ω(B)
```

of pointed connected `1`-types `B` equipped with a group isomorphism from `G` to `Ω(B)` is contractible.
We write `BG` for the unique pointed connected `1`-type whose loop space is isomorphic to `G`.
The pointed type `BG` is also called the **delooping** of `G`, or the **classifying type** of `G`.
The fact that the above type is contractible is of course heavily reliant on the univalence axiom.

```agda
∞-Group : (l : Level) → UU (lsuc l)
∞-Group l = Σ (Pointed-Type l) (λ X → is-0-connected (type-Pointed-Type X))

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = pr1 G

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group =
    type-Pointed-Type classifying-pointed-type-∞-Group

  shape-∞-Group : classifying-type-∞-Group
  shape-∞-Group =
    point-Pointed-Type classifying-pointed-type-∞-Group

  point-∞-Group : unit → classifying-type-∞-Group
  point-∞-Group = point shape-∞-Group

  abstract
    is-0-connected-classifying-type-∞-Group :
      is-0-connected classifying-type-∞-Group
    is-0-connected-classifying-type-∞-Group = pr2 G

  abstract
    mere-eq-classifying-type-∞-Group :
      (X Y : classifying-type-∞-Group) → mere-eq X Y
    mere-eq-classifying-type-∞-Group =
      mere-eq-is-0-connected
        is-0-connected-classifying-type-∞-Group

  pointed-type-∞-Group : Pointed-Type l
  pointed-type-∞-Group = Ω classifying-pointed-type-∞-Group

  type-∞-Group : UU l
  type-∞-Group = type-Pointed-Type pointed-type-∞-Group

  unit-∞-Group : type-∞-Group
  unit-∞-Group = point-Pointed-Type pointed-type-∞-Group

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group = mul-Ω classifying-pointed-type-∞-Group

  associative-mul-∞-Group :
    (x y z : type-∞-Group) →
    mul-∞-Group (mul-∞-Group x y) z ＝
    mul-∞-Group x (mul-∞-Group y z)
  associative-mul-∞-Group = associative-mul-Ω classifying-pointed-type-∞-Group

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → mul-∞-Group unit-∞-Group x ＝ x
  left-unit-law-mul-∞-Group =
    left-unit-law-mul-Ω classifying-pointed-type-∞-Group

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → mul-∞-Group y unit-∞-Group ＝ y
  right-unit-law-mul-∞-Group =
    right-unit-law-mul-Ω classifying-pointed-type-∞-Group

  coherence-unit-laws-mul-∞-Group :
    left-unit-law-mul-∞-Group unit-∞-Group ＝
    right-unit-law-mul-∞-Group unit-∞-Group
  coherence-unit-laws-mul-∞-Group =
    coherence-unit-laws-mul-Ω classifying-pointed-type-∞-Group

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = inv-Ω classifying-pointed-type-∞-Group

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → mul-∞-Group (inv-∞-Group x) x ＝ unit-∞-Group
  left-inverse-law-mul-∞-Group =
    left-inverse-law-mul-Ω classifying-pointed-type-∞-Group

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → mul-∞-Group x (inv-∞-Group x) ＝ unit-∞-Group
  right-inverse-law-mul-∞-Group =
    right-inverse-law-mul-Ω classifying-pointed-type-∞-Group

Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group =
    shape-∞-Group ∞-group-Concrete-Group

  is-0-connected-classifying-type-Concrete-Group :
    is-0-connected classifying-type-Concrete-Group
  is-0-connected-classifying-type-Concrete-Group =
    is-0-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = pr2 G

  set-Concrete-Group : Set l
  pr1 set-Concrete-Group = type-Concrete-Group
  pr2 set-Concrete-Group = is-set-type-Concrete-Group

  abstract
    is-1-type-classifying-type-Concrete-Group :
      is-trunc one-𝕋 classifying-type-Concrete-Group
    is-1-type-classifying-type-Concrete-Group X Y =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group X)
        ( is-set-Prop (X ＝ Y))
        ( λ where
          refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group Y)
              ( is-set-Prop (shape-Concrete-Group ＝ Y))
              ( λ where refl → is-set-type-Concrete-Group))

  classifying-1-type-Concrete-Group : Truncated-Type l one-𝕋
  pr1 classifying-1-type-Concrete-Group = classifying-type-Concrete-Group
  pr2 classifying-1-type-Concrete-Group =
    is-1-type-classifying-type-Concrete-Group

module _
  {l : Level} (G : Concrete-Group l)
  where

  unit-Concrete-Group : type-Concrete-Group G
  unit-Concrete-Group = unit-∞-Group (∞-group-Concrete-Group G)

  mul-Concrete-Group : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group = mul-∞-Group (∞-group-Concrete-Group G)

  mul-Concrete-Group' : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group' x y = mul-Concrete-Group y x

  associative-mul-Concrete-Group :
    (x y z : type-Concrete-Group G) →
    ( mul-Concrete-Group (mul-Concrete-Group x y) z) ＝
    ( mul-Concrete-Group x (mul-Concrete-Group y z))
  associative-mul-Concrete-Group =
    associative-mul-∞-Group (∞-group-Concrete-Group G)

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) → mul-Concrete-Group unit-Concrete-Group x ＝ x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group (∞-group-Concrete-Group G)

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group G) → mul-Concrete-Group y unit-Concrete-Group ＝ y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group (∞-group-Concrete-Group G)

  coherence-unit-laws-mul-Concrete-Group :
    left-unit-law-mul-Concrete-Group unit-Concrete-Group ＝
    right-unit-law-mul-Concrete-Group unit-Concrete-Group
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group (∞-group-Concrete-Group G)

  inv-Concrete-Group : type-Concrete-Group G → type-Concrete-Group G
  inv-Concrete-Group = inv-∞-Group (∞-group-Concrete-Group G)

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group (inv-Concrete-Group x) x ＝ unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group (∞-group-Concrete-Group G)

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group x (inv-Concrete-Group x) ＝ unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group (∞-group-Concrete-Group G)

  has-associative-mul-Concrete-Group :
    has-associative-mul-Set (set-Concrete-Group G)
  pr1 has-associative-mul-Concrete-Group = mul-Concrete-Group
  pr2 has-associative-mul-Concrete-Group = associative-mul-Concrete-Group

  semigroup-Concrete-Group : Semigroup l
  pr1 semigroup-Concrete-Group = set-Concrete-Group G
  pr2 semigroup-Concrete-Group = has-associative-mul-Concrete-Group

  is-unital-Concrete-Group : is-unital-Semigroup semigroup-Concrete-Group
  pr1 is-unital-Concrete-Group = unit-Concrete-Group
  pr1 (pr2 is-unital-Concrete-Group) = left-unit-law-mul-Concrete-Group
  pr2 (pr2 is-unital-Concrete-Group) = right-unit-law-mul-Concrete-Group

  is-group-Concrete-Group' :
    is-group-is-unital-Semigroup
      ( semigroup-Concrete-Group)
      ( is-unital-Concrete-Group)
  pr1 is-group-Concrete-Group' = inv-Concrete-Group
  pr1 (pr2 is-group-Concrete-Group') = left-inverse-law-mul-Concrete-Group
  pr2 (pr2 is-group-Concrete-Group') = right-inverse-law-mul-Concrete-Group

  is-group-Concrete-Group : is-group-Semigroup semigroup-Concrete-Group
  pr1 is-group-Concrete-Group = is-unital-Concrete-Group
  pr2 is-group-Concrete-Group = is-group-Concrete-Group'

  group-Concrete-Group : Group l
  pr1 group-Concrete-Group = semigroup-Concrete-Group
  pr2 group-Concrete-Group = is-group-Concrete-Group

  monoid-Concrete-Group : Monoid l
  monoid-Concrete-Group = monoid-Group group-Concrete-Group
```

## Example 19.6.1

We have already seen that

```text
S_n ≅ Ω(BS_n),
```

i.e., that the loop space of the type of all finite types of cardinality `n` is equivalent to the symmetric group `S_n`.
The type `BS_n` is of course a pointed connected `1`-type, so `BS_n` is indeed the classifying type of the symmetric group `S_n`.

```agda
module _
  (l : Level) (n : ℕ)
  where

  classifying-type-Type-With-Cardinality-ℕ-Concrete-Group : UU (lsuc l)
  classifying-type-Type-With-Cardinality-ℕ-Concrete-Group =
    Type-With-Cardinality-ℕ l n

  shape-Type-With-Cardinality-ℕ-Concrete-Group :
    classifying-type-Type-With-Cardinality-ℕ-Concrete-Group
  shape-Type-With-Cardinality-ℕ-Concrete-Group =
    raise-Fin-Type-With-Cardinality-ℕ l n

  classifying-pointed-type-Type-With-Cardinality-ℕ-Concrete-Group :
    Pointed-Type (lsuc l)
  classifying-pointed-type-Type-With-Cardinality-ℕ-Concrete-Group =
    classifying-type-Type-With-Cardinality-ℕ-Concrete-Group ,
    shape-Type-With-Cardinality-ℕ-Concrete-Group

  is-0-connected-classifying-type-Type-With-Cardinality-ℕ-Concrete-Group :
    is-0-connected classifying-type-Type-With-Cardinality-ℕ-Concrete-Group
  is-0-connected-classifying-type-Type-With-Cardinality-ℕ-Concrete-Group =
    is-0-connected-Type-With-Cardinality-ℕ n

  ∞-group-Type-With-Cardinality-ℕ-Concrete-Group : ∞-Group (lsuc l)
  ∞-group-Type-With-Cardinality-ℕ-Concrete-Group =
    classifying-pointed-type-Type-With-Cardinality-ℕ-Concrete-Group ,
    is-0-connected-classifying-type-Type-With-Cardinality-ℕ-Concrete-Group

  type-Type-With-Cardinality-ℕ-Concrete-Group : UU (lsuc l)
  type-Type-With-Cardinality-ℕ-Concrete-Group =
    type-∞-Group ∞-group-Type-With-Cardinality-ℕ-Concrete-Group

  is-set-type-Type-With-Cardinality-ℕ-Concrete-Group :
    is-set type-Type-With-Cardinality-ℕ-Concrete-Group
  is-set-type-Type-With-Cardinality-ℕ-Concrete-Group =
    is-1-type-Type-With-Cardinality-ℕ n
      ( raise-Fin-Type-With-Cardinality-ℕ l n)
      ( raise-Fin-Type-With-Cardinality-ℕ l n)

  Type-With-Cardinality-ℕ-Concrete-Group : Concrete-Group (lsuc l)
  Type-With-Cardinality-ℕ-Concrete-Group =
    ∞-group-Type-With-Cardinality-ℕ-Concrete-Group ,
    is-set-type-Type-With-Cardinality-ℕ-Concrete-Group

  Type-With-Cardinality-ℕ-Group : Group (lsuc l)
  Type-With-Cardinality-ℕ-Group =
    group-Concrete-Group Type-With-Cardinality-ℕ-Concrete-Group
```

Since the map

```text
Ω : Pointed-Connected-1-Type_𝒰 → Group_𝒰
```

is an equivalence, we obtain two perspectives on the type of all groups.
The elements of the type `Group_𝒰` are groups according to the traditional definition of groups.
We call such groups **abstract groups**.
On the other hand, pointed connected `1`-types `B` are **concrete groups** in the sense that they contain an object `⋆ : B`, and the group that `B` represents is the group of self-identifications (i.e., symmetries) of the base point `⋆ : B`.
Thus we see that when we present a group as a pointed connected `1`-type, then we _concretely_ manifest that group as the group of symmetries of some object.

We can also bring group homomorphisms into the mix: for every group homomorphism `f : G → H` the type of pointed maps `b : BG →_⋆ BH` equipped with a homotopy witnessing

```text
      [G] ----- f ----->  [H]
       |                   |
    ≅  |                   | ≅
       |                   |
       V                   V
    [Ω(BG)] -- Ω(b) --> [Ω(BH)]
```

commutes is contractible.
In other words, every group homomorphism `f : G → H` has a unique **delooping** `Bf : BG → BH`.

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  hom-∞-Group : UU (l1 ⊔ l2)
  hom-∞-Group =
    classifying-pointed-type-∞-Group G →∗ classifying-pointed-type-∞-Group H

  classifying-map-hom-∞-Group :
    hom-∞-Group → classifying-type-∞-Group G → classifying-type-∞-Group H
  classifying-map-hom-∞-Group = map-pointed-map

  preserves-point-classifying-map-hom-∞-Group :
    (f : hom-∞-Group) →
    classifying-map-hom-∞-Group f (shape-∞-Group G) ＝ shape-∞-Group H
  preserves-point-classifying-map-hom-∞-Group =
    preserves-point-pointed-map

  map-hom-∞-Group : hom-∞-Group → type-∞-Group G → type-∞-Group H
  map-hom-∞-Group = map-Ω

  preserves-unit-map-hom-∞-Group :
    (f : hom-∞-Group) → map-hom-∞-Group f (unit-∞-Group G) ＝ unit-∞-Group H
  preserves-unit-map-hom-∞-Group = preserves-refl-map-Ω

  preserves-mul-map-hom-∞-Group :
    (f : hom-∞-Group) {x y : type-∞-Group G} →
    map-hom-∞-Group f (mul-∞-Group G x y) ＝
    mul-∞-Group H (map-hom-∞-Group f x) (map-hom-∞-Group f y)
  preserves-mul-map-hom-∞-Group = preserves-mul-map-Ω

  preserves-inv-map-hom-∞-Group :
    (f : hom-∞-Group) (x : type-∞-Group G) →
    map-hom-∞-Group f (inv-∞-Group G x) ＝ inv-∞-Group H (map-hom-∞-Group f x)
  preserves-inv-map-hom-∞-Group = preserves-inv-map-Ω

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  hom-Concrete-Group : UU (l1 ⊔ l2)
  hom-Concrete-Group =
    hom-∞-Group (∞-group-Concrete-Group G) (∞-group-Concrete-Group H)

  is-set-hom-Concrete-Group : is-set hom-Concrete-Group
  is-set-hom-Concrete-Group =
    is-trunc-map-ev-is-connected
      ( zero-𝕋)
      ( shape-Concrete-Group G)
      ( is-0-connected-classifying-type-Concrete-Group G)
      ( is-1-type-classifying-type-Concrete-Group H)
      ( shape-Concrete-Group H)

  hom-set-Concrete-Group : Set (l1 ⊔ l2)
  pr1 hom-set-Concrete-Group = hom-Concrete-Group
  pr2 hom-set-Concrete-Group = is-set-hom-Concrete-Group

  classifying-map-hom-Concrete-Group :
    hom-Concrete-Group →
    classifying-type-Concrete-Group G → classifying-type-Concrete-Group H
  classifying-map-hom-Concrete-Group =
    classifying-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-point-classifying-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    classifying-map-hom-Concrete-Group f (shape-Concrete-Group G) ＝
    shape-Concrete-Group H
  preserves-point-classifying-map-hom-Concrete-Group =
    preserves-point-classifying-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  map-hom-Concrete-Group :
    hom-Concrete-Group → type-Concrete-Group G → type-Concrete-Group H
  map-hom-Concrete-Group =
    map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-unit-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    map-hom-Concrete-Group f (unit-Concrete-Group G) ＝ unit-Concrete-Group H
  preserves-unit-map-hom-Concrete-Group =
    preserves-unit-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-mul-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) {x y : type-Concrete-Group G} →
    ( map-hom-Concrete-Group f (mul-Concrete-Group G x y)) ＝
    ( mul-Concrete-Group H
      ( map-hom-Concrete-Group f x)
      ( map-hom-Concrete-Group f y))
  preserves-mul-map-hom-Concrete-Group =
    preserves-mul-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-inv-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) (x : type-Concrete-Group G) →
    map-hom-Concrete-Group f (inv-Concrete-Group G x) ＝
    inv-Concrete-Group H (map-hom-Concrete-Group f x)
  preserves-inv-map-hom-Concrete-Group =
    preserves-inv-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  hom-group-hom-Concrete-Group :
    hom-Concrete-Group →
    hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
  hom-group-hom-Concrete-Group f =
    pair (map-hom-Concrete-Group f) (preserves-mul-map-hom-Concrete-Group f)
```

We can do all of group theory in this way.
For example, traditionally a `G`-set is defined to be a set `X` equipped with a group homomorphism `G → Aut(X)`.
That is, the type of **abstract `G`-sets** is defined to be

```text
G-Set_𝒰 ≔ Σ(X : Set_𝒰) hom(G,Aut(X)).
```

```agda
action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
action-∞-Group l2 G = classifying-type-∞-Group G → UU l2

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  type-action-∞-Group : UU l2
  type-action-∞-Group = X (shape-∞-Group G)

  mul-action-∞-Group :
    type-∞-Group G → type-action-∞-Group → type-action-∞-Group
  mul-action-∞-Group = tr X

  associative-mul-action-∞-Group :
    (h g : type-∞-Group G) (x : type-action-∞-Group) →
    (mul-action-∞-Group (mul-∞-Group G h g) x) ＝
    (mul-action-∞-Group g (mul-action-∞-Group h x))
  associative-mul-action-∞-Group = tr-concat {B = X}

  unit-law-mul-action-∞-Group :
    (x : type-action-∞-Group) → mul-action-∞-Group refl x ＝ x
  unit-law-mul-action-∞-Group x = refl

module _
  {l1 : Level} (G : Group l1)
  where

  action-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  action-Group l =
    Σ (Set l) (λ X → hom-Group G (symmetric-Group X))

module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  set-action-Group : Set l2
  set-action-Group = pr1 X

  type-action-Group : UU l2
  type-action-Group = type-Set set-action-Group

  is-set-type-action-Group : is-set type-action-Group
  is-set-type-action-Group = is-set-type-Set set-action-Group

  equiv-mul-action-Group : type-Group G → type-action-Group ≃ type-action-Group
  equiv-mul-action-Group =
    map-hom-Group G (symmetric-Group set-action-Group) (pr2 X)

  mul-action-Group : type-Group G → type-action-Group → type-action-Group
  mul-action-Group g = map-equiv (equiv-mul-action-Group g)

  mul-action-Group' : type-action-Group → type-Group G → type-action-Group
  mul-action-Group' x g = mul-action-Group g x

  preserves-unit-mul-action-Group : mul-action-Group (unit-Group G) ~ id
  preserves-unit-mul-action-Group =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-action-Group)
          ( pr2 X)))

  preserves-mul-action-Group :
    (g : type-Group G) (h : type-Group G) (x : type-action-Group) →
    mul-action-Group (mul-Group G g h) x ＝
    mul-action-Group g (mul-action-Group h x)
  preserves-mul-action-Group g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G (symmetric-Group set-action-Group) (pr2 X)))

  transpose-eq-mul-action-Group :
    (g : type-Group G) (x y : type-action-Group) →
    mul-action-Group g x ＝ y → x ＝ mul-action-Group (inv-Group G g) y
  transpose-eq-mul-action-Group g x ._ refl =
    ( inv
      ( ( ap (mul-action-Group' x) (left-inverse-law-mul-Group G g)) ∙
        ( preserves-unit-mul-action-Group x))) ∙
    ( preserves-mul-action-Group (inv-Group G g) g x)
```

However, this definition is equivalent to a family `X : BG → Set_𝒰` of sets indexed by the classifying type `BG`.
Therefore we define **concrete `G`-sets** to be type families `X : BG → Set_𝒰`.
Given a concrete `G`-set `X : BG → Set_𝒰`, the set being acted upon is the set `X(⋆)`, and the action of `G` on `X(⋆)` is given by transport, since the elements of `G` are equivalent to loops in `BG`.

```agda
module _
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1)
  where

  action-Concrete-Group : UU (l1 ⊔ lsuc l2)
  action-Concrete-Group = classifying-type-Concrete-Group G → Set l2

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  set-action-Concrete-Group : Set l2
  set-action-Concrete-Group = X (shape-Concrete-Group G)

  type-action-Concrete-Group : UU l2
  type-action-Concrete-Group = type-Set set-action-Concrete-Group

  is-set-type-action-Concrete-Group : is-set type-action-Concrete-Group
  is-set-type-action-Concrete-Group = is-set-type-Set set-action-Concrete-Group

  mul-action-Concrete-Group :
    type-Concrete-Group G →
    type-action-Concrete-Group → type-action-Concrete-Group
  mul-action-Concrete-Group g x = tr (type-Set ∘ X) g x
```

The type of **orbits** of a concrete `G`-set `X : BG → Set_𝒰` can then be defined as

```text
X/G ≔ Σ(u : BG) X(u)
```

```agda
orbit-action-∞-Group :
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G) → UU (l1 ⊔ l2)
orbit-action-∞-Group G X = Σ (classifying-type-∞-Group G) X

orbit-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  UU (l1 ⊔ l2)
orbit-action-Concrete-Group G X =
  Σ (classifying-type-Concrete-Group G) (type-Set ∘ X)
```

and the type of **fixed points** of `X` can be defined as

```text
X_G ≔ Π(u : BG) X(u).
```

```agda
fixed-point-action-∞-Group :
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G) → UU (l1 ⊔ l2)
fixed-point-action-∞-Group G X = (u : classifying-type-∞-Group G) → X u

fixed-point-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  UU (l1 ⊔ l2)
fixed-point-action-Concrete-Group G X = (u : classifying-type-Concrete-Group G) → (type-Set ∘ X) u
```

To see that these definitions make sense, note that the fiber inclusion `X(⋆) → X/G` maps each element in the `G`-set `X` to its orbit.
The fiber inclusion is surjective by Exercise 18.5, and it maps two elements `x,y : X(⋆)` to the same orbit precisely when there is a group element `g` such that `gx = y`.
Similarly, for the type of fixed points notice that each `x : X_G` determines an element `x_⋆ : X(⋆)`, which comes equipped with an identification

```text
apd_{x}(g) : gx_⋆ = x_⋆
```

since the group action of `G` on `X` is given by transport.

Also, notice that a subgroup `H` of `G` determines an inclusion homomorphism `i : H → G`, and this inclusion function corresponds uniquely to a pointed map `Bi : BH → BG`.
Since `Ω(Bi)` is an embedding, we note that `Bi` must be a `0`-truncated map.
Therefore, a concrete subgroup of a concrete group `BG` is defined to be a concrete `G`-set `X` such that the type of orbits is connected.
Such concrete `G`-sets are called **transitive**.

```agda
subgroup-action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) →
  classifying-type-∞-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-∞-Group l2 G u =
  Σ ( classifying-type-∞-Group G → Set l2)
    ( λ X →
      ( type-Set (X u)) ×
      ( is-0-connected (Σ (classifying-type-∞-Group G) (type-Set ∘ X))))

subgroup-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-∞-Group l2 G = subgroup-action-∞-Group l2 G (shape-∞-Group G)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-transitive-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-transitive-prop-action-∞-Group =
    is-0-connected-Prop (orbit-action-∞-Group G X)

  is-transitive-action-∞-Group : UU (l1 ⊔ l2)
  is-transitive-action-∞-Group = type-Prop is-transitive-prop-action-∞-Group

  is-prop-is-transitive-action-∞-Group : is-prop is-transitive-action-∞-Group
  is-prop-is-transitive-action-∞-Group =
    is-prop-type-Prop is-transitive-prop-action-∞-Group

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : subgroup-∞-Group l2 G)
  where

  set-action-subgroup-∞-Group :
    classifying-type-∞-Group G → Set l2
  set-action-subgroup-∞-Group = pr1 H

  action-subgroup-∞-Group : classifying-type-∞-Group G → UU l2
  action-subgroup-∞-Group = type-Set ∘ set-action-subgroup-∞-Group

  classifying-type-subgroup-∞-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-∞-Group =
    Σ (classifying-type-∞-Group G) action-subgroup-∞-Group

  shape-subgroup-∞-Group : classifying-type-subgroup-∞-Group
  pr1 shape-subgroup-∞-Group = shape-∞-Group G
  pr2 shape-subgroup-∞-Group = pr1 (pr2 H)

  classifying-pointed-type-subgroup-∞-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-∞-Group =
    classifying-type-subgroup-∞-Group
  pr2 classifying-pointed-type-subgroup-∞-Group =
    shape-subgroup-∞-Group

  is-connected-classifying-type-subgroup-∞-Group :
    is-0-connected classifying-type-subgroup-∞-Group
  is-connected-classifying-type-subgroup-∞-Group = pr2 (pr2 H)

  ∞-group-subgroup-∞-Group : ∞-Group (l1 ⊔ l2)
  pr1 ∞-group-subgroup-∞-Group = classifying-pointed-type-subgroup-∞-Group
  pr2 ∞-group-subgroup-∞-Group = is-connected-classifying-type-subgroup-∞-Group

transitive-action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-∞-Group l2 G =
  Σ (action-∞-Group l2 G) (is-transitive-action-∞-Group G)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : transitive-action-∞-Group l2 G)
  where

  action-transitive-action-∞-Group : action-∞-Group l2 G
  action-transitive-action-∞-Group = pr1 X

  is-transitive-transitive-action-∞-Group :
    is-transitive-action-∞-Group G action-transitive-action-∞-Group
  is-transitive-transitive-action-∞-Group = pr2 X

  type-transitive-action-∞-Group : UU l2
  type-transitive-action-∞-Group =
    type-action-∞-Group G action-transitive-action-∞-Group

  mul-transitive-action-∞-Group :
    type-∞-Group G →
    type-transitive-action-∞-Group → type-transitive-action-∞-Group
  mul-transitive-action-∞-Group =
    mul-action-∞-Group G action-transitive-action-∞-Group

  associative-mul-transitive-action-∞-Group :
    (g h : type-∞-Group G) (x : type-transitive-action-∞-Group) →
    mul-transitive-action-∞-Group (mul-∞-Group G g h) x ＝
    mul-transitive-action-∞-Group h (mul-transitive-action-∞-Group g x)
  associative-mul-transitive-action-∞-Group =
    associative-mul-action-∞-Group G action-transitive-action-∞-Group

  unit-law-mul-transitive-action-∞-Group :
    (x : type-transitive-action-∞-Group) →
    mul-transitive-action-∞-Group (unit-∞-Group G) x ＝ x
  unit-law-mul-transitive-action-∞-Group =
    unit-law-mul-action-∞-Group G action-transitive-action-∞-Group

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-transitive-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-transitive-prop-action-Concrete-Group =
    is-transitive-prop-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-transitive-action-Concrete-Group : UU (l1 ⊔ l2)
  is-transitive-action-Concrete-Group =
    is-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-prop-is-transitive-action-Concrete-Group :
    is-prop is-transitive-action-Concrete-Group
  is-prop-is-transitive-action-Concrete-Group =
    is-prop-is-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

transitive-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-Concrete-Group l2 G =
  type-subtype (is-transitive-prop-action-Concrete-Group {l2 = l2} G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : transitive-action-Concrete-Group l2 G)
  where

  action-transitive-action-Concrete-Group :
    action-Concrete-Group l2 G
  action-transitive-action-Concrete-Group = pr1 X

  is-transitive-transitive-action-Concrete-Group :
    is-transitive-action-Concrete-Group G
      action-transitive-action-Concrete-Group
  is-transitive-transitive-action-Concrete-Group = pr2 X

  transitive-action-∞-group-transitive-action-Concrete-Group :
    transitive-action-∞-Group l2 (∞-group-Concrete-Group G)
  pr1 transitive-action-∞-group-transitive-action-Concrete-Group =
    type-Set ∘ action-transitive-action-Concrete-Group
  pr2 transitive-action-∞-group-transitive-action-Concrete-Group =
    is-transitive-transitive-action-Concrete-Group

  set-transitive-action-Concrete-Group : Set l2
  set-transitive-action-Concrete-Group =
    set-action-Concrete-Group G action-transitive-action-Concrete-Group

  type-transitive-action-Concrete-Group : UU l2
  type-transitive-action-Concrete-Group =
    type-action-Concrete-Group G action-transitive-action-Concrete-Group

  is-set-type-transitive-action-Concrete-Group :
    is-set type-transitive-action-Concrete-Group
  is-set-type-transitive-action-Concrete-Group =
    is-set-type-action-Concrete-Group G action-transitive-action-Concrete-Group

  mul-transitive-action-Concrete-Group :
    type-Concrete-Group G → type-transitive-action-Concrete-Group →
    type-transitive-action-Concrete-Group
  mul-transitive-action-Concrete-Group =
    mul-action-Concrete-Group G action-transitive-action-Concrete-Group

subgroup-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) →
  classifying-type-Concrete-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-Concrete-Group l2 G u =
  Σ ( transitive-action-Concrete-Group l2 G)
    ( λ X → type-Set (action-transitive-action-Concrete-Group G X u))

subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-Concrete-Group l2 G =
  subgroup-action-Concrete-Group l2 G (shape-Concrete-Group G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : subgroup-Concrete-Group l2 G)
  where

  transitive-action-subgroup-Concrete-Group :
    transitive-action-Concrete-Group l2 G
  transitive-action-subgroup-Concrete-Group = pr1 H

  action-subgroup-Concrete-Group : action-Concrete-Group l2 G
  action-subgroup-Concrete-Group =
    action-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  coset-subgroup-Concrete-Group : Set l2
  coset-subgroup-Concrete-Group =
    action-subgroup-Concrete-Group (shape-Concrete-Group G)

  type-coset-subgroup-Concrete-Group : UU l2
  type-coset-subgroup-Concrete-Group = type-Set coset-subgroup-Concrete-Group

  is-transitive-action-subgroup-Concrete-Group :
    is-transitive-action-Concrete-Group G action-subgroup-Concrete-Group
  is-transitive-action-subgroup-Concrete-Group =
    is-transitive-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  mul-transitive-action-subgroup-Concrete-Group :
    type-Concrete-Group G → type-coset-subgroup-Concrete-Group →
    type-coset-subgroup-Concrete-Group
  mul-transitive-action-subgroup-Concrete-Group =
    mul-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  classifying-type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-Concrete-Group =
    orbit-action-Concrete-Group G action-subgroup-Concrete-Group

  unit-coset-subgroup-Concrete-Group : type-coset-subgroup-Concrete-Group
  unit-coset-subgroup-Concrete-Group = pr2 H

  shape-subgroup-Concrete-Group : classifying-type-subgroup-Concrete-Group
  pr1 shape-subgroup-Concrete-Group = shape-Concrete-Group G
  pr2 shape-subgroup-Concrete-Group = unit-coset-subgroup-Concrete-Group

  classifying-pointed-type-subgroup-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-Concrete-Group =
    classifying-type-subgroup-Concrete-Group
  pr2 classifying-pointed-type-subgroup-Concrete-Group =
    shape-subgroup-Concrete-Group

  is-connected-classifying-type-subgroup-Concrete-Group :
    is-0-connected classifying-type-subgroup-Concrete-Group
  is-connected-classifying-type-subgroup-Concrete-Group =
    is-transitive-action-subgroup-Concrete-Group

  classifying-inclusion-subgroup-Concrete-Group :
    classifying-type-subgroup-Concrete-Group →
    classifying-type-Concrete-Group G
  classifying-inclusion-subgroup-Concrete-Group = pr1

  preserves-shape-classifying-inclusion-subgroup-Concrete-Group :
    classifying-inclusion-subgroup-Concrete-Group
      shape-subgroup-Concrete-Group ＝
    shape-Concrete-Group G
  preserves-shape-classifying-inclusion-subgroup-Concrete-Group = refl

  classifying-pointed-inclusion-subgroup-Concrete-Group :
    classifying-pointed-type-subgroup-Concrete-Group →∗
    classifying-pointed-type-Concrete-Group G
  pr1 classifying-pointed-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group
  pr2 classifying-pointed-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group

  is-0-map-classifying-inclusion-subgroup-Concrete-Group :
    is-0-map classifying-inclusion-subgroup-Concrete-Group
  is-0-map-classifying-inclusion-subgroup-Concrete-Group =
    is-0-map-pr1 (λ u → is-set-type-Set (action-subgroup-Concrete-Group u))

  is-faithful-classifying-inclusion-subgroup-Concrete-Group :
    is-faithful classifying-inclusion-subgroup-Concrete-Group
  is-faithful-classifying-inclusion-subgroup-Concrete-Group =
    is-faithful-is-0-map is-0-map-classifying-inclusion-subgroup-Concrete-Group

  type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  type-subgroup-Concrete-Group =
    type-Ω classifying-pointed-type-subgroup-Concrete-Group

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-emb-map-Ω :
    (f : A →∗ B) → is-faithful (map-pointed-map f) → is-emb (map-Ω f)
  is-emb-map-Ω f H =
    is-emb-comp
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap (map-pointed-map f))
      ( is-emb-is-equiv (is-equiv-tr-type-Ω (preserves-point-pointed-map f)))
      ( H (point-Pointed-Type A) (point-Pointed-Type A))

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : subgroup-Concrete-Group l2 G)
  where

  concrete-group-subgroup-Concrete-Group :
    Concrete-Group (l1 ⊔ l2)
  pr1 (pr1 concrete-group-subgroup-Concrete-Group) =
    classifying-pointed-type-subgroup-Concrete-Group G H
  pr2 (pr1 concrete-group-subgroup-Concrete-Group) =
    is-connected-classifying-type-subgroup-Concrete-Group G H
  pr2 concrete-group-subgroup-Concrete-Group =
    is-set-is-emb
      ( map-Ω (classifying-pointed-inclusion-subgroup-Concrete-Group G H))
      ( is-emb-map-Ω
        ( classifying-pointed-inclusion-subgroup-Concrete-Group G H)
        ( is-faithful-classifying-inclusion-subgroup-Concrete-Group G H))
      ( is-set-type-Concrete-Group G)

  hom-inclusion-subgroup-Concrete-Group :
    hom-Concrete-Group concrete-group-subgroup-Concrete-Group G
  pr1 hom-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group G H
  pr2 hom-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group G H
```

Dually, we say that a concrete `G`-set `X` is **free** if the type of orbits `X/G` is a set.

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-free-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-free-prop-action-∞-Group = is-set-Prop (orbit-action-∞-Group G X)

  is-free-action-∞-Group : UU (l1 ⊔ l2)
  is-free-action-∞-Group = type-Prop is-free-prop-action-∞-Group

  is-prop-is-free-action-∞-Group : is-prop is-free-action-∞-Group
  is-prop-is-free-action-∞-Group = is-prop-type-Prop is-free-prop-action-∞-Group

free-action-∞-Group :
  {l1 : Level} (l2 : Level) → ∞-Group l1 → UU (l1 ⊔ lsuc l2)
free-action-∞-Group l2 G =
  type-subtype (is-free-prop-action-∞-Group {l2 = l2} G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-free-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-free-prop-action-Concrete-Group =
    is-free-prop-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)

  is-free-action-Concrete-Group : UU (l1 ⊔ l2)
  is-free-action-Concrete-Group =
    is-free-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)

  is-prop-is-free-action-Concrete-Group : is-prop is-free-action-Concrete-Group
  is-prop-is-free-action-Concrete-Group =
    is-prop-is-free-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)

free-action-Concrete-Group :
  {l1 : Level} (l2 : Level) → Concrete-Group l1 → UU (l1 ⊔ lsuc l2)
free-action-Concrete-Group l2 G =
  Σ (action-Concrete-Group l2 G) (is-free-action-Concrete-Group G)
```

To see that this definition makes sense, we use the following generalization of the fundamental theorem of identity types:

## Theorem 19.6.2

Consider a connected type `A` equipped with an element `a : A`, and consider a family of types `B(x)` indexed by `x : A`.
Then the following are equivalent:

1. Every family of maps

   ```text
   f : Π(x : A) (a = x) → B(x)
   ```

   is a family of `k`-truncated maps.

2. The total space
   ```text
   Σ(x : A) B(x)
   ```
   is `(k + 1)`-truncated.

### Proof

_Proof._ Recall from Exercise 12.10 that the total space `Σ(x : A) B(x)` is `(k + 1)`-truncated if and only if the base point inclusion

```text
(x,y) : unit → Σ(x : A) B(x)
```

is `k`-truncated for every `(x,y) : Σ(x : A) B(x)`.
Since the type `A` is assumed to be connected, this is equivalent to the condition that every base point inclusion of the form

```text
(a,y) : unit → Σ(x : A) B(x)
```

is `k`-truncated.
Base point inclusions of this form are homotopic to `tot(f)`, where

```text
f : Π(x : A) (a = x) → B(x)
```

is given by `f(a,refl) ≔ y`.
The condition that `tot(f)` is `k`-truncated is by Lemma 11.1.2 equivalent to the condition that `f` is a family of `k`-truncated maps.
Furthermore, every family of maps `f : Π(x : A) (a = x) → B(x)` is of the above form by the type theoretic Yoneda lemma (Theorem 13.3.3), completing the proof. ◻

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  (tr-𝒫 :
    {X Y : UU (l1 ⊔ l2)} →
    X ≃ Y → is-in-subuniverse 𝒫 X → is-in-subuniverse 𝒫 Y)
  {A : UU l1} {B : A → UU l2}
  where

  forward-implication-subuniverse-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) →
    is-separated 𝒫 (Σ A B)
  forward-implication-subuniverse-equality-duality =
    forward-implication-structured-equality-duality tr-𝒫

  backward-implication-subuniverse-equality-duality :
    is-separated 𝒫 (Σ A B) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y))
  backward-implication-subuniverse-equality-duality =
    backward-implication-structured-equality-duality tr-𝒫

  subuniverse-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) ↔
    is-separated 𝒫 (Σ A B)
  subuniverse-equality-duality =
    structured-equality-duality tr-𝒫

module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  {A : UU l1} (a : A) {B : A → UU l2}
  where

  abstract
    forward-implication-extended-fundamental-theorem-id :
      is-0-connected A →
      ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)) →
      is-separated 𝒫 (Σ A B)
    forward-implication-extended-fundamental-theorem-id H K =
      forward-implication-subuniverse-equality-duality 𝒫
        ( is-in-subuniverse-equiv 𝒫)
        ( λ x f y b →
          apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected H a x)
            ( 𝒫 (fiber (f y) b))
            ( λ where refl → K f y b))

  abstract
    backward-implication-extended-fundamental-theorem-id :
      is-separated 𝒫 (Σ A B) →
      (f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)
    backward-implication-extended-fundamental-theorem-id K =
      backward-implication-subuniverse-equality-duality 𝒫
        ( is-in-subuniverse-equiv 𝒫)
        ( K)
        ( a)

  extended-fundamental-theorem-id :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)) ↔
    is-separated 𝒫 (Σ A B)
  extended-fundamental-theorem-id H =
    ( forward-implication-extended-fundamental-theorem-id H ,
      backward-implication-extended-fundamental-theorem-id)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (a : A) {B : A → UU l2}
  where

  forward-implication-extended-fundamental-theorem-id-truncated :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) → (x : A) → is-trunc-map k (f x)) →
    is-trunc (succ-𝕋 k) (Σ A B)
  forward-implication-extended-fundamental-theorem-id-truncated =
    forward-implication-extended-fundamental-theorem-id
      ( is-trunc-Prop k)
      ( a)

  backward-implication-extended-fundamental-theorem-id-truncated :
    is-trunc (succ-𝕋 k) (Σ A B) →
    (f : (x : A) → (a ＝ x) → B x) (x : A) → is-trunc-map k (f x)
  backward-implication-extended-fundamental-theorem-id-truncated =
    backward-implication-extended-fundamental-theorem-id
      ( is-trunc-Prop k)
      ( a)

  extended-fundamental-theorem-id-truncated :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-trunc-map k (f x)) ↔
    is-trunc (succ-𝕋 k) (Σ A B)
  pr1 (extended-fundamental-theorem-id-truncated H) =
    forward-implication-extended-fundamental-theorem-id-truncated H
  pr2 (extended-fundamental-theorem-id-truncated H) =
    backward-implication-extended-fundamental-theorem-id-truncated
```

By the previous theorem it follows that if the type of orbits of a concrete `G`-set `X` is a set, then the map `g ↦ gx` must be an embedding for every `x : X(⋆)`.
In other words, the action of `G` on `X` is free.

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  is-abstractly-free-prop-action-∞-Group : Prop (l1 ⊔ l2)
  is-abstractly-free-prop-action-∞-Group =
    Π-Prop
      ( type-action-∞-Group G X)
      ( λ x → is-emb-Prop (λ g → mul-action-∞-Group G X g x))

  is-abstractly-free-action-∞-Group : UU (l1 ⊔ l2)
  is-abstractly-free-action-∞-Group =
    type-Prop is-abstractly-free-prop-action-∞-Group

  is-prop-is-abstractly-free-action-∞-Group :
    is-prop is-abstractly-free-action-∞-Group
  is-prop-is-abstractly-free-action-∞-Group =
    is-prop-type-Prop is-abstractly-free-prop-action-∞-Group

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  abstract
    is-emb-tr-is-abstractly-free-action-∞-Group :
      is-abstractly-free-action-∞-Group G X →
      (u : classifying-type-∞-Group G)
      (x : type-action-∞-Group G X) →
      is-emb (λ (p : shape-∞-Group G ＝ u) → tr X p x)
    is-emb-tr-is-abstractly-free-action-∞-Group H u x =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) u)
        ( is-emb-Prop _)
        ( λ where refl → H x)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  abstract
    is-free-is-abstractly-free-action-∞-Group :
      is-abstractly-free-action-∞-Group G X →
      is-free-action-∞-Group G X
    is-free-is-abstractly-free-action-∞-Group H =
      forward-implication-extended-fundamental-theorem-id-truncated
        ( neg-one-𝕋)
        ( shape-∞-Group G)
        ( is-0-connected-classifying-type-∞-Group G)
        ( λ f u →
          is-prop-map-is-emb
            ( is-emb-htpy
              ( compute-map-out-of-identity-type f u)
              ( is-emb-tr-is-abstractly-free-action-∞-Group G X H u
                ( f (shape-∞-Group G) (unit-∞-Group G)))))

  abstract
    is-abstractly-free-is-free-action-∞-Group :
      is-free-action-∞-Group G X →
      is-abstractly-free-action-∞-Group G X
    is-abstractly-free-is-free-action-∞-Group H x =
      is-emb-is-prop-map
        ( backward-implication-extended-fundamental-theorem-id-truncated
          ( neg-one-𝕋)
          ( shape-∞-Group G)
          ( H)
          ( λ u p → tr X p x)
          ( shape-∞-Group G))

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-abstractly-free-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-abstractly-free-prop-action-Concrete-Group =
    is-abstractly-free-prop-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-abstractly-free-action-Concrete-Group : UU (l1 ⊔ l2)
  is-abstractly-free-action-Concrete-Group =
    is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-prop-is-abstractly-free-action-Concrete-Group :
    is-prop is-abstractly-free-action-Concrete-Group
  is-prop-is-abstractly-free-action-Concrete-Group =
    is-prop-is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-abstractly-free-is-free-action-Concrete-Group :
    is-free-action-Concrete-Group G X →
    is-abstractly-free-action-Concrete-Group G X
  is-abstractly-free-is-free-action-Concrete-Group =
    is-abstractly-free-is-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-free-is-abstractly-free-action-Concrete-Group :
    is-abstractly-free-action-Concrete-Group G X →
    is-free-action-Concrete-Group G X
  is-free-is-abstractly-free-action-Concrete-Group =
    is-free-is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)
```

## Remark 19.6.3

Theorem 19.6.2 can be generalized further.
We include this generalization in Exercise 19.14.

## Example 19.6.4

Consider two sets `A` and `B`, and a universe `𝒰` containing both of them.
Then the automorphism group `Aut(B)` acts on the decidable embeddings `B ↪ᵈ A` by precomposition.
Its type of orbits is the binomial type

```text
binom(A, B) ≔ Σ(X : 𝒰_B) X ↪ᵈ A,
```

which we introduced in Definition 17.6.4.
By Proposition 17.6.6 it follows that `binom(A, B)` is a set, so the action of `Aut(B)` on `B ↪ᵈ A` is free.
Note that we didn’t need to assume that `A` and `B` are sets: the action of `Aut(B)` on `B ↪ᵈ A` is always free.

Similarly, we have an action of the automorphism group `Aut(B)` on the surjective maps `A ↠ B` by postcomposition.
Its type of orbits is the Stirling type of the second kind

```text
Stirling(A, B) ≔ Σ(X : 𝒰_B) A ↠ X,
```

which we introduced in Exercise 18.13.
Assuming that `B` is a set, it was shown in Exercise 18.13 that `Stirling(A, B)` is a set.
In other words, the action of `Aut(B)` on `A ↠ B` is free.

BENCHMARK PROBLEM

## Example 19.6.5

In Exercise 17.20 we introduced the type

```text
D̃_n ≔ Σ(X : BS_2) Σ(Y : X → 𝔽) (Fin{n} ≃ Π(x : X) Y(x)).
```

Notice that this type is the type of orbits of the `ℤ/2`-set `D_n` given by

```text
D_n(X) ≔ Σ(Y : X → 𝔽) (Fin{n} ≃ Π(x : X) Y(x)).
```

The fact that this is a family of sets is a nice exercise.
Note that there is a surjective morphism of `ℤ/2`-sets from `D_n(Fin{2})` to the `ℤ/2` set of divisors of `n`, where the action is given by `d ↦ n/d`.
The concrete `ℤ/2`-action `D_n` is transitive precisely when `n` is either `1` or a prime, and it is free precisely when `n` is not a square.
Combining these two observations, we see that `n` is prime if and only if this action is both transitive and free.
In other words, `n` is prime if and only if the type `D̃_n` of orbits is contractible.

BENCHMARK PROBLEM

`G`-sets which are both transitive and free are very special.
Such `G`-sets are called **`G`-torsors**.
Note that a `G`-set `X` is a `G`-torsor if and only if the type of orbits `X/G` is contractible.
By the fundamental theorem of identity types, this implies that the family of maps

```text
Π(v : BG) (u = v) → X(v)
```

is a family of equivalences, where `(u,x)` is the center of contraction of `X/G`.
It follows that a concrete `G`-set `X : BG → Set_𝒰` is a `G`-torsor if and only if it is in the image of

```text
Id_ : BG → (BG → Set_𝒰).
```

However, we know from Exercise 17.6 that this map is an embedding, so it follows that the type of concrete `G`-torsors is equivalent to `BG`.
On the other hand, the type of concrete `G`-torsors is equivalent to the type of abstract `G`-torsors.
This suggests that the classifying type `BG` of any group `G` can be constructed as the type of abstract `G`-torsors, and this is indeed one way to construct the classifying type of a group `G`.

```agda
module _
  {l1 : Level} (G : Concrete-Group l1)
  where

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group G) → Set l1
  Id-BG-Set X Y = Id-Set (classifying-1-type-Concrete-Group G) X Y

  principal-torsor-Concrete-Group :
    classifying-type-Concrete-Group G → action-Concrete-Group l1 G
  principal-torsor-Concrete-Group = Id-BG-Set

module _
  {l1 : Level} (G : Group l1)
  where

  principal-action-Group : action-Group G l1
  pr1 principal-action-Group = set-Group G
  pr1 (pr2 principal-action-Group) g = equiv-mul-Group G g
  pr2 (pr2 principal-action-Group) {g} {h} =
    eq-htpy-equiv (associative-mul-Group G g h)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : type-action-Group G X → type-action-Group G Y)
  where

  preserves-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  preserves-action-Group =
    (g : type-Group G) →
    coherence-square-maps f (mul-action-Group G X g) (mul-action-Group G Y g) f

  is-prop-preserves-action-Group : is-prop preserves-action-Group
  is-prop-preserves-action-Group =
    is-prop-iterated-Π 2
      ( λ g x →
        is-set-type-action-Group G Y
          ( f (mul-action-Group G X g x))
          ( mul-action-Group G Y g (f x)))

  preserves-action-prop-Group : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 preserves-action-prop-Group = preserves-action-Group
  pr2 preserves-action-prop-Group = is-prop-preserves-action-Group

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  hom-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  hom-action-Group =
    Σ ( type-action-Group G X → type-action-Group G Y)
      ( preserves-action-Group G X Y)

  map-hom-action-Group :
    hom-action-Group → type-action-Group G X → type-action-Group G Y
  map-hom-action-Group = pr1

  preserves-action-hom-action-Group :
    (f : hom-action-Group) →
    preserves-action-Group G X Y (map-hom-action-Group f)
  preserves-action-hom-action-Group = pr2

module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3) (f : hom-action-Group G X Y)
  where

  htpy-hom-action-Group :
    (g : hom-action-Group G X Y) → UU (l2 ⊔ l3)
  htpy-hom-action-Group g =
    map-hom-action-Group G X Y f ~ map-hom-action-Group G X Y g

  refl-htpy-hom-action-Group : htpy-hom-action-Group f
  refl-htpy-hom-action-Group = refl-htpy

  htpy-eq-hom-action-Group :
    (g : hom-action-Group G X Y) →
    f ＝ g → htpy-hom-action-Group g
  htpy-eq-hom-action-Group .f refl =
    refl-htpy-hom-action-Group

  is-torsorial-htpy-hom-action-Group :
    is-torsorial htpy-hom-action-Group
  is-torsorial-htpy-hom-action-Group =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-hom-action-Group G X Y f))
      ( λ g →
        is-prop-Π
          ( λ x →
            is-prop-Π
              ( λ y →
                is-set-type-Set
                  ( set-action-Group G Y)
                  ( g (mul-action-Group G X x y))
                  ( mul-action-Group G Y x (g y)))))
      ( map-hom-action-Group G X Y f)
      ( refl-htpy)
      ( preserves-action-hom-action-Group G X Y f)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  equiv-action-Group =
    Σ ( type-action-Group G X ≃ type-action-Group G Y)
      ( λ e →
        ( g : type-Group G) →
        coherence-square-maps
          ( map-equiv e)
          ( mul-action-Group G X g)
          ( mul-action-Group G Y g)
          ( map-equiv e))

  equiv-equiv-action-Group :
    equiv-action-Group → type-action-Group G X ≃ type-action-Group G Y
  equiv-equiv-action-Group = pr1

  map-equiv-action-Group :
    equiv-action-Group → type-action-Group G X → type-action-Group G Y
  map-equiv-action-Group e =
    map-equiv (equiv-equiv-action-Group e)

  is-equiv-map-equiv-action-Group :
    (e : equiv-action-Group) → is-equiv (map-equiv-action-Group e)
  is-equiv-map-equiv-action-Group e =
    is-equiv-map-equiv (equiv-equiv-action-Group e)

  coherence-square-equiv-action-Group :
    (e : equiv-action-Group) (g : type-Group G) →
    coherence-square-maps
      ( map-equiv-action-Group e)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( map-equiv-action-Group e)
  coherence-square-equiv-action-Group = pr2

  hom-equiv-action-Group :
    equiv-action-Group → hom-action-Group G X Y
  pr1 (hom-equiv-action-Group e) = map-equiv-action-Group e
  pr2 (hom-equiv-action-Group e) = coherence-square-equiv-action-Group e

module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  id-equiv-action-Group : equiv-action-Group G X X
  pr1 id-equiv-action-Group = id-equiv
  pr2 id-equiv-action-Group g = refl-htpy

module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  equiv-eq-action-Group :
    (Y : action-Group G l2) → X ＝ Y → equiv-action-Group G X Y
  equiv-eq-action-Group .X refl = id-equiv-action-Group G X

  abstract
    is-torsorial-equiv-action-Group :
      is-torsorial (λ (Y : action-Group G l2) → equiv-action-Group G X Y)
    is-torsorial-equiv-action-Group =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv-Set (pr1 X))
        ( pr1 X , id-equiv)
        ( is-contr-equiv
          ( Σ ( hom-Group G (symmetric-Group (pr1 X)))
              ( htpy-hom-Group G (symmetric-Group (pr1 X)) (pr2 X)))
          ( equiv-tot
            ( λ f →
              equiv-Π-equiv-family
                ( λ g →
                  inv-equiv
                    ( extensionality-equiv
                      ( map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
                      ( map-hom-Group G (symmetric-Group (pr1 X)) f g)))))
          ( is-torsorial-htpy-hom-Group G
            ( symmetric-Group (pr1 X))
            ( pr2 X)))

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (e : equiv-action-Group G X Y)
  where

  htpy-equiv-action-Group : (f : equiv-action-Group G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-action-Group f =
    htpy-hom-action-Group G X Y
      ( hom-equiv-action-Group G X Y e)
      ( hom-equiv-action-Group G X Y f)

  refl-htpy-equiv-action-Group : htpy-equiv-action-Group e
  refl-htpy-equiv-action-Group =
    refl-htpy-hom-action-Group G X Y (hom-equiv-action-Group G X Y e)

  htpy-eq-equiv-action-Group :
    (f : equiv-action-Group G X Y) → e ＝ f → htpy-equiv-action-Group f
  htpy-eq-equiv-action-Group .e refl = refl-htpy-equiv-action-Group

  is-torsorial-htpy-equiv-action-Group : is-torsorial htpy-equiv-action-Group
  is-torsorial-htpy-equiv-action-Group =
    is-contr-equiv
      ( Σ ( Σ ( hom-action-Group G X Y) (λ f → is-equiv (pr1 f)))
          ( λ f →
            htpy-hom-action-Group G X Y
              ( hom-equiv-action-Group G X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-action-Group G X Y
            ( hom-equiv-action-Group G X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ ((f , E) , H) → id-equiv))
      ( is-torsorial-Eq-subtype
        ( is-torsorial-htpy-hom-action-Group G X Y
          ( hom-equiv-action-Group G X Y e))
        ( λ f → is-property-is-equiv (pr1 f))
        ( hom-equiv-action-Group G X Y e)
        ( refl-htpy)
        ( is-equiv-map-equiv (pr1 e)))

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3) (Z : action-Group G l4)
  where

  comp-equiv-action-Group :
    equiv-action-Group G Y Z → equiv-action-Group G X Y →
    equiv-action-Group G X Z
  pr1 (comp-equiv-action-Group (f , K) (e , H)) = f ∘e e
  pr2 (comp-equiv-action-Group (f , K) (e , H)) g =
    pasting-horizontal-coherence-square-maps
      ( map-equiv e)
      ( map-equiv f)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( mul-action-Group G Z g)
      ( map-equiv e)
      ( map-equiv f)
      ( H g)
      ( K g)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  mere-equiv-prop-action-Group : Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-prop-action-Group = trunc-Prop (equiv-action-Group G X Y)

  mere-equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-action-Group = type-Prop mere-equiv-prop-action-Group

module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  is-torsor-prop-action-Group : Prop (l1 ⊔ l2)
  is-torsor-prop-action-Group =
    mere-equiv-prop-action-Group G (principal-action-Group G) X

  is-torsor-Group : UU (l1 ⊔ l2)
  is-torsor-Group = type-Prop is-torsor-prop-action-Group

  is-prop-is-torsor-Group : is-prop is-torsor-Group
  is-prop-is-torsor-Group = is-prop-type-Prop is-torsor-prop-action-Group

module _
  {l1 : Level} (G : Group l1)
  where

  Torsor-Group : (l : Level) → UU (l1 ⊔ lsuc l)
  Torsor-Group l = Σ (action-Group G l) (is-torsor-Group G)

module _
  {l1 l : Level} (G : Group l1) (X : Torsor-Group G l)
  where

  action-Torsor-Group : action-Group G l
  action-Torsor-Group = pr1 X

  set-Torsor-Group : Set l
  set-Torsor-Group = set-action-Group G action-Torsor-Group

  type-Torsor-Group : UU l
  type-Torsor-Group = type-Set set-Torsor-Group

  is-set-type-Torsor-Group : is-set type-Torsor-Group
  is-set-type-Torsor-Group = is-set-type-Set set-Torsor-Group

  mul-hom-Torsor-Group : hom-Group G (symmetric-Group set-Torsor-Group)
  mul-hom-Torsor-Group = pr2 action-Torsor-Group

  equiv-mul-Torsor-Group : type-Group G → type-Torsor-Group ≃ type-Torsor-Group
  equiv-mul-Torsor-Group = equiv-mul-action-Group G action-Torsor-Group

  mul-Torsor-Group : type-Group G → type-Torsor-Group → type-Torsor-Group
  mul-Torsor-Group = mul-action-Group G action-Torsor-Group

  is-torsor-action-Torsor-Group : is-torsor-Group G action-Torsor-Group
  is-torsor-action-Torsor-Group = pr2 X

module _
  {l1 : Level} (G : Group l1)
  where

  principal-Torsor-Group : Torsor-Group G l1
  pr1 principal-Torsor-Group = principal-action-Group G
  pr2 principal-Torsor-Group =
    unit-trunc-Prop (id-equiv-action-Group G (principal-action-Group G))

module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Group G l2)
  where

  equiv-Torsor-Group :
    {l3 : Level} (Y : Torsor-Group G l3) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-Torsor-Group Y =
    equiv-action-Group G (action-Torsor-Group G X) (action-Torsor-Group G Y)

  id-equiv-Torsor-Group : equiv-Torsor-Group X
  id-equiv-Torsor-Group = id-equiv-action-Group G (action-Torsor-Group G X)

  equiv-eq-Torsor-Group :
    (Y : Torsor-Group G l2) → X ＝ Y → equiv-Torsor-Group Y
  equiv-eq-Torsor-Group .X refl = id-equiv-Torsor-Group

  is-torsorial-equiv-Torsor-Group :
    is-torsorial equiv-Torsor-Group
  is-torsorial-equiv-Torsor-Group =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv-action-Group G (action-Torsor-Group G X))
      ( is-prop-is-torsor-Group G)
      ( action-Torsor-Group G X)
      ( id-equiv-Torsor-Group)
      ( is-torsor-action-Torsor-Group G X)

  is-equiv-equiv-eq-Torsor-Group :
    (Y : Torsor-Group G l2) →
    is-equiv (equiv-eq-Torsor-Group Y)
  is-equiv-equiv-eq-Torsor-Group =
    fundamental-theorem-id
      is-torsorial-equiv-Torsor-Group
      equiv-eq-Torsor-Group

  eq-equiv-Torsor-Group :
    (Y : Torsor-Group G l2) → equiv-Torsor-Group Y → X ＝ Y
  eq-equiv-Torsor-Group Y =
    map-inv-is-equiv (is-equiv-equiv-eq-Torsor-Group Y)

  extensionality-Torsor-Group :
    (Y : Torsor-Group G l2) → (X ＝ Y) ≃ equiv-Torsor-Group Y
  pr1 (extensionality-Torsor-Group Y) = equiv-eq-Torsor-Group Y
  pr2 (extensionality-Torsor-Group Y) = is-equiv-equiv-eq-Torsor-Group Y

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  (e : equiv-Torsor-Group G X Y)
  where

  htpy-equiv-Torsor-Group :
    equiv-Torsor-Group G X Y → UU (l2 ⊔ l3)
  htpy-equiv-Torsor-Group =
    htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  refl-htpy-equiv-Torsor-Group :
    htpy-equiv-Torsor-Group e
  refl-htpy-equiv-Torsor-Group =
    refl-htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  htpy-eq-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    e ＝ f → htpy-equiv-Torsor-Group f
  htpy-eq-equiv-Torsor-Group .e refl =
    refl-htpy-equiv-Torsor-Group

  is-torsorial-htpy-equiv-Torsor-Group :
    is-torsorial htpy-equiv-Torsor-Group
  is-torsorial-htpy-equiv-Torsor-Group =
    is-torsorial-htpy-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( e)

  is-equiv-htpy-eq-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    is-equiv (htpy-eq-equiv-Torsor-Group f)
  is-equiv-htpy-eq-equiv-Torsor-Group =
    fundamental-theorem-id
      is-torsorial-htpy-equiv-Torsor-Group
      htpy-eq-equiv-Torsor-Group

  extensionality-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    (e ＝ f) ≃ htpy-equiv-Torsor-Group f
  pr1 (extensionality-equiv-Torsor-Group f) =
    htpy-eq-equiv-Torsor-Group f
  pr2 (extensionality-equiv-Torsor-Group f) =
    is-equiv-htpy-eq-equiv-Torsor-Group f

  eq-htpy-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) → htpy-equiv-Torsor-Group f → e ＝ f
  eq-htpy-equiv-Torsor-Group f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Torsor-Group f)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  is-set-equiv-Torsor-Group :
    is-set (equiv-Torsor-Group G X Y)
  is-set-equiv-Torsor-Group e f =
    is-prop-equiv
      ( extensionality-equiv-Torsor-Group G X Y e f)
      ( is-prop-Π
        ( λ x →
          is-set-type-Torsor-Group G Y
            ( map-equiv (pr1 e) x)
            ( map-equiv (pr1 f) x)))

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  map-inv-equiv-action-Group :
    equiv-action-Group G X Y → type-action-Group G Y → type-action-Group G X
  map-inv-equiv-action-Group e =
    map-inv-equiv (equiv-equiv-action-Group G X Y e)

  preserves-action-map-inv-equiv-action-Group :
    (e : equiv-action-Group G X Y) →
    preserves-action-Group G Y X (map-inv-equiv-action-Group e)
  preserves-action-map-inv-equiv-action-Group (e , H) g =
    horizontal-inv-equiv-coherence-square-maps
      ( e)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( e)
      ( H g)

  inv-equiv-action-Group :
    equiv-action-Group G X Y → equiv-action-Group G Y X
  pr1 (inv-equiv-action-Group (e , H)) = inv-equiv e
  pr2 (inv-equiv-action-Group e) =
    preserves-action-map-inv-equiv-action-Group e

  hom-inv-equiv-action-Group :
    equiv-action-Group G X Y → hom-action-Group G Y X
  hom-inv-equiv-action-Group e =
    hom-equiv-action-Group G Y X (inv-equiv-action-Group e)

module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  (Z : Torsor-Group G l4)
  where

  comp-equiv-Torsor-Group :
    equiv-Torsor-Group G Y Z →
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G X Z
  comp-equiv-Torsor-Group =
    comp-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)
      ( action-Torsor-Group G Z)

  comp-equiv-Torsor-Group' :
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G Y Z →
    equiv-Torsor-Group G X Z
  comp-equiv-Torsor-Group' e f =
    comp-equiv-Torsor-Group f e

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  inv-equiv-Torsor-Group :
    equiv-Torsor-Group G X Y →
    equiv-Torsor-Group G Y X
  inv-equiv-Torsor-Group =
    inv-equiv-action-Group G
      ( action-Torsor-Group G X)
      ( action-Torsor-Group G Y)

module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1)
  (X1 : Torsor-Group G l2)
  (X2 : Torsor-Group G l3)
  (X3 : Torsor-Group G l4)
  (X4 : Torsor-Group G l5)
  where

  associative-comp-equiv-Torsor-Group :
    (h : equiv-Torsor-Group G X3 X4)
    (g : equiv-Torsor-Group G X2 X3)
    (f : equiv-Torsor-Group G X1 X2) →
    ( comp-equiv-Torsor-Group G X1 X2 X4
      ( comp-equiv-Torsor-Group G X2 X3 X4 h g)
      ( f)) ＝
    ( comp-equiv-Torsor-Group G X1 X3 X4 h
      ( comp-equiv-Torsor-Group G X1 X2 X3 g f))
  associative-comp-equiv-Torsor-Group h g f =
    eq-htpy-equiv-Torsor-Group G X1 X4
      ( comp-equiv-Torsor-Group G X1 X2 X4
        ( comp-equiv-Torsor-Group G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-Torsor-Group G X1 X3 X4 h
        ( comp-equiv-Torsor-Group G X1 X2 X3 g f))
      ( refl-htpy)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Torsor-Group G l2)
  (Y : Torsor-Group G l3)
  where

  left-unit-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X Y Y (id-equiv-Torsor-Group G Y) f) ＝ f
  left-unit-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X Y
      ( comp-equiv-Torsor-Group G X Y Y
        ( id-equiv-Torsor-Group G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X X Y f (id-equiv-Torsor-Group G X)) ＝ f
  right-unit-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X Y
      ( comp-equiv-Torsor-Group G X X Y f
        ( id-equiv-Torsor-Group G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G X Y X (inv-equiv-Torsor-Group G X Y f) f) ＝
    ( id-equiv-Torsor-Group G X)
  left-inverse-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G X X
      ( comp-equiv-Torsor-Group G X Y X
        ( inv-equiv-Torsor-Group G X Y f)
        ( f))
      ( id-equiv-Torsor-Group G X)
      ( is-retraction-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-Torsor-Group :
    (f : equiv-Torsor-Group G X Y) →
    ( comp-equiv-Torsor-Group G Y X Y f (inv-equiv-Torsor-Group G X Y f)) ＝
    ( id-equiv-Torsor-Group G Y)
  right-inverse-law-comp-equiv-Torsor-Group f =
    eq-htpy-equiv-Torsor-Group G Y Y
      ( comp-equiv-Torsor-Group G Y X Y f (inv-equiv-Torsor-Group G X Y f))
      ( id-equiv-Torsor-Group G Y)
      ( is-section-map-inv-equiv (pr1 f))

module _
  {l1 : Level} (G : Group l1)
  where

  preserves-mul-equiv-eq-Torsor-Group :
    {l2 : Level} (X Y Z : Torsor-Group G l2)
    (p : X ＝ Y) (q : Y ＝ Z) →
    ( equiv-eq-Torsor-Group G X Z (p ∙ q)) ＝
    ( comp-equiv-Torsor-Group G X Y Z
      ( equiv-eq-Torsor-Group G Y Z q)
      ( equiv-eq-Torsor-Group G X Y p))
  preserves-mul-equiv-eq-Torsor-Group X .X Z refl q =
    inv
      ( right-unit-law-comp-equiv-Torsor-Group G X Z
        ( equiv-eq-Torsor-Group G X Z q))

module _
  {l1 : Level} (G : Group l1)
  where

  aut-principal-Torsor-Group : Group l1
  pr1 (pr1 (pr1 aut-principal-Torsor-Group)) =
    equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr1 (pr1 aut-principal-Torsor-Group)) =
    is-set-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr1 aut-principal-Torsor-Group)) =
    comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr1 aut-principal-Torsor-Group)) =
    associative-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr1 (pr2 aut-principal-Torsor-Group)) =
    id-equiv-Torsor-Group G (principal-Torsor-Group G)
  pr1 (pr2 (pr1 (pr2 aut-principal-Torsor-Group))) =
    left-unit-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr1 (pr2 aut-principal-Torsor-Group))) =
    right-unit-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr2 aut-principal-Torsor-Group)) =
    inv-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (pr2 (pr2 (pr2 aut-principal-Torsor-Group))) =
    left-inverse-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr2 (pr2 (pr2 (pr2 aut-principal-Torsor-Group))) =
    right-inverse-law-comp-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)

module _
  {l1 l2 : Level} (G : Group l1) (X : Torsor-Group G l2)
  where

  mere-eq-Torsor-Group :
    (Y : Torsor-Group G l2) → mere-eq X Y
  mere-eq-Torsor-Group Y =
    map-binary-trunc-Prop
      ( λ e f →
        eq-equiv-Torsor-Group G X Y
          ( comp-equiv-Torsor-Group G
            ( X)
            ( principal-Torsor-Group G)
            ( Y)
            ( f)
            ( inv-equiv-Torsor-Group G
              ( principal-Torsor-Group G)
              ( X)
              ( e))))
      ( pr2 X)
      ( pr2 Y)

module _
  {l1 : Level} (G : Group l1)
  where

  is-0-connected-Torsor-Group :
    is-0-connected (Torsor-Group G l1)
  is-0-connected-Torsor-Group =
    is-0-connected-mere-eq
      ( principal-Torsor-Group G)
      ( mere-eq-Torsor-Group G (principal-Torsor-Group G))

module _
  {l1 : Level} (G : Group l1)
  where

  Eq-Torsor-Group :
    (X : Torsor-Group G l1) → UU l1
  Eq-Torsor-Group X = type-Torsor-Group G X

  refl-Eq-Torsor-Group :
    Eq-Torsor-Group (principal-Torsor-Group G)
  refl-Eq-Torsor-Group = unit-Group G

  Eq-equiv-Torsor-Group :
    (X : Torsor-Group G l1) →
    equiv-Torsor-Group G (principal-Torsor-Group G) X →
    Eq-Torsor-Group X
  Eq-equiv-Torsor-Group X (e , H) = map-equiv e (unit-Group G)

  preserves-mul-Eq-equiv-Torsor-Group :
    ( e f :
      equiv-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)) →
    ( Eq-equiv-Torsor-Group
      ( principal-Torsor-Group G)
      ( comp-equiv-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( f)
        ( e))) ＝
    ( mul-Group G
      ( Eq-equiv-Torsor-Group
        ( principal-Torsor-Group G)
        ( e))
      ( Eq-equiv-Torsor-Group
        ( principal-Torsor-Group G)
        ( f)))
  preserves-mul-Eq-equiv-Torsor-Group (e , H) (f , K) =
    ( ap
      ( map-equiv f)
      ( inv (right-unit-law-mul-Group G (map-equiv e (unit-Group G))))) ∙
    ( K (map-equiv e (unit-Group G)) (unit-Group G))

  equiv-Eq-Torsor-Group :
    Eq-Torsor-Group (principal-Torsor-Group G) →
    equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
  pr1 (equiv-Eq-Torsor-Group u) = equiv-mul-Group' G u
  pr2 (equiv-Eq-Torsor-Group u) g x = associative-mul-Group G g x u

  is-section-equiv-Eq-Torsor-Group :
    ( Eq-equiv-Torsor-Group (principal-Torsor-Group G) ∘
      equiv-Eq-Torsor-Group) ~
    ( id)
  is-section-equiv-Eq-Torsor-Group u = left-unit-law-mul-Group G u

  is-retraction-equiv-Eq-Torsor-Group :
    is-retraction
      ( Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( equiv-Eq-Torsor-Group)
  is-retraction-equiv-Eq-Torsor-Group e =
    eq-htpy-equiv-Torsor-Group G
      ( principal-Torsor-Group G)
      ( principal-Torsor-Group G)
      ( equiv-Eq-Torsor-Group
        ( Eq-equiv-Torsor-Group (principal-Torsor-Group G) e))
      ( e)
      ( λ g →
        ( inv (pr2 e g (unit-Group G))) ∙
        ( ap (map-equiv (pr1 e)) (right-unit-law-mul-Group G g)))

  abstract
    is-equiv-Eq-equiv-Torsor-Group :
      (X : Torsor-Group G l1) →
      is-equiv (Eq-equiv-Torsor-Group X)
    is-equiv-Eq-equiv-Torsor-Group X =
      apply-universal-property-trunc-Prop
        ( is-torsor-action-Torsor-Group G X)
        ( is-equiv-Prop (Eq-equiv-Torsor-Group X))
        ( λ e →
          tr
            ( λ Y → is-equiv (Eq-equiv-Torsor-Group Y))
            ( eq-equiv-Torsor-Group G (principal-Torsor-Group G) X e)
            ( is-equiv-is-invertible
                equiv-Eq-Torsor-Group
                is-section-equiv-Eq-Torsor-Group
                is-retraction-equiv-Eq-Torsor-Group))

  equiv-Eq-equiv-Torsor-Group :
    (X : Torsor-Group G l1) →
    (principal-Torsor-Group G ＝ X) ≃ Eq-Torsor-Group X
  equiv-Eq-equiv-Torsor-Group X =
    ( Eq-equiv-Torsor-Group X , is-equiv-Eq-equiv-Torsor-Group X) ∘e
    ( extensionality-Torsor-Group G (principal-Torsor-Group G) X)

  preserves-mul-equiv-Eq-equiv-Torsor-Group :
    { p q : principal-Torsor-Group G ＝ principal-Torsor-Group G} →
    map-equiv (equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G)) (p ∙ q) ＝
    mul-Group G
      ( map-equiv (equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G)) p)
      ( map-equiv (equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G)) q)
  preserves-mul-equiv-Eq-equiv-Torsor-Group {p} {q} =
    ( ap
      ( Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( preserves-mul-equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( p)
        ( q))) ∙
    ( preserves-mul-Eq-equiv-Torsor-Group
      ( equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( p))
      ( equiv-eq-Torsor-Group G
        ( principal-Torsor-Group G)
        ( principal-Torsor-Group G)
        ( q)))

  ∞-group-Group : ∞-Group (lsuc l1)
  pr1 (pr1 ∞-group-Group) = Torsor-Group G l1
  pr2 (pr1 ∞-group-Group) = principal-Torsor-Group G
  pr2 ∞-group-Group = is-0-connected-Torsor-Group G

  concrete-group-Group : Concrete-Group (lsuc l1)
  pr1 concrete-group-Group = ∞-group-Group
  pr2 concrete-group-Group =
    is-set-equiv
      ( type-Group G)
      ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G))
      ( is-set-type-Group G)

  classifying-type-Group : UU (lsuc l1)
  classifying-type-Group = classifying-type-Concrete-Group concrete-group-Group

  shape-Group : classifying-type-Group
  shape-Group = shape-Concrete-Group concrete-group-Group

  is-0-connected-classifying-type-Group : is-0-connected classifying-type-Group
  is-0-connected-classifying-type-Group =
    is-0-connected-classifying-type-Concrete-Group concrete-group-Group

  group-concrete-group-Group :
    iso-Group (group-Concrete-Group concrete-group-Group) G
  group-concrete-group-Group =
    iso-equiv-Group
      ( group-Concrete-Group concrete-group-Group)
      ( G)
      ( ( equiv-Eq-equiv-Torsor-Group (principal-Torsor-Group G)) ,
        ( λ {p} {q} → preserves-mul-equiv-Eq-equiv-Torsor-Group {p} {q}))
```
