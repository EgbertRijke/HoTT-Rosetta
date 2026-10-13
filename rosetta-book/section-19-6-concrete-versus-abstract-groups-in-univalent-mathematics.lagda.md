# Section 19.6 Concrete versus abstract groups in univalent mathematics

```agda
module section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-16-3-finite-types
open import section-18-5-set-truncations
open import section-19-1-the-type-of-all-groups
open import section-19-2-group-homomorphisms
open import section-19-4-homotopy-groups-of-types
open import section-19-5-the-eckmann-hilton-argument
```

In univalent mathematics there is another exciting perspective on group theory.
We won’t be able to go into full detail here, but we can sketch some of the key ideas.
To learn more about this beautiful univalent perspective on group theory, I recommend the forthcoming _Symmetry_ book \[citation: `symmetrybook`\].

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

Dually, we say that a concrete `G`-set `X` is **free** if the type of orbits `X/G` is a set.
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

By the previous theorem it follows that if the type of orbits of a concrete `G`-set `X` is a set, then the map `g ↦ gx` must be an embedding for every `x : X(⋆)`.
In other words, the action of `G` on `X` is free.

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
