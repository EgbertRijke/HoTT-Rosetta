# Section 19.2 Group homomorphisms

```agda
module section-19-2-group-homomorphisms where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-19-1-the-type-of-all-groups
```

## Definition 19.2.1

Let `G` and `H` be (semi)groups.
A **homomorphism** of (semi)groups from `G` to `H` is a pair `(f,μ_f)` consisting of a function `f : G → H` between their underlying types, and a homotopy

```text
μ_f : Π(x,y : G) f(μ_G(x,y)) = μ_H(f(x),f(y))
```

witnessing that `f` preserves the binary operation of `G`.
We will write

```text
hom(G,H)
```

for the type of all (semi)group homomorphisms from `G` to `H`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul μA μB f = {x y : A} → f (μA x y) ＝ μB (f x) (f y)

  preserves-mul' : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul' μA μB f = (x y : A) → f (μA x y) ＝ μB (f x) (f y)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-prop-Semigroup :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Semigroup f =
    implicit-Π-Prop
      ( type-Semigroup G)
      ( λ x →
        implicit-Π-Prop
          ( type-Semigroup G)
          ( λ y →
            Id-Prop
              ( set-Semigroup H)
              ( f (mul-Semigroup G x y))
              ( mul-Semigroup H (f x) (f y))))

  preserves-mul-prop-Semigroup' :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Semigroup' f =
    implicit-Π-Prop
      ( type-Semigroup G)
      ( λ x →
        implicit-Π-Prop
          ( type-Semigroup G)
          ( λ y →
            Id-Prop
              ( set-Semigroup H)
              ( f (mul-Semigroup' G x y))
              ( mul-Semigroup H (f x) (f y))))

  preserves-mul-Semigroup :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup f =
    type-Prop (preserves-mul-prop-Semigroup f)

  preserves-mul-Semigroup' :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup' f =
    type-Prop (preserves-mul-prop-Semigroup' f)

  is-prop-preserves-mul-Semigroup :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup f)
  is-prop-preserves-mul-Semigroup f =
    is-prop-type-Prop (preserves-mul-prop-Semigroup f)

  is-prop-preserves-mul-Semigroup' :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup' f)
  is-prop-preserves-mul-Semigroup' f =
    is-prop-type-Prop (preserves-mul-prop-Semigroup' f)

  hom-Semigroup : UU (l1 ⊔ l2)
  hom-Semigroup =
    Σ ( type-Semigroup G → type-Semigroup H)
      ( preserves-mul-Semigroup)

  map-hom-Semigroup :
    hom-Semigroup → type-Semigroup G → type-Semigroup H
  map-hom-Semigroup f = pr1 f

  preserves-mul-hom-Semigroup :
    (f : hom-Semigroup) → preserves-mul-Semigroup (map-hom-Semigroup f)
  preserves-mul-hom-Semigroup f = pr2 f

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group f =
    preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H) f

  preserves-mul-Group' : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group' f =
    preserves-mul-Semigroup' (semigroup-Group G) (semigroup-Group H) f

  is-prop-preserves-mul-Group :
    (f : type-Group G → type-Group H) → is-prop (preserves-mul-Group f)
  is-prop-preserves-mul-Group =
    is-prop-preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-prop-Group : (type-Group G → type-Group H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Group =
    preserves-mul-prop-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-Group : UU (l1 ⊔ l2)
  hom-Group =
    hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  map-hom-Group : hom-Group → type-Group G → type-Group H
  map-hom-Group = pr1

  preserves-mul-hom-Group :
    (f : hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = pr2
```

## Remark 19.2.2

Since it is a property for a function to preserve the multiplication of a semigroup, it follows easily that equality of semigroup homomorphisms is equivalent to the type of homotopies between their underlying functions.
In particular, it follows that the type of homomorphisms of semigroups is a set.

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  htpy-hom-Semigroup : (f g : hom-Semigroup G H) → UU (l1 ⊔ l2)
  htpy-hom-Semigroup f g = map-hom-Semigroup G H f ~ map-hom-Semigroup G H g

  refl-htpy-hom-Semigroup : (f : hom-Semigroup G H) → htpy-hom-Semigroup f f
  refl-htpy-hom-Semigroup f = refl-htpy

  htpy-eq-hom-Semigroup :
    (f g : hom-Semigroup G H) → f ＝ g → htpy-hom-Semigroup f g
  htpy-eq-hom-Semigroup f .f refl = refl-htpy-hom-Semigroup f

  abstract
    is-torsorial-htpy-hom-Semigroup :
      (f : hom-Semigroup G H) → is-torsorial (htpy-hom-Semigroup f)
    is-torsorial-htpy-hom-Semigroup f =
      is-torsorial-Eq-subtype
        ( is-torsorial-htpy (map-hom-Semigroup G H f))
        ( is-prop-preserves-mul-Semigroup G H)
        ( map-hom-Semigroup G H f)
        ( refl-htpy)
        ( preserves-mul-hom-Semigroup G H f)

  abstract
    is-equiv-htpy-eq-hom-Semigroup :
      (f g : hom-Semigroup G H) → is-equiv (htpy-eq-hom-Semigroup f g)
    is-equiv-htpy-eq-hom-Semigroup f =
      fundamental-theorem-id
        ( is-torsorial-htpy-hom-Semigroup f)
        ( htpy-eq-hom-Semigroup f)

  eq-htpy-hom-Semigroup :
    {f g : hom-Semigroup G H} → htpy-hom-Semigroup f g → f ＝ g
  eq-htpy-hom-Semigroup {f} {g} =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Semigroup f g)

  is-set-hom-Semigroup : is-set (hom-Semigroup G H)
  is-set-hom-Semigroup f g =
    is-prop-is-equiv
      ( is-equiv-htpy-eq-hom-Semigroup f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-Semigroup H
            ( map-hom-Semigroup G H f x)
            ( map-hom-Semigroup G H g x)))

  hom-set-Semigroup : Set (l1 ⊔ l2)
  pr1 hom-set-Semigroup = hom-Semigroup G H
  pr2 hom-set-Semigroup = is-set-hom-Semigroup

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  htpy-hom-Group : (f g : hom-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Group = htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  refl-htpy-hom-Group : (f : hom-Group G H) → htpy-hom-Group f f
  refl-htpy-hom-Group =
    refl-htpy-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  htpy-eq-hom-Group : (f g : hom-Group G H) → f ＝ g → htpy-hom-Group f g
  htpy-eq-hom-Group =
    htpy-eq-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  abstract
    is-torsorial-htpy-hom-Group :
      ( f : hom-Group G H) → is-torsorial (htpy-hom-Group f)
    is-torsorial-htpy-hom-Group =
      is-torsorial-htpy-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : hom-Group G H) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group =
      is-equiv-htpy-eq-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  extensionality-hom-Group :
    (f g : hom-Group G H) → (f ＝ g) ≃ htpy-hom-Group f g
  pr1 (extensionality-hom-Group f g) = htpy-eq-hom-Group f g
  pr2 (extensionality-hom-Group f g) = is-equiv-htpy-eq-hom-Group f g

  eq-htpy-hom-Group : {f g : hom-Group G H} → htpy-hom-Group f g → f ＝ g
  eq-htpy-hom-Group =
    eq-htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-set-hom-Group : is-set (hom-Group G H)
  is-set-hom-Group =
    is-set-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-set-Group : Set (l1 ⊔ l2)
  pr1 hom-set-Group = hom-Group G H
  pr2 hom-set-Group = is-set-hom-Group
```

## Remark 19.2.3

The **identity homomorphism** on a (semi)group `G` is defined to be the pair consisting of

```text
id : G → G
λ x. λ y. refl : Π(x,y : G) μ_G(x,y) = μ_G(x,y).
```

```agda
preserves-mul-id-Semigroup :
  {l : Level} (G : Semigroup l) → preserves-mul-Semigroup G G id
preserves-mul-id-Semigroup G = refl

id-hom-Semigroup :
  {l : Level} (G : Semigroup l) → hom-Semigroup G G
pr1 (id-hom-Semigroup G) = id
pr2 (id-hom-Semigroup G) = preserves-mul-id-Semigroup G

id-hom-Group : {l : Level} (G : Group l) → hom-Group G G
id-hom-Group G = id-hom-Semigroup (semigroup-Group G)
```

Let `f : G → H` and `g : H → K` be (semi)group homomorphisms.
Then the composite function `g ∘ f : G → K` is also a (semi)group homomorphism, since we have the identifications

```text
[g(f(μ_G(x,y)))]---->[g(μ_H(f(x),f(y)))]---->[μ_K(g(f(x)),g(f(y)))]
```

```agda
module _
  {l1 l2 l3 : Level}
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3)
  (g : hom-Semigroup H K) (f : hom-Semigroup G H)
  where

  map-comp-hom-Semigroup : type-Semigroup G → type-Semigroup K
  map-comp-hom-Semigroup =
    (map-hom-Semigroup H K g) ∘ (map-hom-Semigroup G H f)

  preserves-mul-comp-hom-Semigroup :
    preserves-mul-Semigroup G K map-comp-hom-Semigroup
  preserves-mul-comp-hom-Semigroup =
    ( ap
      ( map-hom-Semigroup H K g)
      ( preserves-mul-hom-Semigroup G H f)) ∙
    ( preserves-mul-hom-Semigroup H K g)

  comp-hom-Semigroup : hom-Semigroup G K
  pr1 comp-hom-Semigroup = map-comp-hom-Semigroup
  pr2 comp-hom-Semigroup = preserves-mul-comp-hom-Semigroup

module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  (g : hom-Group H K) (f : hom-Group G H)
  where

  comp-hom-Group : hom-Group G K
  comp-hom-Group =
    comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)

  map-comp-hom-Group : type-Group G → type-Group K
  map-comp-hom-Group =
    map-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)

  preserves-mul-comp-hom-Group :
    preserves-mul-Group G K map-comp-hom-Group
  preserves-mul-comp-hom-Group =
    preserves-mul-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)
```

Since the identity type of (semi)group homomorphisms is equivalent to the type of homotopies between (semi)group homomorphisms it is easy to see that (semi)group homomorphisms satisfy the laws of a category, i.e., that we have the identifications

```text
id ∘ f = f
g ∘ id = g
(h ∘ g) ∘ f = h ∘ (g ∘ f)
```

for any composable (semi)group homomorphisms `f`, `g`, and `h`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3) (L : Semigroup l4)
  (h : hom-Semigroup K L) (g : hom-Semigroup H K) (f : hom-Semigroup G H)
  where

  associative-comp-hom-Semigroup :
    comp-hom-Semigroup G H L (comp-hom-Semigroup H K L h g) f ＝
    comp-hom-Semigroup G K L h (comp-hom-Semigroup G H K g f)
  associative-comp-hom-Semigroup = eq-htpy-hom-Semigroup G L refl-htpy

left-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : hom-Semigroup G H) →
  comp-hom-Semigroup G H H (id-hom-Semigroup H) f ＝ f
left-unit-law-comp-hom-Semigroup G
  (pair (pair H is-set-H) (pair μ-H associative-H)) (pair f μ-f) =
  eq-htpy-hom-Semigroup G
    ( pair (pair H is-set-H) (pair μ-H associative-H))
    ( refl-htpy)

right-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : hom-Semigroup G H) →
  comp-hom-Semigroup G G H f (id-hom-Semigroup G) ＝ f
right-unit-law-comp-hom-Semigroup
  (pair (pair G is-set-G) (pair μ-G associative-G)) H (pair f μ-f) =
  eq-htpy-hom-Semigroup
    ( pair (pair G is-set-G) (pair μ-G associative-G)) H refl-htpy

module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  where

  associative-comp-hom-Group :
    (h : hom-Group K L) (g : hom-Group H K) (f : hom-Group G H) →
    comp-hom-Group G H L (comp-hom-Group H K L h g) f ＝
    comp-hom-Group G K L h (comp-hom-Group G H K g f)
  associative-comp-hom-Group =
    associative-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( semigroup-Group L)

left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  comp-hom-Group G H H (id-hom-Group H) f ＝ f
left-unit-law-comp-hom-Group G H =
  left-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  comp-hom-Group G G H f (id-hom-Group G) ＝ f
right-unit-law-comp-hom-Group G H =
  right-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
```

## Definition 19.2.4

Let `h : hom(G,H)` be a homomorphism of (semi)groups.
Then `h` is said to be an **isomorphism** if it comes equipped with an element of type `is-iso(h)`, consisting of triples `(h⁻¹,p,q)` consisting of a homomorphism `h⁻¹ : hom(H,G)` of semigroups and identifications

```text
p : h⁻¹ ∘ h = id[G] and q : h ∘ h⁻¹ = id[H]
```

witnessing that `h⁻¹` satisfies the inverse laws.

```agda
module _
  {l : Level} {A : UU l}
  where

  involutive-Id : (x y : A) → UU l
  involutive-Id x y = Σ A (λ z → (z ＝ y) × (z ＝ x))

  infix 6 _＝ⁱ_
  _＝ⁱ_ : A → A → UU l
  (a ＝ⁱ b) = involutive-Id a b

  reflⁱ : {x : A} → x ＝ⁱ x
  reflⁱ {x} = (x , refl , refl)

module _
  {l : Level} {A : UU l} {x y : A}
  where

  involutive-eq-eq : x ＝ y → x ＝ⁱ y
  involutive-eq-eq p = (x , p , refl)

  eq-involutive-eq : x ＝ⁱ y → x ＝ y
  eq-involutive-eq (z , p , q) = inv q ∙ p

  is-section-eq-involutive-eq : is-section involutive-eq-eq eq-involutive-eq
  is-section-eq-involutive-eq (z , p , refl) = refl

  is-retraction-eq-involutive-eq :
    is-retraction involutive-eq-eq eq-involutive-eq
  is-retraction-eq-involutive-eq p = refl

  is-equiv-involutive-eq-eq : is-equiv involutive-eq-eq
  pr1 (pr1 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr1 is-equiv-involutive-eq-eq) = is-section-eq-involutive-eq
  pr1 (pr2 is-equiv-involutive-eq-eq) = eq-involutive-eq
  pr2 (pr2 is-equiv-involutive-eq-eq) = is-retraction-eq-involutive-eq

  is-equiv-eq-involutive-eq : is-equiv eq-involutive-eq
  pr1 (pr1 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr1 is-equiv-eq-involutive-eq) = is-retraction-eq-involutive-eq
  pr1 (pr2 is-equiv-eq-involutive-eq) = involutive-eq-eq
  pr2 (pr2 is-equiv-eq-involutive-eq) = is-section-eq-involutive-eq

  equiv-involutive-eq-eq : (x ＝ y) ≃ (x ＝ⁱ y)
  pr1 equiv-involutive-eq-eq = involutive-eq-eq
  pr2 equiv-involutive-eq-eq = is-equiv-involutive-eq-eq

  equiv-eq-involutive-eq : (x ＝ⁱ y) ≃ (x ＝ y)
  pr1 equiv-eq-involutive-eq = eq-involutive-eq
  pr2 equiv-eq-involutive-eq = is-equiv-eq-involutive-eq

record
  Large-Precategory (α : Level → Level) (β : Level → Level → Level) : UUω where

  field
    obj-Large-Precategory :
      (l : Level) → UU (α l)

    hom-set-Large-Precategory :
      {l1 l2 : Level} →
      obj-Large-Precategory l1 →
      obj-Large-Precategory l2 →
      Set (β l1 l2)

  hom-Large-Precategory :
    {l1 l2 : Level} →
    obj-Large-Precategory l1 →
    obj-Large-Precategory l2 →
    UU (β l1 l2)
  hom-Large-Precategory X Y = type-Set (hom-set-Large-Precategory X Y)

  is-set-hom-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory l1)
    (Y : obj-Large-Precategory l2) →
    is-set (hom-Large-Precategory X Y)
  is-set-hom-Large-Precategory X Y =
    is-set-type-Set (hom-set-Large-Precategory X Y)

  field
    comp-hom-Large-Precategory :
      {l1 l2 l3 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3} →
      hom-Large-Precategory Y Z →
      hom-Large-Precategory X Y →
      hom-Large-Precategory X Z

    id-hom-Large-Precategory :
      {l1 : Level}
      {X : obj-Large-Precategory l1} →
      hom-Large-Precategory X X

    involutive-eq-associative-comp-hom-Large-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3}
      {W : obj-Large-Precategory l4} →
      (h : hom-Large-Precategory Z W)
      (g : hom-Large-Precategory Y Z)
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory (comp-hom-Large-Precategory h g) f) ＝ⁱ
      ( comp-hom-Large-Precategory h (comp-hom-Large-Precategory g f))

    left-unit-law-comp-hom-Large-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory id-hom-Large-Precategory f) ＝ f

    right-unit-law-comp-hom-Large-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory f id-hom-Large-Precategory) ＝ f

  associative-comp-hom-Large-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3}
      {W : obj-Large-Precategory l4} →
      (h : hom-Large-Precategory Z W)
      (g : hom-Large-Precategory Y Z)
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory (comp-hom-Large-Precategory h g) f) ＝
      ( comp-hom-Large-Precategory h (comp-hom-Large-Precategory g f))
  associative-comp-hom-Large-Precategory h g f =
    eq-involutive-eq
      ( involutive-eq-associative-comp-hom-Large-Precategory h g f)

open Large-Precategory public

make-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  ( obj : (l : Level) → UU (α l))
  ( hom-set : {l1 l2 : Level} → obj l1 → obj l2 → Set (β l1 l2))
  ( _∘_ :
    {l1 l2 l3 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} →
    type-Set (hom-set Y Z) → type-Set (hom-set X Y) → type-Set (hom-set X Z))
  ( id : {l : Level} {X : obj l} → type-Set (hom-set X X))
  ( assoc-comp-hom :
    {l1 l2 l3 l4 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} {W : obj l4}
    (h : type-Set (hom-set Z W))
    (g : type-Set (hom-set Y Z))
    (f : type-Set (hom-set X Y)) →
    ( (h ∘ g) ∘ f) ＝ ( h ∘ (g ∘ f)))
  ( left-unit-comp-hom :
    {l1 l2 : Level} {X : obj l1} {Y : obj l2} (f : type-Set (hom-set X Y)) →
    id ∘ f ＝ f)
  ( right-unit-comp-hom :
    {l1 l2 : Level} {X : obj l1} {Y : obj l2} (f : type-Set (hom-set X Y)) →
    f ∘ id ＝ f) →
  Large-Precategory α β
make-Large-Precategory
  obj hom-set _∘_ id assoc-comp-hom left-unit-comp-hom right-unit-comp-hom =
  λ where
    .obj-Large-Precategory → obj
    .hom-set-Large-Precategory → hom-set
    .comp-hom-Large-Precategory → _∘_
    .id-hom-Large-Precategory → id
    .involutive-eq-associative-comp-hom-Large-Precategory h g f →
      involutive-eq-eq (assoc-comp-hom h g f)
    .left-unit-law-comp-hom-Large-Precategory → left-unit-comp-hom
    .right-unit-law-comp-hom-Large-Precategory → right-unit-comp-hom

{-# INLINE make-Large-Precategory #-}

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  ap-comp-hom-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3}
    {g g' : hom-Large-Precategory C Y Z} (p : g ＝ g')
    {f f' : hom-Large-Precategory C X Y} (q : f ＝ f') →
    comp-hom-Large-Precategory C g f ＝
    comp-hom-Large-Precategory C g' f'
  ap-comp-hom-Large-Precategory = ap-binary (comp-hom-Large-Precategory C)

  comp-hom-Large-Precategory' :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3} →
    hom-Large-Precategory C X Y →
    hom-Large-Precategory C Y Z →
    hom-Large-Precategory C X Z
  comp-hom-Large-Precategory' f g = comp-hom-Large-Precategory C g f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : hom-Large-Precategory C X Y)
  where

  is-iso-Large-Precategory : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-Large-Precategory =
    Σ ( hom-Large-Precategory C Y X)
      ( λ g →
        ( comp-hom-Large-Precategory C f g ＝ id-hom-Large-Precategory C) ×
        ( comp-hom-Large-Precategory C g f ＝ id-hom-Large-Precategory C))

  hom-inv-is-iso-Large-Precategory :
    is-iso-Large-Precategory → hom-Large-Precategory C Y X
  hom-inv-is-iso-Large-Precategory = pr1

  is-section-hom-inv-is-iso-Large-Precategory :
    (H : is-iso-Large-Precategory) →
    comp-hom-Large-Precategory C f (hom-inv-is-iso-Large-Precategory H) ＝
    id-hom-Large-Precategory C
  is-section-hom-inv-is-iso-Large-Precategory = pr1 ∘ pr2

  is-retraction-hom-inv-is-iso-Large-Precategory :
    (H : is-iso-Large-Precategory) →
    comp-hom-Large-Precategory C (hom-inv-is-iso-Large-Precategory H) f ＝
    id-hom-Large-Precategory C
  is-retraction-hom-inv-is-iso-Large-Precategory = pr2 ∘ pr2

Semigroup-Large-Precategory : Large-Precategory lsuc (_⊔_)
Semigroup-Large-Precategory =
  make-Large-Precategory
    ( Semigroup)
    ( hom-set-Semigroup)
    ( λ {l1} {l2} {l3} {G} {H} {K} → comp-hom-Semigroup G H K)
    ( λ {l} {G} → id-hom-Semigroup G)
    ( λ {l1} {l2} {l3} {l4} {G} {H} {K} {L} →
      associative-comp-hom-Semigroup G H K L)
    ( λ {l1} {l2} {G} {H} → left-unit-law-comp-hom-Semigroup G H)
    ( λ {l1} {l2} {G} {H} → right-unit-law-comp-hom-Semigroup G H)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : hom-Semigroup G H)
  where

  is-iso-Semigroup : UU (l1 ⊔ l2)
  is-iso-Semigroup =
    is-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  hom-inv-is-iso-Semigroup :
    is-iso-Semigroup → hom-Semigroup H G
  hom-inv-is-iso-Semigroup =
    hom-inv-is-iso-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  map-inv-is-iso-Semigroup :
    is-iso-Semigroup → type-Semigroup H → type-Semigroup G
  map-inv-is-iso-Semigroup U =
    map-hom-Semigroup H G (hom-inv-is-iso-Semigroup U)

  is-section-hom-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    comp-hom-Semigroup H G H f (hom-inv-is-iso-Semigroup U) ＝
    id-hom-Semigroup H
  is-section-hom-inv-is-iso-Semigroup =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-section-map-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    ( map-hom-Semigroup G H f ∘ map-inv-is-iso-Semigroup U) ~ id
  is-section-map-inv-is-iso-Semigroup U =
    htpy-eq-hom-Semigroup H H
      ( comp-hom-Semigroup H G H f (hom-inv-is-iso-Semigroup U))
      ( id-hom-Semigroup H)
      ( is-section-hom-inv-is-iso-Semigroup U)

  is-retraction-hom-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    comp-hom-Semigroup G H G (hom-inv-is-iso-Semigroup U) f ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-is-iso-Semigroup =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-retraction-map-inv-is-iso-Semigroup :
    (U : is-iso-Semigroup) →
    ( map-inv-is-iso-Semigroup U ∘ map-hom-Semigroup G H f) ~ id
  is-retraction-map-inv-is-iso-Semigroup U =
    htpy-eq-hom-Semigroup G G
      ( comp-hom-Semigroup G H G (hom-inv-is-iso-Semigroup U) f)
      ( id-hom-Semigroup G)
      ( is-retraction-hom-inv-is-iso-Semigroup U)

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-iso-Group : UU (l1 ⊔ l2)
  is-iso-Group =
    is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  hom-inv-is-iso-Group :
    is-iso-Group → hom-Group H G
  hom-inv-is-iso-Group =
    hom-inv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  map-inv-is-iso-Group :
    is-iso-Group → type-Group H → type-Group G
  map-inv-is-iso-Group =
    map-inv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  is-section-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group H G H f (hom-inv-is-iso-Group U) ＝
    id-hom-Group H
  is-section-hom-inv-is-iso-Group =
    is-section-hom-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-section-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-hom-Group G H f ∘ map-inv-is-iso-Group U) ~ id
  is-section-map-inv-is-iso-Group =
    is-section-map-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-retraction-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group G H G (hom-inv-is-iso-Group U) f ＝
    id-hom-Group G
  is-retraction-hom-inv-is-iso-Group =
    is-retraction-hom-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-retraction-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-inv-is-iso-Group U ∘ map-hom-Group G H f) ~ id
  is-retraction-map-inv-is-iso-Group =
    is-retraction-map-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
```

We write `G ≅ H` for the type of all isomorphisms of semigroups from `G` to `H`, i.e.,

```text
G ≅ H ≔ Σ(h : hom(G,H)) Σ(k : hom(H,G)) (k ∘ h = id[G]) × (h ∘ k = id[H]).
```

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  where

  iso-Large-Precategory : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Large-Precategory =
    Σ (hom-Large-Precategory C X Y) (is-iso-Large-Precategory C)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  where

  hom-iso-Large-Precategory : hom-Large-Precategory C X Y
  hom-iso-Large-Precategory = pr1 f

  is-iso-iso-Large-Precategory :
    is-iso-Large-Precategory C hom-iso-Large-Precategory
  is-iso-iso-Large-Precategory = pr2 f

  hom-inv-iso-Large-Precategory : hom-Large-Precategory C Y X
  hom-inv-iso-Large-Precategory = pr1 (pr2 f)

  is-section-hom-inv-iso-Large-Precategory :
    ( comp-hom-Large-Precategory C
      ( hom-iso-Large-Precategory)
      ( hom-inv-iso-Large-Precategory)) ＝
    ( id-hom-Large-Precategory C)
  is-section-hom-inv-iso-Large-Precategory = pr1 (pr2 (pr2 f))

  is-retraction-hom-inv-iso-Large-Precategory :
    ( comp-hom-Large-Precategory C
      ( hom-inv-iso-Large-Precategory)
      ( hom-iso-Large-Precategory)) ＝
    ( id-hom-Large-Precategory C)
  is-retraction-hom-inv-iso-Large-Precategory = pr2 (pr2 (pr2 f))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  where

  is-iso-inv-is-iso-Large-Precategory :
    (p : is-iso-Large-Precategory C f) →
    is-iso-Large-Precategory C (hom-inv-iso-Large-Precategory C (f , p))
  pr1 (is-iso-inv-is-iso-Large-Precategory p) = f
  pr1 (pr2 (is-iso-inv-is-iso-Large-Precategory p)) =
    is-retraction-hom-inv-is-iso-Large-Precategory C f p
  pr2 (pr2 (is-iso-inv-is-iso-Large-Precategory p)) =
    is-section-hom-inv-is-iso-Large-Precategory C f p

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  inv-iso-Large-Precategory :
    iso-Large-Precategory C X Y → iso-Large-Precategory C Y X
  pr1 (inv-iso-Large-Precategory f) = hom-inv-iso-Large-Precategory C f
  pr2 (inv-iso-Large-Precategory f) =
    is-iso-inv-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  iso-Semigroup : UU (l1 ⊔ l2)
  iso-Semigroup = iso-Large-Precategory Semigroup-Large-Precategory G H

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) (f : iso-Semigroup G H)
  where

  hom-iso-Semigroup : hom-Semigroup G H
  hom-iso-Semigroup =
    hom-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  map-iso-Semigroup : type-Semigroup G → type-Semigroup H
  map-iso-Semigroup = map-hom-Semigroup G H hom-iso-Semigroup

  preserves-mul-iso-Semigroup :
    {x y : type-Semigroup G} →
    map-iso-Semigroup (mul-Semigroup G x y) ＝
    mul-Semigroup H (map-iso-Semigroup x) (map-iso-Semigroup y)
  preserves-mul-iso-Semigroup =
    preserves-mul-hom-Semigroup G H hom-iso-Semigroup

  is-iso-iso-Semigroup : is-iso-Semigroup G H hom-iso-Semigroup
  is-iso-iso-Semigroup =
    is-iso-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  inv-iso-Semigroup : iso-Semigroup H G
  inv-iso-Semigroup =
    inv-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  hom-inv-iso-Semigroup : hom-Semigroup H G
  hom-inv-iso-Semigroup =
    hom-inv-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  map-inv-iso-Semigroup : type-Semigroup H → type-Semigroup G
  map-inv-iso-Semigroup =
    map-hom-Semigroup H G hom-inv-iso-Semigroup

  preserves-mul-inv-iso-Semigroup :
    {x y : type-Semigroup H} →
    map-inv-iso-Semigroup (mul-Semigroup H x y) ＝
    mul-Semigroup G (map-inv-iso-Semigroup x) (map-inv-iso-Semigroup y)
  preserves-mul-inv-iso-Semigroup =
    preserves-mul-hom-Semigroup H G hom-inv-iso-Semigroup

  is-section-hom-inv-iso-Semigroup :
    comp-hom-Semigroup H G H hom-iso-Semigroup hom-inv-iso-Semigroup ＝
    id-hom-Semigroup H
  is-section-hom-inv-iso-Semigroup =
    is-section-hom-inv-iso-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-section-map-inv-iso-Semigroup :
    map-iso-Semigroup ∘ map-inv-iso-Semigroup ~ id
  is-section-map-inv-iso-Semigroup =
    htpy-eq-hom-Semigroup H H
      ( comp-hom-Semigroup H G H
        ( hom-iso-Semigroup)
        ( hom-inv-iso-Semigroup))
      ( id-hom-Semigroup H)
      ( is-section-hom-inv-iso-Semigroup)

  is-retraction-hom-inv-iso-Semigroup :
    comp-hom-Semigroup G H G hom-inv-iso-Semigroup hom-iso-Semigroup ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-iso-Semigroup =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-retraction-map-inv-iso-Semigroup :
    map-inv-iso-Semigroup ∘ map-iso-Semigroup ~ id
  is-retraction-map-inv-iso-Semigroup =
    htpy-eq-hom-Semigroup G G
      ( comp-hom-Semigroup G H G
        ( hom-inv-iso-Semigroup)
        ( hom-iso-Semigroup))
      ( id-hom-Semigroup G)
      ( is-retraction-hom-inv-iso-Semigroup)

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  iso-Group : UU (l1 ⊔ l2)
  iso-Group = iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-iso-Group : iso-Group → hom-Group G H
  hom-iso-Group = hom-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  map-iso-Group : iso-Group → type-Group G → type-Group H
  map-iso-Group = map-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-iso-Group :
    (f : iso-Group) {x y : type-Group G} →
    map-iso-Group f (mul-Group G x y) ＝
    mul-Group H (map-iso-Group f x) (map-iso-Group f y)
  preserves-mul-iso-Group =
    preserves-mul-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-iso-iso-Group :
    (f : iso-Group) → is-iso-Group G H (hom-iso-Group f)
  is-iso-iso-Group =
    is-iso-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-inv-iso-Group : iso-Group → hom-Group H G
  hom-inv-iso-Group =
    hom-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  map-inv-iso-Group : iso-Group → type-Group H → type-Group G
  map-inv-iso-Group =
    map-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-inv-iso-Group :
    (f : iso-Group) {x y : type-Group H} →
    map-inv-iso-Group f (mul-Group H x y) ＝
    mul-Group G (map-inv-iso-Group f x) (map-inv-iso-Group f y)
  preserves-mul-inv-iso-Group =
    preserves-mul-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-section-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group H G H (hom-iso-Group f) (hom-inv-iso-Group f) ＝
    id-hom-Group H
  is-section-hom-inv-iso-Group =
    is-section-hom-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-section-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-iso-Group f ∘ map-inv-iso-Group f) ~ id
  is-section-map-inv-iso-Group =
    is-section-map-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-retraction-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group G H G (hom-inv-iso-Group f) (hom-iso-Group f) ＝
    id-hom-Group G
  is-retraction-hom-inv-iso-Group =
    is-retraction-hom-inv-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  is-retraction-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-inv-iso-Group f ∘ map-iso-Group f) ~ id
  is-retraction-map-inv-iso-Group =
    is-retraction-map-inv-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
```

If `f` is an isomorphism, then its inverse is unique.
In other words, being an isomorphism is a property.

## Lemma 19.2.5

For any semigroup homomorphism `h : hom(G,H)`, the type

```text
is-iso(h)
```

is a proposition.
It follows that the type `G ≅ H` is a set for any two semigroups `G` and `H`.

### Proof

_Proof._ Let `k` and `k'` be two inverses of `h`.
In Remark 19.2.2 we have observed that the type of semigroup homomorphisms between any two semigroups is a set.
Therefore it follows that the types `h ∘ k = id` and `k ∘ h = id` are propositions, so it suffices to check that `k = k'`.
In Remark 19.2.2 we also observed that the equality type `k = k'` is equivalent to the type of homotopies `k ~ k'` between their underlying functions.
We construct a homotopy `k ~ k'` by the usual argument:

```text
[k(y)]---->[k(h(k'(y)))]---->[k'(y)]
```

 ◻

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  all-elements-equal-is-iso-Large-Precategory :
    (f : hom-Large-Precategory C X Y)
    (H K : is-iso-Large-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-Large-Precategory f (g , p , q) (g' , p' , q') =
    eq-type-subtype
      ( λ g →
        product-Prop
          ( Id-Prop
            ( hom-set-Large-Precategory C Y Y)
            ( comp-hom-Large-Precategory C f g)
            ( id-hom-Large-Precategory C))
          ( Id-Prop
            ( hom-set-Large-Precategory C X X)
            ( comp-hom-Large-Precategory C g f)
            ( id-hom-Large-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precategory C g)) ∙
        ( ap ( comp-hom-Large-Precategory C g) (inv p')) ∙
        ( inv (associative-comp-hom-Large-Precategory C g f g')) ∙
        ( ap ( comp-hom-Large-Precategory' C g') q) ∙
        ( left-unit-law-comp-hom-Large-Precategory C g'))

  is-prop-is-iso-Large-Precategory :
    (f : hom-Large-Precategory C X Y) →
    is-prop (is-iso-Large-Precategory C f)
  is-prop-is-iso-Large-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-Large-Precategory f)

  is-iso-prop-Large-Precategory :
    (f : hom-Large-Precategory C X Y) → Prop (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 (is-iso-prop-Large-Precategory f) =
    is-iso-Large-Precategory C f
  pr2 (is-iso-prop-Large-Precategory f) =
    is-prop-is-iso-Large-Precategory f

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  eq-iso-eq-hom-Large-Precategory :
    (f g : iso-Large-Precategory C X Y) →
    hom-iso-Large-Precategory C f ＝ hom-iso-Large-Precategory C g → f ＝ g
  eq-iso-eq-hom-Large-Precategory f g =
    eq-type-subtype (is-iso-prop-Large-Precategory C)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-prop-is-iso-Semigroup :
      (f : hom-Semigroup G H) → is-prop (is-iso-Semigroup G H f)
    is-prop-is-iso-Semigroup =
      is-prop-is-iso-Large-Precategory
        ( Semigroup-Large-Precategory)
        { X = G}
        { Y = H}

  is-iso-prop-Semigroup :
    hom-Semigroup G H → Prop (l1 ⊔ l2)
  is-iso-prop-Semigroup =
    is-iso-prop-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-prop-is-iso-Group : is-prop (is-iso-Group G H f)
  is-prop-is-iso-Group =
    is-prop-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  is-iso-prop-Group : Prop (l1 ⊔ l2)
  is-iso-prop-Group =
    is-iso-prop-Semigroup (semigroup-Group G) (semigroup-Group H) f
```
