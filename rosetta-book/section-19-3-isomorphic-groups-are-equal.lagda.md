# Section 19.3 Isomorphic groups are equal

```agda
module section-19-3-isomorphic-groups-are-equal where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import exercise-9-3-homotopic-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-11-6-the-structure-identity-principle
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-4-maps-and-families-of-types
open import section-19-1-the-type-of-all-groups
open import section-19-2-group-homomorphisms
```

## Lemma 19.3.1

A (semi)group homomorphism `h : hom(G,H)` is an isomorphism if and only if its underlying map is an equivalence.
Consequently, there is an equivalence

```text
(G ≅ H) ≃ Σ(e : G ≃ H) Π(x,y : G) e(μ_G(x,y)) = μ_H(e(x),e(y))
```

### Proof

_Proof._ If `h : hom(G,H)` is an isomorphism, then the inverse semigroup homomorphism also provides an inverse of the underlying map of `h`.
Thus we obtain that `h` is an equivalence.
For the converse, suppose that the underlying map of `f : G → H` is an equivalence.
Then its inverse is also a semigroup homomorphism, since we have

```text
f⁻¹(μ_H(x,y)) = f⁻¹(μ_H(f(f⁻¹(x)),f(f⁻¹(y))))
= f⁻¹(f(μ_G(f⁻¹(x),f⁻¹(y))))
= μ_G(f⁻¹(x),f⁻¹(y)).
```

 ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv μA μB e = preserves-mul μA μB (map-equiv e)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup e =
    preserves-mul-equiv (mul-Semigroup G) (mul-Semigroup H) e

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup =
    Σ (type-Semigroup G ≃ type-Semigroup H) preserves-mul-equiv-Semigroup

  is-equiv-hom-Semigroup : hom-Semigroup G H → UU (l1 ⊔ l2)
  is-equiv-hom-Semigroup f = is-equiv (map-hom-Semigroup G H f)

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : hom-Semigroup G H)
      ( U : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv U)
    preserves-mul-map-inv-is-equiv-Semigroup (f , μ-f) U {x} {y} =
      map-inv-is-equiv
        ( is-emb-is-equiv U
          ( map-inv-is-equiv U (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv U x)
            ( map-inv-is-equiv U y)))
        ( ( is-section-map-inv-is-equiv U (mul-Semigroup H x y)) ∙
          ( ap
            ( λ t → mul-Semigroup H t y)
            ( inv (is-section-map-inv-is-equiv U x))) ∙
          ( ap
            ( mul-Semigroup H (f (map-inv-is-equiv U x)))
            ( inv (is-section-map-inv-is-equiv U y))) ∙
          ( inv μ-f))

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-iso-is-equiv-hom-Semigroup :
      (f : hom-Semigroup G H) →
      is-equiv-hom-Semigroup G H f → is-iso-Semigroup G H f
    pr1 (pr1 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      map-inv-is-equiv U
    pr2 (pr1 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      preserves-mul-map-inv-is-equiv-Semigroup G H (f , μ-f) U
    pr1 (pr2 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      eq-htpy-hom-Semigroup H H (is-section-map-inv-is-equiv U)
    pr2 (pr2 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      eq-htpy-hom-Semigroup G G (is-retraction-map-inv-is-equiv U)

  abstract
    is-equiv-is-iso-Semigroup :
      (f : hom-Semigroup G H) →
      is-iso-Semigroup G H f → is-equiv-hom-Semigroup G H f
    is-equiv-is-iso-Semigroup (f , μ-f) ((g , μ-g) , S , R) =
      is-equiv-is-invertible g
        ( htpy-eq (ap pr1 S))
        ( htpy-eq (ap pr1 R))

  equiv-iso-equiv-Semigroup : equiv-Semigroup G H ≃ iso-Semigroup G H
  equiv-iso-equiv-Semigroup =
    ( equiv-type-subtype
      ( λ f → is-property-is-equiv (map-hom-Semigroup G H f))
      ( is-prop-is-iso-Semigroup G H)
      ( is-iso-is-equiv-hom-Semigroup)
      ( is-equiv-is-iso-Semigroup)) ∘e
    ( equiv-right-swap-Σ)

  iso-equiv-Semigroup : equiv-Semigroup G H → iso-Semigroup G H
  iso-equiv-Semigroup = map-equiv equiv-iso-equiv-Semigroup

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-equiv-hom-Group : hom-Group G H → UU (l1 ⊔ l2)
  is-equiv-hom-Group =
    is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-iso-is-equiv-hom-Group :
    (f : hom-Group G H) → is-equiv-hom-Group f → is-iso-Group G H f
  is-iso-is-equiv-hom-Group =
    is-iso-is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-equiv-is-iso-Group :
    (f : hom-Group G H) → is-iso-Group G H f → is-equiv-hom-Group f
  is-equiv-is-iso-Group =
    is-equiv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group ≃ iso-Group G H
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group → iso-Group G H
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group
```

## Definition 19.3.2

Let `G` and `H` be semigroups in a univalent universe `𝒰`.
We define the family of maps

```text
iso-eq : (G = H) → (G ≅ H)
```

indexed by `H : Semigroup_𝒰` by `iso-eq(refl) ≔ id[G]`.

## Theorem 19.3.3

Consider a semigroup `G` in a univalent universe `𝒰`.
Then the family of maps

```text
iso-eq : (G = H) → (G ≅ H)
```

indexed by `H : Semigroup_𝒰` is a family of equivalences.

### Proof

_Proof._ By the fundamental theorem of identity types Theorem 11.2.2 it suffices to show that the total space

```text
Σ(H : Semigroup_𝒰) G ≅ H
```

is contractible.
Since the type of isomorphisms from `G` to `H` is equivalent to the type of multiplication-preserving equivalences from `G` to `H` it suffices to show that the type

```text
Σ(H : Semigroup_𝒰) Σ(e : G ≃ H) Π(x,y : G) e(μ_G(x,y)) = μ_{H}(e(x),e(y))
```

is contractible.
Since `Semigroup_𝒰 ≐ Σ(H : Set_𝒰) has-associative-mul(H)` we are in position to apply the structure identity principle stated in Theorem 11.6.2.
Note that `H ↦ G ≃ H` is an identity system on `Set_𝒰` at the set `G`.
By condition (v) of Theorem 11.6.2 it therefore suffices to show that the type

```text
Σ(μ' : has-associative-mul(G)) Π(x,y : G) μ_G(x,y) = μ'(x,y)
```

is contractible.
This follows by function extensionality, since associativity of a binary operation on a set is a proposition. ◻

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  {l1 : Level}
  where

  hom-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → hom-Large-Precategory C X Y
  hom-eq-Large-Precategory X .X refl = id-hom-Large-Precategory C

  hom-inv-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → hom-Large-Precategory C Y X
  hom-inv-eq-Large-Precategory X Y = hom-eq-Large-Precategory Y X ∘ inv

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level} {X : obj-Large-Precategory C l1}
  where

  is-iso-id-hom-Large-Precategory :
    is-iso-Large-Precategory C (id-hom-Large-Precategory C {X = X})
  pr1 is-iso-id-hom-Large-Precategory = id-hom-Large-Precategory C
  pr1 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)
  pr2 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)

  id-iso-Large-Precategory : iso-Large-Precategory C X X
  pr1 id-iso-Large-Precategory = id-hom-Large-Precategory C
  pr2 id-iso-Large-Precategory = is-iso-id-hom-Large-Precategory

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level}
  where

  iso-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → iso-Large-Precategory C X Y
  pr1 (iso-eq-Large-Precategory X Y p) = hom-eq-Large-Precategory C X Y p
  pr2 (iso-eq-Large-Precategory X .X refl) = is-iso-id-hom-Large-Precategory C

module _
  {l : Level} (G : Semigroup l)
  where

  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = mul-Semigroup G
  pr2 (pr1 (center-total-preserves-mul-id-Semigroup)) =
    associative-mul-Semigroup G
  pr2 (center-total-preserves-mul-id-Semigroup) = refl

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    center-total-preserves-mul-id-Semigroup ＝ t
  contraction-total-preserves-mul-id-Semigroup
    ( (μ-G' , associative-G') , μ-id) =
    eq-type-subtype
      ( λ μ →
        preserves-mul-prop-Semigroup G (pair (set-Semigroup G) μ) id)
      ( eq-type-subtype
        ( λ μ →
          Π-Prop
            ( type-Semigroup G)
            ( λ x →
              Π-Prop
                ( type-Semigroup G)
                ( λ y →
                  Π-Prop
                    ( type-Semigroup G)
                    ( λ z →
                      Id-Prop
                        ( set-Semigroup G)
                        ( μ (μ x y) z) (μ x (μ y z))))))
        ( eq-htpy (λ x → eq-htpy (λ y → μ-id))))

  is-torsorial-preserves-mul-id-Semigroup :
    is-torsorial
      ( λ (μ : has-associative-mul (type-Semigroup G)) →
        preserves-mul (mul-Semigroup G) (pr1 μ) id)
  pr1 is-torsorial-preserves-mul-id-Semigroup =
    center-total-preserves-mul-id-Semigroup
  pr2 is-torsorial-preserves-mul-id-Semigroup =
    contraction-total-preserves-mul-id-Semigroup

  is-torsorial-equiv-Semigroup :
    is-torsorial (equiv-Semigroup G)
  is-torsorial-equiv-Semigroup =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv (type-Semigroup G))
        ( is-prop-is-set)
        ( type-Semigroup G)
        ( id-equiv)
        ( is-set-type-Semigroup G))
      ( pair (set-Semigroup G) id-equiv)
      ( is-torsorial-preserves-mul-id-Semigroup)

module _
  {l : Level} (G : Semigroup l)
  where

  is-torsorial-iso-Semigroup :
    is-torsorial (iso-Semigroup G)
  is-torsorial-iso-Semigroup =
    is-contr-equiv'
      ( Σ (Semigroup l) (equiv-Semigroup G))
      ( equiv-tot (equiv-iso-equiv-Semigroup G))
      ( is-torsorial-equiv-Semigroup G)

  id-iso-Semigroup : iso-Semigroup G G
  id-iso-Semigroup =
    id-iso-Large-Precategory Semigroup-Large-Precategory {X = G}

  iso-eq-Semigroup : (H : Semigroup l) → G ＝ H → iso-Semigroup G H
  iso-eq-Semigroup = iso-eq-Large-Precategory Semigroup-Large-Precategory G
```

## Corollary 19.3.4

The type `Semigroup_𝒰` is a `1`-type.

### Proof

_Proof._ The identity types of `Semigroup_𝒰` are sets because they are equivalent to the sets of isomorphisms between semigroups. ◻

```agda
is-large-category-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) → UUω
is-large-category-Large-Precategory C =
  {l : Level} (X Y : obj-Large-Precategory C l) →
  is-equiv (iso-eq-Large-Precategory C X Y)

record
  Large-Category (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Category

  field
    large-precategory-Large-Category :
      Large-Precategory α β

    is-large-category-Large-Category :
      is-large-category-Large-Precategory large-precategory-Large-Category

open Large-Category public

is-large-category-Semigroup :
  is-large-category-Large-Precategory Semigroup-Large-Precategory
is-large-category-Semigroup G =
  fundamental-theorem-id (is-torsorial-iso-Semigroup G) (iso-eq-Semigroup G)

extensionality-Semigroup :
  {l : Level} (G H : Semigroup l) → (G ＝ H) ≃ iso-Semigroup G H
pr1 (extensionality-Semigroup G H) = iso-eq-Semigroup G H
pr2 (extensionality-Semigroup G H) = is-large-category-Semigroup G H

eq-iso-Semigroup :
  {l : Level} (G H : Semigroup l) → iso-Semigroup G H → G ＝ H
eq-iso-Semigroup G H = map-inv-is-equiv (is-large-category-Semigroup G H)

Semigroup-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Semigroup-Large-Category =
  Semigroup-Large-Precategory
is-large-category-Large-Category Semigroup-Large-Category =
  is-large-category-Semigroup

module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  composition-operation-binary-family-Set =
    {x y z : A} →
    type-Set (hom-set y z) → type-Set (hom-set x y) → type-Set (hom-set x z)

module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  where

  is-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-associative-composition-operation-binary-family-Set comp-hom =
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom (comp-hom h g) f ＝ⁱ comp-hom h (comp-hom g f))

  associative-composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  associative-composition-operation-binary-family-Set =
    Σ ( composition-operation-binary-family-Set hom-set)
      ( is-associative-composition-operation-binary-family-Set)

  is-unital-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set → UU (l1 ⊔ l2)
  is-unital-composition-operation-binary-family-Set comp-hom =
    Σ ( (x : A) → type-Set (hom-set x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom (e y) f ＝ f) ×
        ( {x y : A} (f : type-Set (hom-set x y)) → comp-hom f (e x) ＝ f))

module _
  {l1 l2 : Level} {A : UU l1} (hom-set : A → A → Set l2)
  (H : associative-composition-operation-binary-family-Set hom-set)
  where

  comp-hom-associative-composition-operation-binary-family-Set :
    composition-operation-binary-family-Set hom-set
  comp-hom-associative-composition-operation-binary-family-Set = pr1 H

  involutive-eq-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g)
      ( f)) ＝ⁱ
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h)
      ( comp-hom-associative-composition-operation-binary-family-Set g f))
  involutive-eq-associative-composition-operation-binary-family-Set = pr2 H

  witness-associative-composition-operation-binary-family-Set :
    {x y z w : A}
    (h : type-Set (hom-set z w))
    (g : type-Set (hom-set y z))
    (f : type-Set (hom-set x y)) →
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( comp-hom-associative-composition-operation-binary-family-Set h g) (f)) ＝
    ( comp-hom-associative-composition-operation-binary-family-Set
      ( h) (comp-hom-associative-composition-operation-binary-family-Set g f))
  witness-associative-composition-operation-binary-family-Set h g f =
    eq-involutive-eq
      ( involutive-eq-associative-composition-operation-binary-family-Set h g f)

Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precategory l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( λ hom-set →
          Σ ( associative-composition-operation-binary-family-Set hom-set)
            ( λ (comp-hom , assoc-comp) →
              is-unital-composition-operation-binary-family-Set
                ( hom-set)
                ( comp-hom))))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  precategory-Large-Precategory :
    (l : Level) → Precategory (α l) (β l l)
  pr1 (precategory-Large-Precategory l) =
    obj-Large-Precategory C l
  pr1 (pr2 (precategory-Large-Precategory l)) =
    hom-set-Large-Precategory C
  pr1 (pr1 (pr2 (pr2 (precategory-Large-Precategory l)))) =
    comp-hom-Large-Precategory C
  pr2 (pr1 (pr2 (pr2 (precategory-Large-Precategory l)))) =
    involutive-eq-associative-comp-hom-Large-Precategory C
  pr1 (pr2 (pr2 (pr2 (precategory-Large-Precategory l)))) x =
    id-hom-Large-Precategory C
  pr1 (pr2 (pr2 (pr2 (pr2 (precategory-Large-Precategory l))))) =
    left-unit-law-comp-hom-Large-Precategory C
  pr2 (pr2 (pr2 (pr2 (pr2 (precategory-Large-Precategory l))))) =
    right-unit-law-comp-hom-Large-Precategory C

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  obj-Precategory : UU l1
  obj-Precategory = pr1 C

  hom-set-Precategory : (x y : obj-Precategory) → Set l2
  hom-set-Precategory = pr1 (pr2 C)

  hom-Precategory : (x y : obj-Precategory) → UU l2
  hom-Precategory x y = type-Set (hom-set-Precategory x y)

  is-set-hom-Precategory :
    (x y : obj-Precategory) → is-set (hom-Precategory x y)
  is-set-hom-Precategory x y = is-set-type-Set (hom-set-Precategory x y)

  associative-composition-operation-Precategory :
    associative-composition-operation-binary-family-Set hom-set-Precategory
  associative-composition-operation-Precategory = pr1 (pr2 (pr2 C))

  comp-hom-Precategory :
    {x y z : obj-Precategory} →
    hom-Precategory y z →
    hom-Precategory x y →
    hom-Precategory x z
  comp-hom-Precategory =
    comp-hom-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

  comp-hom-Precategory' :
    {x y z : obj-Precategory} →
    hom-Precategory x y →
    hom-Precategory y z →
    hom-Precategory x z
  comp-hom-Precategory' f g = comp-hom-Precategory g f

  involutive-eq-associative-comp-hom-Precategory :
    {x y z w : obj-Precategory}
    (h : hom-Precategory z w)
    (g : hom-Precategory y z)
    (f : hom-Precategory x y) →
    ( comp-hom-Precategory (comp-hom-Precategory h g) f) ＝ⁱ
    ( comp-hom-Precategory h (comp-hom-Precategory g f))
  involutive-eq-associative-comp-hom-Precategory =
    involutive-eq-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

  associative-comp-hom-Precategory :
    {x y z w : obj-Precategory}
    (h : hom-Precategory z w)
    (g : hom-Precategory y z)
    (f : hom-Precategory x y) →
    ( comp-hom-Precategory (comp-hom-Precategory h g) f) ＝
    ( comp-hom-Precategory h (comp-hom-Precategory g f))
  associative-comp-hom-Precategory =
    witness-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

  is-unital-composition-operation-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( comp-hom-Precategory)
  is-unital-composition-operation-Precategory = pr2 (pr2 (pr2 C))

  id-hom-Precategory : {x : obj-Precategory} → hom-Precategory x x
  id-hom-Precategory {x} = pr1 is-unital-composition-operation-Precategory x

  left-unit-law-comp-hom-Precategory :
    {x y : obj-Precategory} (f : hom-Precategory x y) →
    comp-hom-Precategory id-hom-Precategory f ＝ f
  left-unit-law-comp-hom-Precategory =
    pr1 (pr2 is-unital-composition-operation-Precategory)

  right-unit-law-comp-hom-Precategory :
    {x y : obj-Precategory} (f : hom-Precategory x y) →
    comp-hom-Precategory f id-hom-Precategory ＝ f
  right-unit-law-comp-hom-Precategory =
    pr2 (pr2 is-unital-composition-operation-Precategory)

is-iso-Precategory :
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : hom-Precategory C x y) →
  UU l2
is-iso-Precategory C {x} {y} f =
  Σ ( hom-Precategory C y x)
    ( λ g →
      ( comp-hom-Precategory C f g ＝ id-hom-Precategory C) ×
      ( comp-hom-Precategory C g f ＝ id-hom-Precategory C))

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  all-elements-equal-is-iso-Precategory :
    (f : hom-Precategory C x y)
    (H K : is-iso-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-Precategory f
    (g , p , q) (g' , p' , q') =
    eq-type-subtype
      ( λ g →
        product-Prop
          ( Id-Prop
            ( hom-set-Precategory C y y)
            ( comp-hom-Precategory C f g)
            ( id-hom-Precategory C))
          ( Id-Prop
            ( hom-set-Precategory C x x)
            ( comp-hom-Precategory C g f)
            ( id-hom-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Precategory C g)) ∙
        ( ap ( comp-hom-Precategory C g) (inv p')) ∙
        ( inv (associative-comp-hom-Precategory C g f g')) ∙
        ( ap ( comp-hom-Precategory' C g') q) ∙
        ( left-unit-law-comp-hom-Precategory C g'))

  is-prop-is-iso-Precategory :
    (f : hom-Precategory C x y) →
    is-prop (is-iso-Precategory C f)
  is-prop-is-iso-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-Precategory f)

  is-iso-prop-Precategory :
    (f : hom-Precategory C x y) → Prop l2
  pr1 (is-iso-prop-Precategory f) = is-iso-Precategory C f
  pr2 (is-iso-prop-Precategory f) = is-prop-is-iso-Precategory f

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  iso-Precategory : UU l2
  iso-Precategory = Σ (hom-Precategory C x y) (is-iso-Precategory C)

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-set-iso-Precategory : is-set (iso-Precategory C x y)
  is-set-iso-Precategory =
    is-set-type-subtype
      ( is-iso-prop-Precategory C)
      ( is-set-hom-Precategory C x y)

  iso-set-Precategory : Set l2
  pr1 iso-set-Precategory = iso-Precategory C x y
  pr2 iso-set-Precategory = is-set-iso-Precategory

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  hom-iso-Precategory : hom-Precategory C x y
  hom-iso-Precategory = pr1 f

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x : obj-Precategory C}
  where

  is-iso-id-hom-Precategory :
    is-iso-Precategory C (id-hom-Precategory C {x})
  pr1 is-iso-id-hom-Precategory = id-hom-Precategory C
  pr1 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)
  pr2 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)

  id-iso-Precategory : iso-Precategory C x x
  pr1 id-iso-Precategory = id-hom-Precategory C
  pr2 id-iso-Precategory = is-iso-id-hom-Precategory

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  hom-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → hom-Precategory C x y
  hom-eq-Precategory x .x refl = id-hom-Precategory C

  iso-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → iso-Precategory C x y
  pr1 (iso-eq-Precategory x y p) = hom-eq-Precategory x y p
  pr2 (iso-eq-Precategory x .x refl) = is-iso-id-hom-Precategory C

  compute-hom-iso-eq-Precategory :
    {x y : obj-Precategory C} →
    (p : x ＝ y) →
    hom-eq-Precategory x y p ＝
    hom-iso-Precategory C (iso-eq-Precategory x y p)
  compute-hom-iso-eq-Precategory p = refl

  is-category-prop-Precategory : Prop (l1 ⊔ l2)
  is-category-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y → is-equiv-Prop (iso-eq-Precategory x y)))

  is-category-Precategory : UU (l1 ⊔ l2)
  is-category-Precategory = type-Prop is-category-prop-Precategory

  is-prop-is-category-Precategory : is-prop is-category-Precategory
  is-prop-is-category-Precategory =
    is-prop-type-Prop is-category-prop-Precategory

Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Category l1 l2 = Σ (Precategory l1 l2) (is-category-Precategory)

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  precategory-Category : Precategory l1 l2
  precategory-Category = pr1 C

  obj-Category : UU l1
  obj-Category = obj-Precategory precategory-Category

  is-category-Category :
    is-category-Precategory precategory-Category
  is-category-Category = pr2 C

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level}
  where

  compute-hom-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) →
    hom-eq-Precategory (precategory-Large-Precategory C l1) X Y ~
    hom-eq-Large-Precategory C X Y
  compute-hom-eq-Large-Precategory X .X refl = refl

  compute-iso-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) →
    iso-eq-Precategory (precategory-Large-Precategory C l1) X Y ~
    iso-eq-Large-Precategory C X Y
  compute-iso-eq-Large-Precategory X Y p =
    eq-iso-eq-hom-Large-Precategory C
      ( iso-eq-Precategory (precategory-Large-Precategory C l1) X Y p)
      ( iso-eq-Large-Precategory C X Y p)
      ( compute-hom-eq-Large-Precategory X Y p)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  (is-large-category-C : is-large-category-Large-Precategory C)
  where

  is-category-is-large-category-Large-Precategory :
    (l : Level) → is-category-Precategory (precategory-Large-Precategory C l)
  is-category-is-large-category-Large-Precategory l X Y =
    is-equiv-htpy
      ( iso-eq-Large-Precategory C X Y)
      ( compute-iso-eq-Large-Precategory C X Y)
      ( is-large-category-C X Y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β)
  where

  precategory-Large-Category : (l : Level) → Precategory (α l) (β l l)
  precategory-Large-Category =
    precategory-Large-Precategory (large-precategory-Large-Category C)

  is-category-Large-Category :
    (l : Level) → is-category-Precategory (precategory-Large-Category l)
  is-category-Large-Category =
    is-category-is-large-category-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-large-category-Large-Category C)

  category-Large-Category : (l : Level) → Category (α l) (β l l)
  pr1 (category-Large-Category l) = precategory-Large-Category l
  pr2 (category-Large-Category l) = is-category-Large-Category l

module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  where

  is-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory 𝒞)
      ( λ x →
        Π-Prop
          ( obj-Precategory 𝒞)
          ( λ y → is-emb-Prop (iso-eq-Precategory 𝒞 x y)))

  is-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-preunivalent-Precategory = type-Prop is-preunivalent-prop-Precategory

module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  where

  is-strongly-preunivalent-prop-Precategory : Prop (l1 ⊔ l2)
  is-strongly-preunivalent-prop-Precategory =
    Π-Prop
      ( obj-Precategory 𝒞)
      ( λ x →
        is-set-Prop
          ( Σ ( obj-Precategory 𝒞)
              ( iso-Precategory 𝒞 x)))

  is-strongly-preunivalent-Precategory : UU (l1 ⊔ l2)
  is-strongly-preunivalent-Precategory =
    type-Prop is-strongly-preunivalent-prop-Precategory

  is-preunivalent-is-strongly-preunivalent-Precategory :
    is-strongly-preunivalent-Precategory →
    is-preunivalent-Precategory 𝒞
  is-preunivalent-is-strongly-preunivalent-Precategory H x y =
    is-emb-is-prop-map
      ( backward-implication-structured-equality-duality
        ( is-prop-equiv')
        ( H x)
        ( x)
        ( iso-eq-Precategory 𝒞 x)
        ( y))

Strongly-Preunivalent-Category : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strongly-Preunivalent-Category l1 l2 =
  Σ (Precategory l1 l2) (is-strongly-preunivalent-Precategory)

module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  precategory-Strongly-Preunivalent-Category : Precategory l1 l2
  precategory-Strongly-Preunivalent-Category = pr1 𝒞

  obj-Strongly-Preunivalent-Category : UU l1
  obj-Strongly-Preunivalent-Category =
    obj-Precategory precategory-Strongly-Preunivalent-Category


  hom-set-Strongly-Preunivalent-Category :
    obj-Strongly-Preunivalent-Category →
    obj-Strongly-Preunivalent-Category →
    Set l2
  hom-set-Strongly-Preunivalent-Category =
    hom-set-Precategory precategory-Strongly-Preunivalent-Category

  hom-Strongly-Preunivalent-Category :
    obj-Strongly-Preunivalent-Category →
    obj-Strongly-Preunivalent-Category →
    UU l2
  hom-Strongly-Preunivalent-Category =
    hom-Precategory precategory-Strongly-Preunivalent-Category

  is-set-hom-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) →
    is-set (hom-Strongly-Preunivalent-Category x y)
  is-set-hom-Strongly-Preunivalent-Category =
    is-set-hom-Precategory precategory-Strongly-Preunivalent-Category

  comp-hom-Strongly-Preunivalent-Category :
    {x y z : obj-Strongly-Preunivalent-Category} →
    hom-Strongly-Preunivalent-Category y z →
    hom-Strongly-Preunivalent-Category x y →
    hom-Strongly-Preunivalent-Category x z
  comp-hom-Strongly-Preunivalent-Category =
    comp-hom-Precategory precategory-Strongly-Preunivalent-Category

  associative-comp-hom-Strongly-Preunivalent-Category :
    {x y z w : obj-Strongly-Preunivalent-Category}
    (h : hom-Strongly-Preunivalent-Category z w)
    (g : hom-Strongly-Preunivalent-Category y z)
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( comp-hom-Strongly-Preunivalent-Category h g)
      ( f) ＝
    comp-hom-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-Strongly-Preunivalent-Category g f)
  associative-comp-hom-Strongly-Preunivalent-Category =
    associative-comp-hom-Precategory precategory-Strongly-Preunivalent-Category

  involutive-eq-associative-comp-hom-Strongly-Preunivalent-Category :
    {x y z w : obj-Strongly-Preunivalent-Category}
    (h : hom-Strongly-Preunivalent-Category z w)
    (g : hom-Strongly-Preunivalent-Category y z)
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( comp-hom-Strongly-Preunivalent-Category h g)
      ( f) ＝ⁱ
    comp-hom-Strongly-Preunivalent-Category
      ( h)
      ( comp-hom-Strongly-Preunivalent-Category g f)
  involutive-eq-associative-comp-hom-Strongly-Preunivalent-Category =
    involutive-eq-associative-comp-hom-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  associative-composition-operation-Strongly-Preunivalent-Category :
    associative-composition-operation-binary-family-Set
      hom-set-Strongly-Preunivalent-Category
  associative-composition-operation-Strongly-Preunivalent-Category =
    associative-composition-operation-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  id-hom-Strongly-Preunivalent-Category :
    {x : obj-Strongly-Preunivalent-Category} →
    hom-Strongly-Preunivalent-Category x x
  id-hom-Strongly-Preunivalent-Category =
    id-hom-Precategory precategory-Strongly-Preunivalent-Category

  left-unit-law-comp-hom-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category}
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( id-hom-Strongly-Preunivalent-Category)
      ( f) ＝
    f
  left-unit-law-comp-hom-Strongly-Preunivalent-Category =
    left-unit-law-comp-hom-Precategory
      precategory-Strongly-Preunivalent-Category

  right-unit-law-comp-hom-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category}
    (f : hom-Strongly-Preunivalent-Category x y) →
    comp-hom-Strongly-Preunivalent-Category
      ( f)
      ( id-hom-Strongly-Preunivalent-Category) ＝
    f
  right-unit-law-comp-hom-Strongly-Preunivalent-Category =
    right-unit-law-comp-hom-Precategory
      precategory-Strongly-Preunivalent-Category

  is-unital-composition-operation-Strongly-Preunivalent-Category :
    is-unital-composition-operation-binary-family-Set
      hom-set-Strongly-Preunivalent-Category
      comp-hom-Strongly-Preunivalent-Category
  is-unital-composition-operation-Strongly-Preunivalent-Category =
    is-unital-composition-operation-Precategory
      ( precategory-Strongly-Preunivalent-Category)

  is-strongly-preunivalent-Strongly-Preunivalent-Category :
    is-strongly-preunivalent-Precategory
      precategory-Strongly-Preunivalent-Category
  is-strongly-preunivalent-Strongly-Preunivalent-Category = pr2 𝒞

  iso-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) → UU l2
  iso-Strongly-Preunivalent-Category =
    iso-Precategory precategory-Strongly-Preunivalent-Category

  iso-eq-Strongly-Preunivalent-Category :
    (x y : obj-Strongly-Preunivalent-Category) →
    x ＝ y → iso-Strongly-Preunivalent-Category x y
  iso-eq-Strongly-Preunivalent-Category =
    iso-eq-Precategory precategory-Strongly-Preunivalent-Category

  is-preunivalent-Strongly-Preunivalent-Category :
    is-preunivalent-Precategory precategory-Strongly-Preunivalent-Category
  is-preunivalent-Strongly-Preunivalent-Category =
    is-preunivalent-is-strongly-preunivalent-Precategory
      ( precategory-Strongly-Preunivalent-Category)
      ( is-strongly-preunivalent-Strongly-Preunivalent-Category)

  emb-iso-eq-Strongly-Preunivalent-Category :
    {x y : obj-Strongly-Preunivalent-Category} →
    (x ＝ y) ↪ (iso-Precategory precategory-Strongly-Preunivalent-Category x y)
  emb-iso-eq-Strongly-Preunivalent-Category {x} {y} =
    ( iso-eq-Precategory precategory-Strongly-Preunivalent-Category x y ,
      is-preunivalent-Strongly-Preunivalent-Category x y)

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-strongly-preunivalent-category-Category :
    is-strongly-preunivalent-Precategory (precategory-Category C)
  is-strongly-preunivalent-category-Category x =
    is-set-is-contr
      ( fundamental-theorem-id'
        ( iso-eq-Precategory (precategory-Category C) x)
        ( is-category-Category C x))

  strongly-preunivalent-category-Category : Strongly-Preunivalent-Category l1 l2
  strongly-preunivalent-category-Category =
    ( precategory-Category C , is-strongly-preunivalent-category-Category)

module _
  {l1 l2 : Level} (𝒞 : Strongly-Preunivalent-Category l1 l2)
  where

  is-1-type-obj-Strongly-Preunivalent-Category :
    is-1-type (obj-Strongly-Preunivalent-Category 𝒞)
  is-1-type-obj-Strongly-Preunivalent-Category x y =
    is-set-is-emb
      ( iso-eq-Precategory (precategory-Strongly-Preunivalent-Category 𝒞) x y)
      ( is-preunivalent-Strongly-Preunivalent-Category 𝒞 x y)
      ( is-set-iso-Precategory (precategory-Strongly-Preunivalent-Category 𝒞))

  obj-1-type-Strongly-Preunivalent-Category : 1-Type l1
  pr1 obj-1-type-Strongly-Preunivalent-Category =
    obj-Strongly-Preunivalent-Category 𝒞
  pr2 obj-1-type-Strongly-Preunivalent-Category =
    is-1-type-obj-Strongly-Preunivalent-Category

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-1-type-obj-Category : is-1-type (obj-Category C)
  is-1-type-obj-Category =
    is-1-type-obj-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)

  obj-1-type-Category : 1-Type l1
  obj-1-type-Category =
    obj-1-type-Strongly-Preunivalent-Category
      ( strongly-preunivalent-category-Category C)

Semigroup-Category : (l : Level) → Category (lsuc l) l
Semigroup-Category = category-Large-Category Semigroup-Large-Category

is-1-type-Semigroup : {l : Level} → is-1-type (Semigroup l)
is-1-type-Semigroup {l} = is-1-type-obj-Category (Semigroup-Category l)
```

We now turn to the proof that isomorphic groups are equal.
Analogously to the map `iso-eq` of semigroups, we have a map `iso-eq` of groups.
Note, however, that the domain of this map is now the identity type `G = H` of the _groups_ `G` and `H`, so the maps `iso-eq` of semigroups and groups are not exactly the same maps.

## Definition 19.3.5

Let `G` and `H` be groups in a univalent universe `𝒰`.
We define the family of maps

```text
iso-eq : (G = H) → (G ≅ H)
```

indexed by `H : Group_𝒰` by `iso-eq(refl) ≔ id[G]`.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (C : Large-Precategory α β)
  where

  Full-Large-Subprecategory : UUω
  Full-Large-Subprecategory =
    {l : Level} → subtype (γ l) (obj-Large-Precategory C l)

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (C : Large-Precategory α β)
  (P : Full-Large-Subprecategory γ C)
  where

  is-in-obj-Full-Large-Subprecategory :
    {l : Level} (X : obj-Large-Precategory C l) → UU (γ l)
  is-in-obj-Full-Large-Subprecategory X = is-in-subtype P X

  is-prop-is-in-obj-Full-Large-Subprecategory :
    {l : Level} (X : obj-Large-Precategory C l) →
    is-prop (is-in-obj-Full-Large-Subprecategory X)
  is-prop-is-in-obj-Full-Large-Subprecategory =
    is-prop-is-in-subtype P

  obj-Full-Large-Subprecategory : (l : Level) → UU (α l ⊔ γ l)
  obj-Full-Large-Subprecategory l = type-subtype (P {l})

  hom-set-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2) →
    Set (β l1 l2)
  hom-set-Full-Large-Subprecategory X Y =
    hom-set-Large-Precategory C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)

  hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2) →
    UU (β l1 l2)
  hom-Full-Large-Subprecategory X Y =
    hom-Large-Precategory C
      ( inclusion-subtype P X)
      ( inclusion-subtype P Y)

  comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3) →
    hom-Full-Large-Subprecategory Y Z → hom-Full-Large-Subprecategory X Y →
    hom-Full-Large-Subprecategory X Z
  comp-hom-Full-Large-Subprecategory X Y Z =
    comp-hom-Large-Precategory C

  id-hom-Full-Large-Subprecategory :
    {l1 : Level} (X : obj-Full-Large-Subprecategory l1) →
    hom-Full-Large-Subprecategory X X
  id-hom-Full-Large-Subprecategory X =
    id-hom-Large-Precategory C

  associative-comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3)
    (W : obj-Full-Large-Subprecategory l4)
    (h : hom-Full-Large-Subprecategory Z W)
    (g : hom-Full-Large-Subprecategory Y Z)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y W
      ( comp-hom-Full-Large-Subprecategory Y Z W h g)
      ( f) ＝
    comp-hom-Full-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Full-Large-Subprecategory X Y Z g f)
  associative-comp-hom-Full-Large-Subprecategory X Y Z W =
    associative-comp-hom-Large-Precategory C

  involutive-eq-associative-comp-hom-Full-Large-Subprecategory :
    {l1 l2 l3 l4 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (Z : obj-Full-Large-Subprecategory l3)
    (W : obj-Full-Large-Subprecategory l4)
    (h : hom-Full-Large-Subprecategory Z W)
    (g : hom-Full-Large-Subprecategory Y Z)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y W
      ( comp-hom-Full-Large-Subprecategory Y Z W h g)
      ( f) ＝ⁱ
    comp-hom-Full-Large-Subprecategory X Z W
      ( h)
      ( comp-hom-Full-Large-Subprecategory X Y Z g f)
  involutive-eq-associative-comp-hom-Full-Large-Subprecategory X Y Z W =
    involutive-eq-associative-comp-hom-Large-Precategory C

  left-unit-law-comp-hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X Y Y
      ( id-hom-Full-Large-Subprecategory Y)
      ( f) ＝
    f
  left-unit-law-comp-hom-Full-Large-Subprecategory X Y =
    left-unit-law-comp-hom-Large-Precategory C

  right-unit-law-comp-hom-Full-Large-Subprecategory :
    {l1 l2 : Level}
    (X : obj-Full-Large-Subprecategory l1)
    (Y : obj-Full-Large-Subprecategory l2)
    (f : hom-Full-Large-Subprecategory X Y) →
    comp-hom-Full-Large-Subprecategory X X Y
      ( f)
      ( id-hom-Full-Large-Subprecategory X) ＝
    f
  right-unit-law-comp-hom-Full-Large-Subprecategory X Y =
    right-unit-law-comp-hom-Large-Precategory C

  large-precategory-Full-Large-Subprecategory :
    Large-Precategory (λ l → α l ⊔ γ l) β
  obj-Large-Precategory
    large-precategory-Full-Large-Subprecategory =
    obj-Full-Large-Subprecategory
  hom-set-Large-Precategory
    large-precategory-Full-Large-Subprecategory =
    hom-set-Full-Large-Subprecategory
  comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory
    {l1} {l2} {l3} {X} {Y} {Z} =
    comp-hom-Full-Large-Subprecategory X Y Z
  id-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {X} =
    id-hom-Full-Large-Subprecategory X
  involutive-eq-associative-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory
    {l1} {l2} {l3} {l4} {X} {Y} {Z} {W} =
    involutive-eq-associative-comp-hom-Full-Large-Subprecategory X Y Z W
  left-unit-law-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {l2} {X} {Y} =
    left-unit-law-comp-hom-Full-Large-Subprecategory X Y
  right-unit-law-comp-hom-Large-Precategory
    large-precategory-Full-Large-Subprecategory {l1} {l2} {X} {Y} =
    right-unit-law-comp-hom-Full-Large-Subprecategory X Y

Group-Full-Large-Subprecategory :
  Full-Large-Subprecategory (λ l → l) Semigroup-Large-Precategory
Group-Full-Large-Subprecategory = is-group-prop-Semigroup

Group-Large-Precategory : Large-Precategory lsuc (_⊔_)
Group-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Semigroup-Large-Precategory)
    ( Group-Full-Large-Subprecategory)

module _
  {l : Level} (G : Group l)
  where

  iso-eq-Group : (H : Group l) → G ＝ H → iso-Group G H
  iso-eq-Group = iso-eq-Large-Precategory Group-Large-Precategory G
```

## Theorem 19.3.6

For any two groups `G` and `H` in a univalent universe `𝒰`, the map

```text
iso-eq : (G = H) → (G ≅ H)
```

is an equivalence.

### Proof

_Proof._ Let `G` and `H` be groups in `𝒰`, and write `UG` and `UH` for their underlying semigroups, respectively.
Then we have a commuting triangle

```text
[(G = H)] --ap{pr1}--> [(UG = UH)]
       \               /
 iso-eq \             / iso-eq
         \           /
          V         V
           [(G ≅ H)]
```

Since being a group is a property of semigroups it follows that the projection map `Group_𝒰 → Semigroup_𝒰` forgetting the unit and inverses, is an embedding.
Thus the top map in this triangle is an equivalence.
The map on the right is an equivalence by Theorem 19.3.3, so the claim follows by the 3-for-2 property. ◻

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    extensionality-Group' : (H : Group l) → (G ＝ H) ≃ iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup (semigroup-Group G) (semigroup-Group H)) ∘e
      ( equiv-ap-inclusion-subtype is-group-prop-Semigroup {s = G} {t = H})

  abstract
    is-torsorial-iso-Group : is-torsorial (λ (H : Group l) → iso-Group G H)
    is-torsorial-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-torsorial-Id G)
```

## Corollary 19.3.7

The type of groups is a `1`-type.

```agda
is-large-category-Group :
  is-large-category-Large-Precategory Group-Large-Precategory
is-large-category-Group G =
  fundamental-theorem-id (is-torsorial-iso-Group G) (iso-eq-Group G)

eq-iso-Group : {l : Level} (G H : Group l) → iso-Group G H → G ＝ H
eq-iso-Group G H = map-inv-is-equiv (is-large-category-Group G H)

Group-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Group-Large-Category = Group-Large-Precategory
is-large-category-Large-Category Group-Large-Category = is-large-category-Group

Group-Category : (l : Level) → Category (lsuc l) l
Group-Category = category-Large-Category Group-Large-Category

is-1-type-Group : {l : Level} → is-1-type (Group l)
is-1-type-Group {l} = is-1-type-obj-Category (Group-Category l)
```
