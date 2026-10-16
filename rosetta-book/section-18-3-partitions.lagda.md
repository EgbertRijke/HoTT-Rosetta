# Section 18.3 Partitions

```agda
module section-18-3-partitions where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import exercise-11-4-embedding-triangles
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import exercise-12-13-fiber-inclusions-truncated
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-15-2-surjective-maps
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-4-maps-and-families-of-types
open import section-18-1-equivalence-relations-and-the-replacement-axiom
```

There are many equivalent ways of stating what an equivalence relation is.
We saw in Theorem 18.2.5 that the type of equivalence relations on `A` is equivalent to the type of surjective maps out of `A` into a set.
Here we will show that the type of equivalence relations on `A` is equivalent to the type of partitions of `A`.
Another type that is equivalent to the type of equivalence relations of `A` is the type of set-indexed `Σ`-decompositions of `A`, i.e., the type of triples `(X, Y, e)` consisting of a set `X`, a family `Y` of inhabited types indexed by `X`, and an equivalence `e : A ≃ Σ(x : X) Y(x)`.
The fact that the type of equivalence relations on `A` is equivalent to the type of set-indexed `Σ`-decompositions of `A` is stated as Exercise 18.4

In this section we show that equivalence relations on `A` are partitions of `A`.
Recall that the type of inhabited subtypes of `A` is defined to be

```text
  P_𝒰⁺(A) ≔ Σ(Q : A → Prop_𝒰) ‖Σ(a : A) Q(a)‖.
```

The equivalence of equivalence relations and partitions requires some finesse regarding universes.
This is why we set up the definition of partitions in the following way.

## Definition 18.3.1

Let `A` be a type and let `𝒰` and `𝒱` be two universes.
A **`(𝒰,𝒱)`-partition** of a type `A` is a subset

```text
  P : P_𝒰⁺(A) → Prop_𝒱
```

of the type of inhabited subsets of `A` such that for each `x : A` there is a unique inhabited subset `Q` of `A` in `P` that contains `x`, i.e., if it comes equipped with an element of type

```text
  is-partition(P) := Π(x : A) is-contr(Σ(Q : P_𝒰⁺(A)) P(Q) × Q(x))
```

The type of all `(𝒰,𝒱)`-partitions of `A` is defined by

```text
  Partition_{𝒰,𝒱}(A) ≔ Σ(P : P_𝒰⁺(A) → Prop_𝒱) is-partition(P)
```

```agda
is-partition-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  Prop (l1 ⊔ lsuc l2 ⊔ l3)
is-partition-Prop {l1} {l2} {l3} {A} P =
  Π-Prop A
    ( λ x →
      is-contr-Prop
        ( Σ ( type-subtype P)
            ( λ Q → is-in-inhabited-subtype (inclusion-subtype P Q) x)))

is-partition :
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l3 (inhabited-subtype l2 A)) →
  UU (l1 ⊔ lsuc l2 ⊔ l3)
is-partition P = type-Prop (is-partition-Prop P)

partition :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition {l1} l2 l3 A = type-subtype (is-partition-Prop {l1} {l2} {l3} {A})

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  subtype-partition : subtype l3 (inhabited-subtype l2 A)
  subtype-partition = pr1 P

  is-partition-subtype-partition : is-partition subtype-partition
  is-partition-subtype-partition = pr2 P

  is-block-partition : inhabited-subtype l2 A → UU l3
  is-block-partition = is-in-subtype subtype-partition

  is-prop-is-block-partition :
    (Q : inhabited-subtype l2 A) → is-prop (is-block-partition Q)
  is-prop-is-block-partition = is-prop-is-in-subtype subtype-partition

  block-partition-Large-Type : UU (l1 ⊔ lsuc l2 ⊔ l3)
  block-partition-Large-Type = type-subtype subtype-partition

  inhabited-subtype-block-partition-Large-Type :
    block-partition-Large-Type → inhabited-subtype l2 A
  inhabited-subtype-block-partition-Large-Type =
    inclusion-subtype subtype-partition

  is-emb-inhabited-subtype-block-partition-Large-Type :
    is-emb inhabited-subtype-block-partition-Large-Type
  is-emb-inhabited-subtype-block-partition-Large-Type =
    is-emb-inclusion-subtype subtype-partition

  emb-inhabited-subtype-block-partition-Large-Type :
    block-partition-Large-Type ↪ inhabited-subtype l2 A
  emb-inhabited-subtype-block-partition-Large-Type =
    emb-subtype subtype-partition

  is-block-inhabited-subtype-block-partition-Large-Type :
    (B : block-partition-Large-Type) →
    is-block-partition (inhabited-subtype-block-partition-Large-Type B)
  is-block-inhabited-subtype-block-partition-Large-Type =
    is-in-subtype-inclusion-subtype subtype-partition

  subtype-block-partition-Large-Type :
    block-partition-Large-Type → subtype l2 A
  subtype-block-partition-Large-Type =
    subtype-inhabited-subtype ∘ inhabited-subtype-block-partition-Large-Type

  is-inhabited-subtype-block-partition-Large-Type :
    (B : block-partition-Large-Type) →
    is-inhabited-subtype (subtype-block-partition-Large-Type B)
  is-inhabited-subtype-block-partition-Large-Type B =
    is-inhabited-subtype-inhabited-subtype
      ( inhabited-subtype-block-partition-Large-Type B)

  type-block-partition-Large-Type : block-partition-Large-Type → UU (l1 ⊔ l2)
  type-block-partition-Large-Type Q =
    type-inhabited-subtype (inhabited-subtype-block-partition-Large-Type Q)

  inhabited-type-block-partition-Large-Type :
    block-partition-Large-Type → Inhabited-Type (l1 ⊔ l2)
  inhabited-type-block-partition-Large-Type Q =
    inhabited-type-inhabited-subtype
      ( inhabited-subtype-block-partition-Large-Type Q)

  is-in-block-partition-Large-Type : block-partition-Large-Type → A → UU l2
  is-in-block-partition-Large-Type Q =
    is-in-inhabited-subtype (inhabited-subtype-block-partition-Large-Type Q)

  is-prop-is-in-block-partition-Large-Type :
    (Q : block-partition-Large-Type) (a : A) →
    is-prop (is-in-block-partition-Large-Type Q a)
  is-prop-is-in-block-partition-Large-Type Q =
    is-prop-is-in-inhabited-subtype
      ( inhabited-subtype-block-partition-Large-Type Q)

  large-block-element-partition : A → block-partition-Large-Type
  large-block-element-partition a =
    pr1 (center (is-partition-subtype-partition a))

  is-surjective-large-block-element-partition :
    is-surjective large-block-element-partition
  is-surjective-large-block-element-partition B =
    map-trunc-Prop
      ( λ (a , u) →
        pair
          ( a)
          ( eq-type-subtype
            ( subtype-partition)
            ( ap pr1
              ( ap
                ( inclusion-subtype
                  ( λ Q → subtype-inhabited-subtype (pr1 Q) a))
                ( contraction
                  ( is-partition-subtype-partition a)
                  ( pair B u))))))
      ( is-inhabited-subtype-block-partition-Large-Type B)

  is-locally-small-block-partition-Large-Type :
    is-locally-small (l1 ⊔ l2) block-partition-Large-Type
  is-locally-small-block-partition-Large-Type =
    is-locally-small-type-subtype
      ( subtype-partition)
      ( is-locally-small-inhabited-subtype is-small')

  is-small-block-partition-Large-Type :
    is-small (l1 ⊔ l2) block-partition-Large-Type
  is-small-block-partition-Large-Type =
    is-small-is-surjective
      ( is-surjective-large-block-element-partition)
      ( is-small-lmax l2 A)
      ( is-locally-small-block-partition-Large-Type)

  block-partition : UU (l1 ⊔ l2)
  block-partition = type-is-small is-small-block-partition-Large-Type

  compute-block-partition : block-partition-Large-Type ≃ block-partition
  compute-block-partition = equiv-is-small is-small-block-partition-Large-Type

  map-compute-block-partition : block-partition-Large-Type → block-partition
  map-compute-block-partition = map-equiv compute-block-partition

  make-block-partition :
    (Q : inhabited-subtype l2 A) → is-block-partition Q → block-partition
  make-block-partition Q H = map-compute-block-partition (pair Q H)

  map-inv-compute-block-partition : block-partition → block-partition-Large-Type
  map-inv-compute-block-partition =
    map-inv-equiv compute-block-partition

  is-section-map-inv-compute-block-partition :
    ( map-compute-block-partition ∘ map-inv-compute-block-partition) ~ id
  is-section-map-inv-compute-block-partition =
    is-section-map-inv-equiv compute-block-partition

  is-retraction-map-inv-compute-block-partition :
    ( map-inv-compute-block-partition ∘ map-compute-block-partition) ~ id
  is-retraction-map-inv-compute-block-partition =
    is-retraction-map-inv-equiv compute-block-partition

  inhabited-subtype-block-partition : block-partition → inhabited-subtype l2 A
  inhabited-subtype-block-partition =
    inhabited-subtype-block-partition-Large-Type ∘
    map-inv-compute-block-partition

  is-emb-inhabited-subtype-block-partition :
    is-emb inhabited-subtype-block-partition
  is-emb-inhabited-subtype-block-partition =
    is-emb-comp
      ( inhabited-subtype-block-partition-Large-Type)
      ( map-inv-compute-block-partition)
      ( is-emb-inhabited-subtype-block-partition-Large-Type)
      ( is-emb-is-equiv (is-equiv-map-inv-equiv compute-block-partition))

  emb-inhabited-subtype-block-partition :
    block-partition ↪ inhabited-subtype l2 A
  pr1 emb-inhabited-subtype-block-partition = inhabited-subtype-block-partition
  pr2 emb-inhabited-subtype-block-partition =
    is-emb-inhabited-subtype-block-partition

  is-block-inhabited-subtype-block-partition :
    (B : block-partition) →
    is-block-partition (inhabited-subtype-block-partition B)
  is-block-inhabited-subtype-block-partition B =
    is-block-inhabited-subtype-block-partition-Large-Type
      ( map-inv-compute-block-partition B)

  subtype-block-partition : block-partition → subtype l2 A
  subtype-block-partition =
    subtype-block-partition-Large-Type ∘ map-inv-compute-block-partition

  inhabited-type-block-partition : block-partition → Inhabited-Type (l1 ⊔ l2)
  inhabited-type-block-partition B =
    inhabited-type-block-partition-Large-Type
      ( map-inv-compute-block-partition B)

  is-inhabited-subtype-block-partition :
    (B : block-partition) → is-inhabited-subtype (subtype-block-partition B)
  is-inhabited-subtype-block-partition B =
    is-inhabited-subtype-block-partition-Large-Type
      ( map-inv-compute-block-partition B)

  type-block-partition : block-partition → UU (l1 ⊔ l2)
  type-block-partition B =
    type-block-partition-Large-Type (map-inv-compute-block-partition B)

  is-in-block-partition : (B : block-partition) → A → UU l2
  is-in-block-partition B =
    is-in-block-partition-Large-Type (map-inv-compute-block-partition B)

  is-prop-is-in-block-partition :
    (B : block-partition) (a : A) → is-prop (is-in-block-partition B a)
  is-prop-is-in-block-partition B =
    is-prop-is-in-block-partition-Large-Type
      ( map-inv-compute-block-partition B)

  abstract
    compute-is-in-block-partition :
      (B : inhabited-subtype l2 A) (H : is-block-partition B) (x : A) →
      is-in-inhabited-subtype B x ≃
      is-in-block-partition (make-block-partition B H) x
    compute-is-in-block-partition B H x =
      equiv-tr
        ( λ C → is-in-block-partition-Large-Type C x)
        ( inv (is-retraction-map-inv-compute-block-partition (B , H)))

  abstract
    make-is-in-block-partition :
      (B : inhabited-subtype l2 A) (H : is-block-partition B) (x : A) →
      is-in-inhabited-subtype B x →
      is-in-block-partition (make-block-partition B H) x
    make-is-in-block-partition B H x K =
      map-equiv (compute-is-in-block-partition B H x) K

  block-containing-element-partition : A → UU (l1 ⊔ l2)
  block-containing-element-partition a =
    Σ block-partition (λ B → is-in-block-partition B a)

  abstract
    is-contr-block-containing-element-partition :
      (a : A) → is-contr (block-containing-element-partition a)
    is-contr-block-containing-element-partition a =
      is-contr-equiv'
        ( Σ block-partition-Large-Type
          ( λ B → is-in-block-partition-Large-Type B a))
        ( equiv-Σ
          ( λ B → is-in-block-partition B a)
          ( compute-block-partition)
          ( λ B →
            equiv-tr
              ( λ C → is-in-block-partition-Large-Type C a)
              ( inv (is-retraction-map-inv-compute-block-partition B))))
        ( is-partition-subtype-partition a)

  center-block-containing-element-partition :
    (a : A) → block-containing-element-partition a
  center-block-containing-element-partition a =
    center (is-contr-block-containing-element-partition a)

  class-partition : A → block-partition
  class-partition a =
    pr1 (center-block-containing-element-partition a)

  is-block-class-partition :
    (a : A) →
    is-block-partition (inhabited-subtype-block-partition (class-partition a))
  is-block-class-partition a =
    is-block-inhabited-subtype-block-partition (class-partition a)

  is-in-block-class-partition :
    (a : A) → is-in-block-partition (class-partition a) a
  is-in-block-class-partition a =
    pr2 (center-block-containing-element-partition a)

  compute-base-type-partition : Σ block-partition type-block-partition ≃ A
  compute-base-type-partition =
    ( right-unit-law-Σ-is-contr
      ( λ x → is-contr-block-containing-element-partition x)) ∘e
    ( equiv-left-swap-Σ)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  has-same-blocks-partition :
    {l4 : Level} (Q : partition l2 l4 A) → UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  has-same-blocks-partition Q =
    has-same-elements-subtype (subtype-partition P) (subtype-partition Q)

  refl-has-same-blocks-partition : has-same-blocks-partition P
  refl-has-same-blocks-partition =
    refl-has-same-elements-subtype (subtype-partition P)

  extensionality-partition :
    (Q : partition l2 l3 A) → (P ＝ Q) ≃ has-same-blocks-partition Q
  extensionality-partition =
    extensionality-type-subtype
      ( is-partition-Prop)
      ( is-partition-subtype-partition P)
      ( refl-has-same-elements-subtype (subtype-partition P))
      ( extensionality-subtype (subtype-partition P))

  eq-has-same-blocks-partition :
    (Q : partition l2 l3 A) → has-same-blocks-partition Q → P ＝ Q
  eq-has-same-blocks-partition Q =
    map-inv-equiv (extensionality-partition Q)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A) (B : block-partition P)
  where

  has-same-elements-block-partition-Prop :
    block-partition P → Prop (l1 ⊔ l2)
  has-same-elements-block-partition-Prop C =
    has-same-elements-inhabited-subtype-Prop
      ( inhabited-subtype-block-partition P B)
      ( inhabited-subtype-block-partition P C)

  has-same-elements-block-partition :
    block-partition P → UU (l1 ⊔ l2)
  has-same-elements-block-partition C =
    has-same-elements-inhabited-subtype
      ( inhabited-subtype-block-partition P B)
      ( inhabited-subtype-block-partition P C)

  is-prop-has-same-elements-block-partition :
    (C : block-partition P) → is-prop (has-same-elements-block-partition C)
  is-prop-has-same-elements-block-partition C =
    is-prop-has-same-elements-inhabited-subtype
      ( inhabited-subtype-block-partition P B)
      ( inhabited-subtype-block-partition P C)

  refl-has-same-elements-block-partition :
    has-same-elements-block-partition B
  refl-has-same-elements-block-partition =
    refl-has-same-elements-inhabited-subtype
      ( inhabited-subtype-block-partition P B)

  abstract
    is-torsorial-has-same-elements-block-partition :
      is-torsorial has-same-elements-block-partition
    is-torsorial-has-same-elements-block-partition =
      is-contr-equiv'
        ( Σ ( block-partition P)
            ( λ C →
              inhabited-subtype-block-partition P B ＝
              inhabited-subtype-block-partition P C))
        ( equiv-tot
          ( λ C →
            extensionality-inhabited-subtype
              ( inhabited-subtype-block-partition P B)
              ( inhabited-subtype-block-partition P C)))
        ( fundamental-theorem-id'
          ( λ C → ap (inhabited-subtype-block-partition P))
          ( is-emb-inhabited-subtype-block-partition P B))

  has-same-elements-eq-block-partition :
    (C : block-partition P) → (B ＝ C) →
    has-same-elements-block-partition C
  has-same-elements-eq-block-partition .B refl =
    refl-has-same-elements-block-partition

  is-equiv-has-same-elements-eq-block-partition :
    (C : block-partition P) →
    is-equiv (has-same-elements-eq-block-partition C)
  is-equiv-has-same-elements-eq-block-partition =
    fundamental-theorem-id
      is-torsorial-has-same-elements-block-partition
      has-same-elements-eq-block-partition

  extensionality-block-partition :
    (C : block-partition P) →
    (B ＝ C) ≃ has-same-elements-block-partition C
  pr1 (extensionality-block-partition C) =
    has-same-elements-eq-block-partition C
  pr2 (extensionality-block-partition C) =
    is-equiv-has-same-elements-eq-block-partition C

  eq-has-same-elements-block-partition :
    (C : block-partition P) →
    has-same-elements-block-partition C → B ＝ C
  eq-has-same-elements-block-partition C =
    map-inv-equiv (extensionality-block-partition C)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  is-set-block-partition : is-set (block-partition P)
  is-set-block-partition B C =
    is-prop-equiv
      ( extensionality-block-partition P B C)
      ( is-prop-has-same-elements-block-partition P B C)

  block-partition-Set : Set (l1 ⊔ l2)
  pr1 block-partition-Set = block-partition P
  pr2 block-partition-Set = is-set-block-partition

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  emb-inclusion-block-partition :
    (B : block-partition P) → type-block-partition P B ↪ A
  emb-inclusion-block-partition B =
    comp-emb
      ( emb-equiv (compute-base-type-partition P))
      ( emb-fiber-inclusion
        ( type-block-partition P)
        ( is-set-block-partition P)
        ( B))

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  (B : block-partition P)
  where

  share-common-element-block-partition-Prop :
    (C : block-partition P) → Prop (l1 ⊔ l2)
  share-common-element-block-partition-Prop C =
    ∃ A (λ a → subtype-block-partition P B a ∧ subtype-block-partition P C a)

  share-common-element-block-partition :
    (C : block-partition P) → UU (l1 ⊔ l2)
  share-common-element-block-partition C =
    type-Prop (share-common-element-block-partition-Prop C)

  eq-share-common-element-block-partition :
    (C : block-partition P) → share-common-element-block-partition C → B ＝ C
  eq-share-common-element-block-partition C H =
    apply-universal-property-trunc-Prop H
      ( Id-Prop (block-partition-Set P) B C)
      ( λ (a , K , L) →
        ap
          ( pr1)
          ( eq-is-contr
            ( is-contr-block-containing-element-partition P a)
            { B , K}
            { C , L}))

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  compute-total-block-partition :
    Σ (block-partition P) (type-block-partition P) ≃ A
  compute-total-block-partition =
    ( right-unit-law-Σ-is-contr
      ( is-contr-block-containing-element-partition P)) ∘e
    ( equiv-left-swap-Σ)

  map-compute-total-block-partition :
    Σ (block-partition P) (type-block-partition P) → A
  map-compute-total-block-partition = map-equiv compute-total-block-partition
```

## Theorem 18.3.2

Consider a type `A`, a universe `𝒰`, and consider a universe `𝒱` containing both `A` and every type in `𝒰`.
Then we have an equivalence

```text
  Eq-Rel_𝒰(A) ≃ Partition_{𝒰,𝒱}(A).
```

### Proof

Consider an equivalence relation `R` on `A`.
Then we define

```text
  P : P_𝒰⁺(A) → Prop_𝒱
```

by `P(Q) ≔ ∃_{(x : A)} ∀_{(y : A)} Q(y) ↔ R(x,y)`.
In other words, `P` is the subtype of equivalence classes of `R`, which are all inhabited.
To show that `P` is a partition of `A`, let `x : A`.
The type

```text
  Σ(Q : P_𝒰⁺(A)) P(Q) × Q(x)
```

is equivalent to the type

```text
  Σ(Q : P_𝒰⁺(A)) Π(y : A) Q(y) ↔ R(x,y)
```

since the proposition `∃_{(z : A)} ∀_{(y : A)} Q(y) ↔ R(z,y)` is equivalent to the type `Π(y : A) Q(y) ↔ R(x,y)`, given an element `q : Q(x)`.
By univalence it follows that the latter type is equivalent to the identity type `Q = R(x)` in `P_𝒰⁺(A)`, so the total space is contractible.
Thus we obtain a map

```text
  ψ : Eq-Rel_𝒰(A) → Partition_{𝒰,𝒱}(A).
```

For the converse map, we first define for any `(𝒰,𝒱)`-partition `P` of `A` a binary relation `R_P` such that `R_P(x)` is at the center of contraction in the type

```text
  Σ(Q : P⁺_𝒰(A)) P(Q) × Q(x).
```

In other words, `R_P(x)` is defined to be the unique block in the partition `P` such that `R_P(x,x)` holds.
It is immediate from its definition that `R_P(x,y)` is a proposition in `𝒰`.
To see that `R_P` is symmetric, note that if `R_P(x,y)` holds, then `R_P(x)` is an element of type

```text
  Σ(Q : P⁺_𝒰(A)) P(Q) × Q(y).
```

By contractibility, this implies that `R(x) = R(y)`, from which we obtain that `R(y,x)` holds.
To see that `R_P` is transitive we observe similarly that if `R(x,y)` and `R(y,z)` hold, then we have an identification `R(x) = R(y)` and it follows that `R(x,z)` holds.
Thus we obtain a map

```text
  φ : Partition_{𝒰,𝒱}(A) → Eq-Rel_𝒰(A).
```

It remains to prove that the maps `ψ` and `φ` are inverse to each other, first let `R` be an equivalence relation.
In order to show that `φ(ψ(R)) = R` it suffices by univalence to show that the equivalence relation obtained from the partition induced by `R` is given by

```text
  R'(x,y) := Σ(Q : P_𝒰⁺(A)) (∃_{(u : A)} ∀_{(v : A)} Q(v) ↔ R(u,v)) × Q(x) × Q(y).
```

is equivalent to `R`.
Observe that the proposition `R'(x,y)` is equivalent to `R(x,x) × R(x,y)`, which is equivalent to `R(x,y)`.
This shows that the composite

```text
                ψ                         φ
  Eq-Rel_𝒰(A) ----> Partition_{𝒰,𝒱}(A) ----> Eq-Rel_𝒰(A)
```

is homotopic to the identity function.

Finally, we have to show that for any partition `P` of `A` and any inhabited subtype `Q` of `A` we have `ψ(φ(P))(Q) ↔ P(Q)`.
Note that this is a proposition, so we may assume an element `x : A` such that `Q(x)` holds.
By univalence it follows that `ψ(φ(P))(Q)` holds if and only if `Q = R_P(x)`, where `R_P` is the equivalence relation constructed in the definition of the map `φ`.
Now we see that `P(Q)` holds if and only if `Q` is in the contractible type

```text
  Σ(Q' : P⁺_𝒰(A)) P(Q') × Q'(x),
```

which is the case if and only if `Q = R_P(x)`.
This shows that the composite

```text
                       φ                  ψ
  Partition_{𝒰,𝒱}(A) ----> Eq-Rel_𝒰(A) ----> Partition_{𝒰,𝒱}(A)
```

is homotopic to the identity function. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-block-prop-partition-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-block-prop-partition-equivalence-relation Q =
    is-equivalence-class-Prop R (subtype-inhabited-subtype Q)

  is-block-partition-equivalence-relation :
    inhabited-subtype l2 A → UU (l1 ⊔ l2)
  is-block-partition-equivalence-relation Q =
    type-Prop (is-block-prop-partition-equivalence-relation Q)

  abstract
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation :
      is-partition
        ( is-equivalence-class-inhabited-subtype-equivalence-relation R)
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation x =
      is-contr-equiv
        ( Σ ( Σ ( equivalence-class R)
                ( λ C → is-in-equivalence-class R C x))
            ( λ t → is-inhabited-subtype (subtype-equivalence-class R (pr1 t))))
        ( ( equiv-right-swap-Σ) ∘e
          ( equiv-Σ
            ( λ Q → is-in-subtype (subtype-equivalence-class R (pr1 Q)) x)
            ( equiv-right-swap-Σ)
            ( λ Q → id-equiv)))
        ( is-contr-Σ
          ( is-torsorial-is-in-equivalence-class R x)
          ( center-total-is-in-equivalence-class R x)
          ( is-proof-irrelevant-is-prop
            ( is-prop-type-trunc-Prop)
            ( is-inhabited-subtype-equivalence-class R (class R x))))

  partition-equivalence-relation : partition l2 (l1 ⊔ l2) A
  pr1 partition-equivalence-relation =
    is-block-prop-partition-equivalence-relation
  pr2 partition-equivalence-relation =
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation

  equiv-block-equivalence-class :
    equivalence-class R ≃ block-partition partition-equivalence-relation
  equiv-block-equivalence-class =
    ( compute-block-partition partition-equivalence-relation) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( inv-equiv-inclusion-is-full-subtype
        ( is-inhabited-subtype-Prop ∘ subtype-equivalence-class R)
        ( is-inhabited-subtype-equivalence-class R)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition : A → A → UU (l1 ⊔ l2)
  sim-partition x y =
    Σ ( block-partition P)
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)

  is-proof-irrelevant-sim-partition :
    (x y : A) → is-proof-irrelevant (sim-partition x y)
  is-proof-irrelevant-sim-partition x y (Q , p , q) =
    is-contr-equiv'
      ( Σ ( Σ ( block-partition P)
              ( λ B → is-in-block-partition P B x))
          ( λ B → is-in-block-partition P (pr1 B) y))
      ( associative-Σ)
      ( is-contr-Σ
        ( is-contr-block-containing-element-partition P x)
        ( Q , p)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-in-block-partition P Q y)
          ( q)))

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition x y)

  prop-equivalence-relation-partition : Relation-Prop (l1 ⊔ l2) A
  pr1 (prop-equivalence-relation-partition x y) = sim-partition x y
  pr2 (prop-equivalence-relation-partition x y) = is-prop-sim-partition x y

  refl-sim-partition : is-reflexive sim-partition
  pr1 (refl-sim-partition x) = class-partition P x
  pr1 (pr2 (refl-sim-partition x)) = is-in-block-class-partition P x
  pr2 (pr2 (refl-sim-partition x)) = is-in-block-class-partition P x

  symmetric-sim-partition : is-symmetric sim-partition
  pr1 (symmetric-sim-partition x y (Q , p , q)) = Q
  pr1 (pr2 (symmetric-sim-partition x y (Q , p , q))) = q
  pr2 (pr2 (symmetric-sim-partition x y (Q , p , q))) = p

  transitive-sim-partition : is-transitive sim-partition
  pr1 (transitive-sim-partition x y z (B , p , q) (B' , p' , q')) = B
  pr1 (pr2 (transitive-sim-partition x y z (B , p , q) (B' , p' , q'))) =
    backward-implication
      ( has-same-elements-eq-inhabited-subtype
        ( inhabited-subtype-block-partition P B)
        ( inhabited-subtype-block-partition P B')
        ( ap
          ( inhabited-subtype-block-partition P)
          ( ap
            ( pr1)
            ( eq-is-contr
              ( is-contr-block-containing-element-partition P y)
              { B , p}
              { B' , q'})))
        ( x))
      ( p')
  pr2 (pr2 (transitive-sim-partition x y z (B , p , q) (B' , p' , q'))) = q

  equivalence-relation-partition : equivalence-relation (l1 ⊔ l2) A
  pr1 equivalence-relation-partition = prop-equivalence-relation-partition
  pr1 (pr2 equivalence-relation-partition) = refl-sim-partition
  pr1 (pr2 (pr2 equivalence-relation-partition)) = symmetric-sim-partition
  pr2 (pr2 (pr2 equivalence-relation-partition)) = transitive-sim-partition

  is-inhabited-subtype-prop-equivalence-relation-partition :
    (a : A) → is-inhabited-subtype (prop-equivalence-relation-partition a)
  is-inhabited-subtype-prop-equivalence-relation-partition a =
    unit-trunc-Prop (a , refl-sim-partition a)

  inhabited-subtype-equivalence-relation-partition :
    (a : A) → inhabited-subtype (l1 ⊔ l2) A
  pr1 (inhabited-subtype-equivalence-relation-partition a) =
    prop-equivalence-relation-partition a
  pr2 (inhabited-subtype-equivalence-relation-partition a) =
    is-inhabited-subtype-prop-equivalence-relation-partition a

  is-block-inhabited-subtype-equivalence-relation-partition :
    (a : A) →
    is-block-partition
      ( partition-equivalence-relation equivalence-relation-partition)
      ( inhabited-subtype-equivalence-relation-partition a)
  is-block-inhabited-subtype-equivalence-relation-partition a =
    unit-trunc-Prop (a , (λ x → (id , id)))

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-partition-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-partition (partition-equivalence-relation R))
      ( R)
  pr1
    ( relate-same-elements-equivalence-relation-partition-equivalence-relation
      x y)
    ( C , p , q) =
    apply-universal-property-trunc-Prop
      ( is-block-inhabited-subtype-block-partition
        ( partition-equivalence-relation R)
        ( C))
      ( prop-equivalence-relation R x y)
      ( λ (z , K) →
        transitive-equivalence-relation R
          x _ y
          ( forward-implication (K y) q)
          ( symmetric-equivalence-relation R _ x (forward-implication (K x) p)))
  pr1
    ( pr2
      ( relate-same-elements-equivalence-relation-partition-equivalence-relation
        x y)
      ( r)) =
    make-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
  pr1
    ( pr2
      ( pr2
        ( relate-same-elements-equivalence-relation-partition-equivalence-relation
          x y)
        ( r))) =
    make-is-in-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( x)
      ( refl-equivalence-relation R x)
  pr2
    ( pr2
      ( pr2
        ( relate-same-elements-equivalence-relation-partition-equivalence-relation
          x y)
        ( r))) =
    make-is-in-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( y)
      ( r)

is-section-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (R : equivalence-relation l A) →
  equivalence-relation-partition (partition-equivalence-relation R) ＝ R
is-section-equivalence-relation-partition-equivalence-relation R =
  eq-relate-same-elements-equivalence-relation
    ( equivalence-relation-partition (partition-equivalence-relation R))
    ( R)
    ( relate-same-elements-equivalence-relation-partition-equivalence-relation
      R)

module _
  {l1 l2 : Level} {A : UU l1} (P : partition l1 l2 A)
  where

  abstract
    is-block-is-equivalence-class-equivalence-relation-partition :
      (Q : inhabited-subtype l1 A) →
      is-equivalence-class
        ( equivalence-relation-partition P)
        ( subtype-inhabited-subtype Q) →
      is-block-partition P Q
    is-block-is-equivalence-class-equivalence-relation-partition Q H =
      apply-universal-property-trunc-Prop H
        ( subtype-partition P Q)
        ( λ (a , K) →
          tr
            ( is-block-partition P)
            ( inv
              ( eq-has-same-elements-inhabited-subtype Q
                ( inhabited-subtype-block-partition P (class-partition P a))
                ( λ x →
                  ( iff-equiv
                    ( ( left-unit-law-Σ-is-contr
                        ( is-contr-block-containing-element-partition P a)
                        ( center-block-containing-element-partition P a)) ∘e
                      ( inv-associative-Σ))) ∘iff
                  ( K x))))
            ( is-block-class-partition P a))

  abstract
    is-equivalence-class-is-block-partition :
      (Q : inhabited-subtype l1 A) →
      is-block-partition P Q →
      is-equivalence-class
        ( equivalence-relation-partition P)
        ( subtype-inhabited-subtype Q)
    is-equivalence-class-is-block-partition Q H =
      apply-universal-property-trunc-Prop
        ( is-inhabited-subtype-inhabited-subtype Q)
        ( is-equivalence-class-Prop
          ( equivalence-relation-partition P)
          ( subtype-inhabited-subtype Q))
        ( λ (a , q) →
          unit-trunc-Prop
            ( pair
              ( a)
              ( λ x →
                iff-equiv
                ( ( inv-equiv
                    ( ( left-unit-law-Σ-is-contr
                        ( is-contr-block-containing-element-partition P a)
                        ( ( make-block-partition P Q H) ,
                          ( make-is-in-block-partition P Q H a q))) ∘e
                      ( inv-associative-Σ))) ∘e
                  ( compute-is-in-block-partition P Q H x)))))

  has-same-elements-partition-equivalence-relation-partition :
    has-same-elements-subtype
      ( subtype-partition
        ( partition-equivalence-relation (equivalence-relation-partition P)))
      ( subtype-partition P)
  pr1 (has-same-elements-partition-equivalence-relation-partition Q) H =
    is-block-is-equivalence-class-equivalence-relation-partition Q H
  pr2 (has-same-elements-partition-equivalence-relation-partition Q) H =
    is-equivalence-class-is-block-partition Q H

is-retraction-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (P : partition l l A) →
  partition-equivalence-relation (equivalence-relation-partition P) ＝ P
is-retraction-equivalence-relation-partition-equivalence-relation P =
  eq-has-same-blocks-partition
    ( partition-equivalence-relation (equivalence-relation-partition P))
    ( P)
    ( has-same-elements-partition-equivalence-relation-partition P)

abstract
  is-equiv-equivalence-relation-partition :
    {l : Level} {A : UU l} →
    is-equiv (equivalence-relation-partition {l} {l} {l} {A})
  is-equiv-equivalence-relation-partition =
    is-equiv-is-invertible
      partition-equivalence-relation
      is-section-equivalence-relation-partition-equivalence-relation
      is-retraction-equivalence-relation-partition-equivalence-relation

equiv-equivalence-relation-partition :
  {l : Level} {A : UU l} → partition l l A ≃ equivalence-relation l A
equiv-equivalence-relation-partition =
  ( equivalence-relation-partition , is-equiv-equivalence-relation-partition)
```
