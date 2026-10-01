# Section 17.2 Propositional extensionality

```agda
module section-17-2-propositional-extensionality where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-4-2-boolean-operations
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-2-observational-equality-booleans
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-1-booleans-are-sets
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-6-universal-property-empty-types
open import exercise-13-7-universal-property-contractible-types
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-3-logic-in-type-theory
open import section-15-3-cantors-diagonal-argument
open import section-17-1-equivalent-forms-of-the-univalence-axiom
```

An important direct consequence of the univalence axiom is the principle of propositional extensionality.
This principle asserts that any two logically equivalent propositions `P` and `Q` can be identified.
Propositional extensionality is an important principle on its own, which is sometimes assumed in formal systems without the univalence axiom.

In order to prove propositional extensionality, we first observe that the univalence axiom also characterizes the identity type of any subuniverse.

## Proposition 17.2.1

Consider a universe `𝒰`, and let `P` be a family of propositions over `𝒰`.
Then the family of maps

```text
  equiv-eq : (A = B) → (pr1(A) ≃ pr1(B))
```

indexed by `A, B : Σ(X : 𝒰) P(X)`, given by `equiv-eq(refl) ≔ id` is an equivalence.

### Proof

Since `P` is a subuniverse, it follows from Corollary 12.2.4 that the projection map is an embedding.
Therefore we see that the asserted map is the composite of the equivalences

```text
           ap_pr1                      equiv-eq
  (A = B) --------> (pr1(A) = pr1(B)) ----------> (pr1(A) ≃ pr1(B)) ◻
```

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
is-subuniverse P = (X : UU _) → is-prop (P X)

subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subuniverse l1 l2 = UU l1 → Prop l2

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-in-subuniverse : (X : UU l1) → UU l2
  is-in-subuniverse X = type-Prop (P X)

  is-prop-is-in-subuniverse : (X : UU l1) → is-prop (is-in-subuniverse X)
  is-prop-is-in-subuniverse X = is-prop-type-Prop (P X)

  type-subuniverse : UU (lsuc l1 ⊔ l2)
  type-subuniverse = Σ (UU l1) is-in-subuniverse

  inclusion-subuniverse : type-subuniverse → UU l1
  inclusion-subuniverse = pr1

  is-in-subuniverse-inclusion-subuniverse :
    (X : type-subuniverse) → is-in-subuniverse (inclusion-subuniverse X)
  is-in-subuniverse-inclusion-subuniverse = pr2

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-essentially-in-subuniverse X =
    Σ (type-subuniverse P) (λ Y → inclusion-subuniverse P Y ≃ X)

  is-proof-irrelevant-is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) →
    is-proof-irrelevant (is-essentially-in-subuniverse X)
  is-proof-irrelevant-is-essentially-in-subuniverse X ((X' , p) , e) =
    is-torsorial-Eq-subtype
      ( is-contr-equiv'
        ( Σ (UU _) (λ T → T ≃ X'))
        ( equiv-tot (equiv-postcomp-equiv e))
        ( is-torsorial-equiv' X'))
      ( is-prop-is-in-subuniverse P)
      ( X')
      ( e)
      ( p)

  is-prop-is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → is-prop (is-essentially-in-subuniverse X)
  is-prop-is-essentially-in-subuniverse X =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-is-essentially-in-subuniverse X)

  is-essentially-in-subuniverse-Prop :
    {l3 : Level} (X : UU l3) → Prop (lsuc l1 ⊔ l2 ⊔ l3)
  pr1 (is-essentially-in-subuniverse-Prop X) =
    is-essentially-in-subuniverse X
  pr2 (is-essentially-in-subuniverse-Prop X) =
    is-prop-is-essentially-in-subuniverse X

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-emb-inclusion-subuniverse : is-emb (inclusion-subuniverse P)
  is-emb-inclusion-subuniverse = is-emb-inclusion-subtype P

  emb-inclusion-subuniverse : type-subuniverse P ↪ UU l1
  emb-inclusion-subuniverse = emb-subtype P

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  equiv-subuniverse : (X Y : type-subuniverse P) → UU l1
  equiv-subuniverse X Y = (pr1 X) ≃ (pr1 Y)

  equiv-eq-subuniverse :
    (X Y : type-subuniverse P) → X ＝ Y → equiv-subuniverse X Y
  equiv-eq-subuniverse X .X refl = id-equiv

  abstract
    is-torsorial-equiv-subuniverse :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse X Y)
    is-torsorial-equiv-subuniverse (X , p) =
      is-torsorial-Eq-subtype
        ( is-torsorial-equiv X)
        ( is-subtype-subuniverse P)
        ( X)
        ( id-equiv)
        ( p)

    is-torsorial-equiv-subuniverse' :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse Y X)
    is-torsorial-equiv-subuniverse' (X , p) =
      is-torsorial-Eq-subtype
        ( is-torsorial-equiv' X)
        ( is-subtype-subuniverse P)
        ( X)
        ( id-equiv)
        ( p)

  abstract
    is-equiv-equiv-eq-subuniverse :
      (X Y : type-subuniverse P) → is-equiv (equiv-eq-subuniverse X Y)
    is-equiv-equiv-eq-subuniverse X =
      fundamental-theorem-id
        ( is-torsorial-equiv-subuniverse X)
        ( equiv-eq-subuniverse X)

  extensionality-subuniverse :
    (X Y : type-subuniverse P) → (X ＝ Y) ≃ equiv-subuniverse X Y
  pr1 (extensionality-subuniverse X Y) = equiv-eq-subuniverse X Y
  pr2 (extensionality-subuniverse X Y) = is-equiv-equiv-eq-subuniverse X Y

  eq-equiv-subuniverse :
    {X Y : type-subuniverse P} → equiv-subuniverse X Y → X ＝ Y
  eq-equiv-subuniverse {X} {Y} =
    map-inv-is-equiv (is-equiv-equiv-eq-subuniverse X Y)

  compute-eq-equiv-id-equiv-subuniverse :
    {X : type-subuniverse P} →
    eq-equiv-subuniverse {X} {X} (id-equiv {A = pr1 X}) ＝ refl
  compute-eq-equiv-id-equiv-subuniverse =
    is-retraction-map-inv-equiv (extensionality-subuniverse _ _) refl
```

## Remark 17.2.2

Often, when `P` is a subuniverse, i.e., a subtype of the a universe `𝒰`, we will also write `A` for the type `pr1(A)` if `A : Σ(X : 𝒰) P(X)`.
Using this shorthand notation, the equivalence in Proposition 17.2.1 is displayed as

```text
  (A = B) ≃ (A ≃ B).
```

Important examples of subuniverses include the subuniverse `Prop_𝒰` of propositions in `𝒰`, the subuniverse `Set_𝒰` of sets in `𝒰`, and the subuniverse `𝒰^{≤ k}` of `k`-truncated types in `𝒰`.
The subuniverse `𝔽` of finite types in `𝒰₀`, and the subuniverses `BS_k` of `k`-element types are further important subuniverses to which Proposition 17.2.1 applies.
Note that by the univalence axiom, any subuniverse is automatically closed under equivalences.
Indeed, if we have `X ≃ Y`, then we have `P(X) → P(Y)` by transporting along the equality `X = Y` induced by univalence.

```agda
is-torsorial-equiv-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  is-torsorial (type-equiv-Truncated-Type A)
is-torsorial-equiv-Truncated-Type A =
  is-torsorial-Eq-subtype
    ( is-torsorial-equiv (type-Truncated-Type A))
    ( is-property-is-trunc _)
    ( type-Truncated-Type A)
    ( id-equiv)
    ( is-trunc-type-Truncated-Type A)

extensionality-Truncated-Type :
  {l : Level} {k : 𝕋} (A B : Truncated-Type l k) →
  (A ＝ B) ≃ type-equiv-Truncated-Type A B
extensionality-Truncated-Type A =
  extensionality-type-subtype
    ( is-trunc-Prop _)
    ( is-trunc-type-Truncated-Type A)
    ( id-equiv)
    ( λ X → equiv-univalence)

abstract
  is-trunc-Truncated-Type :
    {l : Level} (k : 𝕋) → is-trunc (succ-𝕋 k) (Truncated-Type l k)
  is-trunc-Truncated-Type k X Y =
    is-trunc-equiv k
      ( type-equiv-Truncated-Type X Y)
      ( extensionality-Truncated-Type X Y)
      ( is-trunc-type-equiv-Truncated-Type X Y)

Truncated-Type-Truncated-Type :
  (l : Level) (k : 𝕋) → Truncated-Type (lsuc l) (succ-𝕋 k)
pr1 (Truncated-Type-Truncated-Type l k) = Truncated-Type l k
pr2 (Truncated-Type-Truncated-Type l k) = is-trunc-Truncated-Type k

abstract
  is-set-equiv-is-set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  equiv-Set : UU (l1 ⊔ l2)
  equiv-Set = type-Set A ≃ type-Set B

  equiv-set-Set : Set (l1 ⊔ l2)
  pr1 equiv-set-Set = equiv-Set
  pr2 equiv-set-Set =
    is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B)

module _
  {l : Level} (X : Set l)
  where

  equiv-eq-Set : (Y : Set l) → X ＝ Y → equiv-Set X Y
  equiv-eq-Set = equiv-eq-subuniverse is-set-Prop X

  abstract
    is-torsorial-equiv-Set : is-torsorial (λ (Y : Set l) → equiv-Set X Y)
    is-torsorial-equiv-Set =
      is-torsorial-equiv-subuniverse is-set-Prop X

  abstract
    is-equiv-equiv-eq-Set : (Y : Set l) → is-equiv (equiv-eq-Set Y)
    is-equiv-equiv-eq-Set = is-equiv-equiv-eq-subuniverse is-set-Prop X

  eq-equiv-Set : (Y : Set l) → equiv-Set X Y → X ＝ Y
  eq-equiv-Set Y = eq-equiv-subuniverse is-set-Prop

  extensionality-Set : (Y : Set l) → (X ＝ Y) ≃ equiv-Set X Y
  pr1 (extensionality-Set Y) = equiv-eq-Set Y
  pr2 (extensionality-Set Y) = is-equiv-equiv-eq-Set Y
```

## Theorem 17.2.3

Propositions satisfy **propositional extensionality**: For any two propositions `P` and `Q`, the canonical map

```text
  iff-eq : (P = Q) → (P ⇔ Q)
```

defined by `iff-eq(refl) ≔ (id,id)` is an equivalence.
It follows that the type `Prop_𝒰` of propositions in `𝒰` is a set.

### Proof

Recall from Exercise 13.3 that `is-prop(X)` is a proposition for any type `X`.
Proposition 17.2.1 therefore applies, which gives

```text
  (P = Q) ≃ (P ≃ Q) ≃ (P ↔ Q).
```

The last equivalence follows from Proposition 12.1.4, using the fact that `P ≃ Q` is a proposition by Exercise 13.4. ◻

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-iff-Prop P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv)

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P ↔ type-Prop Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q

module _
  {l1 : Level}
  where

  abstract
    is-torsorial-iff :
      (P : Prop l1) → is-torsorial (λ (Q : Prop l1) → type-Prop P ↔ type-Prop Q)
    is-torsorial-iff P =
      is-contr-equiv
        ( Σ (Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
        ( equiv-tot (equiv-equiv-iff P))
        ( is-torsorial-Eq-subtype
          ( is-torsorial-equiv (type-Prop P))
          ( is-property-is-prop)
          ( type-Prop P)
          ( id-equiv)
          ( is-prop-type-Prop P))

  abstract
    is-equiv-iff-eq : (P Q : Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
    is-equiv-iff-eq P =
      fundamental-theorem-id (is-torsorial-iff P) (λ Q → iff-eq {P = P} {Q})

  propositional-extensionality :
    (P Q : Prop l1) → (P ＝ Q) ≃ (type-Prop P ↔ type-Prop Q)
  pr1 (propositional-extensionality P Q) = iff-eq
  pr2 (propositional-extensionality P Q) = is-equiv-iff-eq P Q

  eq-iff' : (P Q : Prop l1) → type-Prop P ↔ type-Prop Q → P ＝ Q
  eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

  eq-iff :
    {P Q : Prop l1} →
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → P ＝ Q
  eq-iff {P} {Q} f g = eq-iff' P Q (pair f g)

  eq-equiv-Prop :
    {P Q : Prop l1} → type-Prop P ≃ type-Prop Q → P ＝ Q
  eq-equiv-Prop e =
    eq-iff (map-equiv e) (map-inv-equiv e)

  equiv-eq-Prop :
    {P Q : Prop l1} → P ＝ Q → type-Prop P ≃ type-Prop Q
  equiv-eq-Prop {P} refl = id-equiv

  is-torsorial-equiv-Prop :
    (P : Prop l1) → is-torsorial (λ Q → type-Prop P ≃ type-Prop Q)
  is-torsorial-equiv-Prop P =
    is-contr-equiv'
      ( Σ (Prop l1) (λ Q → type-Prop P ↔ type-Prop Q))
      ( equiv-tot (equiv-equiv-iff P))
      ( is-torsorial-iff P)
```

## Corollary 17.2.4

The type

```text
  decidable-Prop_𝒰 ≔ Σ(P : Prop_𝒰) is-decidable(P)
```

of decidable propositions in any universe `𝒰` is equivalent to `bool`.

### Proof

Note that `Σ` distributes from the left over coproducts, so we have an equivalence

```text
  (Σ(P : Prop_𝒰) P + ¬ P) ≃ (Σ(P : Prop_𝒰) P) + (Σ(Q : Prop_𝒰) ¬ Q).
```

Therefore it suffices to show that both `Σ(P : Prop_𝒰) P` and `Σ(Q : Prop_𝒰) ¬ Q` are contractible.
At the centers of contraction we have `(unit,⋆)` and `(empty,id)`, respectively.
For the contractions, note that both types are subtypes of the types of propositions.
Therefore it suffices to show that `unit = P` for any proposition `P` equipped with `p : P`, and that `empty = Q` for any proposition `Q` equipped with `q : ¬ Q`.
Both identifications are obtained immediately from propositional extensionality. ◻

```agda
abstract
  is-prop-raise-unit : {l1 : Level} → is-prop (raise-unit l1)
  is-prop-raise-unit {l1} = is-prop-equiv' (compute-raise l1 unit) is-prop-unit

raise-unit-Prop : (l1 : Level) → Prop l1
raise-unit-Prop l1 = raise-unit l1 , is-prop-raise-unit

raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

compute-raise-empty : (l : Level) → empty ≃ raise-empty l
compute-raise-empty l = compute-raise l empty

raise-ex-falso :
  (l1 : Level) {l2 : Level} {A : UU l2} →
  raise-empty l1 → A
raise-ex-falso l = ex-falso ∘ map-inv-equiv (compute-raise-empty l)

abstract
  is-prop-raise-empty :
    {l1 : Level} → is-prop (raise-empty l1)
  is-prop-raise-empty {l1} =
    is-prop-equiv'
      ( compute-raise l1 empty)
      ( is-prop-empty)

raise-empty-Prop :
  (l1 : Level) → Prop l1
pr1 (raise-empty-Prop l1) = raise-empty l1
pr2 (raise-empty-Prop l1) = is-prop-raise-empty

abstract
  is-empty-raise-empty :
    {l1 : Level} → is-empty (raise-empty l1)
  is-empty-raise-empty {l1} = map-inv-equiv (compute-raise-empty l1)

abstract
  is-set-raise-empty :
    {l1 : Level} → is-set (raise-empty l1)
  is-set-raise-empty = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-raise-empty

raise-empty-Set :
  (l1 : Level) → Set l1
pr1 (raise-empty-Set l1) = raise-empty l1
pr2 (raise-empty-Set l1) = is-set-raise-empty

abstract
  is-torsorial-true-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → type-Prop P)
  is-torsorial-true-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-unit l1 ↔ type-Prop P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( equiv-universal-property-contr
                ( raise-star)
                ( is-contr-raise-unit)
                ( type-Prop P)) ∘e
              ( right-unit-law-product-is-contr
                ( is-contr-Π
                  ( λ _ →
                    is-proof-irrelevant-is-prop
                      ( is-prop-raise-unit)
                      ( raise-star)))))))
      ( is-torsorial-iff (raise-unit-Prop l1))

abstract
  is-torsorial-false-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → ¬ (type-Prop P))
  is-torsorial-false-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-empty l1 ↔ type-Prop P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( inv-equiv
                ( equiv-postcomp (type-Prop P) (compute-raise l1 empty))) ∘e
              ( left-unit-law-product-is-contr
                ( universal-property-empty-is-empty
                  ( raise-empty l1)
                  ( is-empty-raise-empty)
                  ( type-Prop P))))))
      ( is-torsorial-iff (raise-empty-Prop l1))

module _
  {l : Level}
  where

  map-equiv-bool-Decidable-Prop : Decidable-Prop l → bool
  map-equiv-bool-Decidable-Prop P =
    rec-coproduct (λ _ → true) (λ _ → false) (is-decidable-Decidable-Prop P)

  map-inv-equiv-bool-Decidable-Prop : bool → Decidable-Prop l
  map-inv-equiv-bool-Decidable-Prop true =
    ( raise-unit l , is-prop-raise-unit , inl raise-star)
  map-inv-equiv-bool-Decidable-Prop false =
    ( raise-empty l , is-prop-raise-empty , inr map-inv-raise)

  is-section-map-inv-equiv-bool-Decidable-Prop :
    (map-equiv-bool-Decidable-Prop ∘ map-inv-equiv-bool-Decidable-Prop) ~ id
  is-section-map-inv-equiv-bool-Decidable-Prop false = refl
  is-section-map-inv-equiv-bool-Decidable-Prop true = refl

  is-retraction-map-inv-equiv-bool-Decidable-Prop :
    (map-inv-equiv-bool-Decidable-Prop ∘ map-equiv-bool-Decidable-Prop) ~ id
  is-retraction-map-inv-equiv-bool-Decidable-Prop prop@(_ , _ , inl _) =
    ap
      ( λ ((t' , is-prop-t') , type-t') → (t' , is-prop-t' , inl type-t'))
      ( eq-is-contr is-torsorial-true-Prop)
  is-retraction-map-inv-equiv-bool-Decidable-Prop prop@(_ , _ , inr _) =
    ap
      ( λ ((t' , is-prop-t') , type-t') → (t' , is-prop-t' , inr type-t'))
      ( eq-is-contr is-torsorial-false-Prop)

  is-equiv-map-equiv-bool-Decidable-Prop :
    is-equiv map-equiv-bool-Decidable-Prop
  is-equiv-map-equiv-bool-Decidable-Prop =
    is-equiv-is-invertible
      ( map-inv-equiv-bool-Decidable-Prop)
      ( is-section-map-inv-equiv-bool-Decidable-Prop)
      ( is-retraction-map-inv-equiv-bool-Decidable-Prop)

  equiv-bool-Decidable-Prop : Decidable-Prop l ≃ bool
  equiv-bool-Decidable-Prop =
    ( map-equiv-bool-Decidable-Prop ,
      is-equiv-map-equiv-bool-Decidable-Prop)

  bool-Decidable-Prop : Decidable-Prop l → bool
  bool-Decidable-Prop = map-equiv equiv-bool-Decidable-Prop

  abstract
    compute-equiv-bool-Decidable-Prop :
      (P : Decidable-Prop l) →
      type-Decidable-Prop P ≃ (map-equiv equiv-bool-Decidable-Prop P ＝ true)
    compute-equiv-bool-Decidable-Prop (P , H , inl p) =
      equiv-is-contr
        ( is-proof-irrelevant-is-prop H p)
        ( is-proof-irrelevant-is-prop (is-set-bool true true) refl)
    compute-equiv-bool-Decidable-Prop (P , H , inr np) =
      equiv-is-empty np neq-false-true-bool
```
