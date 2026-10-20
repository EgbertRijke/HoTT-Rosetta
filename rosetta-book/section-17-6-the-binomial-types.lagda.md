# Section 17.6 The binomial types

```agda
module section-17-6-the-binomial-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-3-4-binomial-coefficients
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-4-2-boolean-operations
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-7-3-the-standard-finite-types
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-6-coproduct-functor-equivalences
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
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import section-13-4-composing-with-equivalences
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-6-universal-property-empty-types
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-16-2-double-counting-in-type-theory
open import section-16-3-finite-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-17-4-maps-and-families-of-types
```

To wrap up this section on univalence, we will use the univalence axiom to construct for any two types `A` and `B` a type `(A choose B)` that has properties similar to the binomial coefficients `(n choose k)`.
Indeed, we will show that if `A` is an `n`-element type and `B` is a `k`-element type, then `(A choose B)` is an `(n choose k)`-element type.
The binomial types are defined using decidable embeddings.

## Definition 17.6.1

A map `f : A → B` is said to be **decidable** if it comes equipped with an element of type

```text
  is-decidable(f) ≔ Π(b : B) is-decidable(fib(f,b)).
```

```agda
open import section-11-4-embeddings using (is-decidable-map)
```

We will write `A ↪ᵈ B` for the type of **decidable embeddings** from `A` to `B`, i.e., for the type of embeddings that are also decidable maps.

## Definition 17.6.2

Consider a type `A` and a universe `𝒰`.
We define the **connected component** of `𝒰` at `A` by

```text
  𝒰_A ≔ Σ(X : 𝒰) ‖A ≃ X‖.
```

```agda
component-UU-Level :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
component-UU-Level l1 A = type-subtype (mere-equiv-Prop {l2 = l1} A)

type-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} → component-UU-Level l1 A → UU l1
type-component-UU-Level X = pr1 X

abstract
  mere-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    mere-equiv A (type-component-UU-Level X)
  mere-equiv-component-UU-Level X = pr2 X

component-UU :
  {l1 : Level} (A : UU l1) → UU (lsuc l1)
component-UU {l1} A = component-UU-Level l1 A

type-component-UU : {l1 : Level} {A : UU l1} (X : component-UU A) → UU l1
type-component-UU X = type-component-UU-Level X

abstract
  mere-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    mere-equiv A (type-component-UU X)
  mere-equiv-component-UU X = mere-equiv-component-UU-Level X

equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) → UU l1
equiv-component-UU-Level X Y =
  type-component-UU-Level X ≃ type-component-UU-Level Y

id-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  equiv-component-UU-Level X X
id-equiv-component-UU-Level X = id-equiv

equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} {X Y : component-UU-Level l1 A} →
  X ＝ Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

abstract
  is-torsorial-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    is-torsorial (equiv-component-UU-Level X)
  is-torsorial-equiv-component-UU-Level X =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv (type-component-UU-Level X))
      ( λ Y → is-prop-mere-equiv _ Y)
      ( type-component-UU-Level X)
      ( id-equiv)
      ( mere-equiv-component-UU-Level X)

abstract
  is-equiv-equiv-eq-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
    is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
  is-equiv-equiv-eq-component-UU-Level X =
    fundamental-theorem-id
      ( is-torsorial-equiv-component-UU-Level X)
      ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → X ＝ Y
eq-equiv-component-UU-Level X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-component-UU-Level X Y)

equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) → UU l1
equiv-component-UU X Y = equiv-component-UU-Level X Y

id-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) → equiv-component-UU X X
id-equiv-component-UU X = id-equiv-component-UU-Level X

equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} {X Y : component-UU A} →
  X ＝ Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

abstract
  is-torsorial-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    is-torsorial (equiv-component-UU X)
  is-torsorial-equiv-component-UU X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-component-UU :
    {l1 : Level} {A : UU l1} (X Y : component-UU A) →
    is-equiv (equiv-eq-component-UU {X = X} {Y})
  is-equiv-equiv-eq-component-UU X Y =
    is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → X ＝ Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y
```

## Example 17.6.3

Note that type `𝒰_{Fin n}` is the type `BSₙ` of all `n`-element types.
Note also that if `A ≃ B`, then `𝒰_A ≃ 𝒰_B`.

## Definition 17.6.4

Consider two types `A` and `B` and a universe `𝒰` containing both `A` and `B`.
We define the **binomial type** `(A choose B)_𝒰` by

```text
  (A choose B)_𝒰 ≔ Σ(X : 𝒰_B) X ↪ᵈ A.
```

```agda
binomial-type-Level :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level l X Y =
  Σ (component-UU-Level l Y) (λ Z → type-component-UU-Level Z ↪ᵈ X)

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type-Level l3 X Y)
  where

  type-binomial-type-Level : UU l3
  type-binomial-type-Level = type-component-UU-Level (pr1 Z)

  abstract
    mere-compute-binomial-type-Level :
      mere-equiv Y type-binomial-type-Level
    mere-compute-binomial-type-Level = mere-equiv-component-UU-Level (pr1 Z)

  decidable-emb-binomial-type-Level : type-binomial-type-Level ↪ᵈ X
  decidable-emb-binomial-type-Level = pr2 Z

  map-decidable-emb-binomial-type-Level : type-binomial-type-Level → X
  map-decidable-emb-binomial-type-Level =
    map-decidable-emb decidable-emb-binomial-type-Level

  abstract
    is-emb-map-emb-binomial-type-Level :
      is-emb map-decidable-emb-binomial-type-Level
    is-emb-map-emb-binomial-type-Level =
      is-emb-map-decidable-emb decidable-emb-binomial-type-Level

binomial-type : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type {l1} {l2} X Y = binomial-type-Level (l1 ⊔ l2) X Y

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (Z : binomial-type X Y)
  where

  type-binomial-type : UU (l1 ⊔ l2)
  type-binomial-type = type-component-UU-Level (pr1 Z)

  abstract
    mere-compute-binomial-type : mere-equiv Y type-binomial-type
    mere-compute-binomial-type = mere-equiv-component-UU-Level (pr1 Z)

  decidable-emb-binomial-type : type-binomial-type ↪ᵈ X
  decidable-emb-binomial-type = pr2 Z

  map-decidable-emb-binomial-type : type-binomial-type → X
  map-decidable-emb-binomial-type =
    map-decidable-emb decidable-emb-binomial-type

  abstract
    is-emb-map-emb-binomial-type : is-emb map-decidable-emb-binomial-type
    is-emb-map-emb-binomial-type =
      is-emb-map-decidable-emb decidable-emb-binomial-type
```

## Remark 17.6.5

We define the binomial types using decidable embeddings because the usual properties of binomial coefficients generalize most naturally under the extra assumption of decidability.
In particular the binomial theorem for types, which is stated as Exercise 17.14 and generalized in Exercise 18.14, rely on the use of decidable embeddings.

## Proposition 17.6.6

Consider two types `A` and `B`, and a universe `𝒰` containing both `A` and `B`.
Then we have an equivalence

```text
  (A choose B)_𝒰 ≃ Σ(P : A → decidable-Prop_𝒰) ‖B ≃ Σ(a : A) P(a)‖.
```

from the binomial type `(A choose B)_𝒰` to the type of decidable subtypes of `A` that are merely equivalent to `B`.

### Proof

This equivalence follows from Theorem 17.4.2, by which we have

```text
  (Σ(X : 𝒰) X ↪ᵈ A) ≃ (A → decidable-Prop_𝒰). ◻
```

```agda
binomial-type-Level' :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
binomial-type-Level' l A B =
  Σ ( A → Decidable-Prop l)
    ( λ P → mere-equiv B (Σ A (type-Decidable-Prop ∘ P)))

binomial-type' :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc (l1 ⊔ l2))
binomial-type' {l1} {l2} A B = binomial-type-Level' (l1 ⊔ l2) A B

compute-binomial-type-Level :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type-Level (l1 ⊔ l) A B ≃ binomial-type-Level' (l1 ⊔ l) A B
compute-binomial-type-Level l {l1} {l2} A B =
  ( ( ( equiv-Σ
        ( λ P → mere-equiv B (Σ A (type-Decidable-Prop ∘ P)))
        ( equiv-Fiber-Decidable-Prop l A)
        ( λ e →
          equiv-trunc-Prop
            ( equiv-postcomp-equiv
              ( inv-equiv (equiv-total-fiber (pr1 (pr2 e)))) B))) ∘e
      ( inv-associative-Σ)) ∘e
    ( equiv-tot (λ X → commutative-product))) ∘e
  ( associative-Σ)

compute-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ binomial-type' A B
compute-binomial-type {l1} {l2} A B =
  compute-binomial-type-Level (l1 ⊔ l2) A B
```

## Remark 17.6.7

Combining Corollary 17.2.4 and Proposition 17.6.6, we obtain an equivalence

```text
  (A choose B)_𝒰 ≃ Σ(f : A → bool) ‖B ≃ Σ(a : A) f(a) = true‖.
```

for any universe `𝒰` that contains both `A` and `B`.
This equivalence is important, because the right hand side doesn’t depend on the universe `𝒰`.
Therefore we will simply write `(A choose B)` for `(A choose B)_𝒰`, if the universe `𝒰` contains both `A` and `B`.

```agda
small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
small-binomial-type A B =
  Σ (A → bool) (λ f → mere-equiv B (fiber f true))

compute-small-binomial-type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  binomial-type A B ≃ small-binomial-type A B
compute-small-binomial-type A B =
  ( equiv-Σ
    ( λ f → mere-equiv B (fiber f true))
    ( equiv-postcomp A equiv-bool-Decidable-Prop)
    ( λ P →
      equiv-trunc-Prop
        ( equiv-postcomp-equiv
          ( equiv-tot (λ a → compute-equiv-bool-Decidable-Prop (P a)))
          ( B)))) ∘e
  ( compute-binomial-type A B)
```

## Lemma 17.6.8

For any two types `A` and `B`, we have equivalences

```text
          (∅ choose ∅) ≃ 1
      (A + 1 choose ∅) ≃ 1
      (∅ choose B + 1) ≃ ∅
  (A + 1 choose B + 1) ≃ (A choose B) + (A choose B + 1).
```

### Proof

For the first two equivalences, we prove that `(X choose ∅)` is contractible for any type `X`.
To see this, we first note that the type `𝒰_∅` is contractible.
Indeed, at the center of contraction we have the empty type, and any two types that are merely equivalent to the empty type are empty and hence equivalent.
Therefore it follows that

```text
  (X choose ∅) ≃ ∅ ↪ᵈ X.
```

The type of decidable embeddings `∅ ↪ᵈ X` is contractible, because the type `∅ → X` is contractible with the map `ex-falso : ∅ → X` at the center of contraction, which is of course a decidable embedding.

Next, the fact that the binomial type `(∅ choose B + 1)` is empty follows from the fact that the type of maps `X → ∅` is empty for any type `X` merely equivalent to `B + 1`.

For the last equivalence we will use Proposition 17.6.6.
Using the universal property of `A + 1`, we see that

```text
  (A + 1 choose B + 1)
  ≃ Σ(P : A → decidable-Prop_𝒰) Σ(Q : decidable-Prop_𝒰) ‖(B + 1) ≃ Σ(a : A) P(a) + Q‖.
```

Using the fact that `decidable-Prop_𝒰 ≃ Fin 2`, observe that we have an equivalence

```text
  Σ(Q : decidable-Prop_𝒰) ‖(B + 1) ≃ (Σ(a : A) P(a) + Q)‖
  ≃ ‖(B + 1) ≃ (Σ(a : A) P(a) + 1)‖ + ‖(B + 1) ≃ Σ(a : A) P(a)‖.
```

Furthermore, note that it follows from Proposition 16.2.1 that

```text
  ‖(B + 1) ≃ (Σ(a : A) P(a) + 1)‖ ≃ ‖B ≃ Σ(a : A) P(a)‖.
```

Thus we see that

```text
  (A + 1 choose B + 1)
  ≃ ( Σ(P : A → decidable-Prop_𝒰) ‖B ≃ Σ(a : A) P(a)‖)
    + (Σ(P : A → decidable-Prop_𝒰) ‖(B + 1) ≃ Σ(a : A) P(a)‖). ◻
```

```agda
equiv-precomp-decidable-emb-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : UU l3) → (B ↪ᵈ C) ≃ (A ↪ᵈ C)
equiv-precomp-decidable-emb-equiv e C =
  equiv-Σ
    ( is-decidable-emb)
    ( equiv-precomp e C)
    ( λ g →
      equiv-iff-is-prop
        ( is-prop-is-decidable-emb g)
        ( is-prop-is-decidable-emb (g ∘ map-equiv e))
        ( λ H → is-decidable-emb-comp H (is-decidable-emb-is-equiv (pr2 e)))
        ( λ d →
          is-decidable-emb-htpy
            ( λ b → ap g (inv (is-section-map-inv-equiv e b)))
            ( is-decidable-emb-comp
              ( d)
              ( is-decidable-emb-is-equiv (is-equiv-map-inv-equiv e)))))

abstract
  is-contr-component-UU-Level-empty :
    (l : Level) → is-contr (component-UU-Level l empty)
  pr1 (pr1 (is-contr-component-UU-Level-empty l)) = raise-empty l
  pr2 (pr1 (is-contr-component-UU-Level-empty l)) =
    unit-trunc-Prop (compute-raise l empty)
  pr2 (is-contr-component-UU-Level-empty l) X =
    eq-equiv-subuniverse
      ( mere-equiv-Prop empty)
      ( equiv-is-empty
        ( map-inv-equiv (compute-raise l empty))
        ( λ x →
          apply-universal-property-trunc-Prop
          ( pr2 X)
          ( empty-Prop)
          ( λ e → map-inv-equiv e x)))

abstract
  is-contr-component-UU-empty : is-contr (component-UU empty)
  is-contr-component-UU-empty =
    is-contr-component-UU-Level-empty lzero

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-emb-ex-falso : is-emb (ex-falso {A = A})
    is-emb-ex-falso ()

  ex-falso-emb : empty ↪ A
  pr1 ex-falso-emb = ex-falso
  pr2 ex-falso-emb = is-emb-ex-falso

abstract
  is-decidable-map-ex-falso :
    {l : Level} {X : UU l} → is-decidable-map (ex-falso {l} {X})
  is-decidable-map-ex-falso x = inr pr1

abstract
  is-decidable-emb-ex-falso :
    {l : Level} {X : UU l} → is-decidable-emb (ex-falso {l} {X})
  is-decidable-emb-ex-falso = (is-emb-ex-falso , is-decidable-map-ex-falso)

decidable-emb-ex-falso :
  {l : Level} {X : UU l} → empty ↪ᵈ X
decidable-emb-ex-falso = (ex-falso , is-decidable-emb-ex-falso)

decidable-emb-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → A ↪ᵈ B
decidable-emb-is-empty {A = A} f =
  map-equiv
    ( equiv-precomp-decidable-emb-equiv (equiv-is-empty f id) _)
    ( decidable-emb-ex-falso)

abstract
  binomial-type-over-empty :
    {l : Level} {X : UU l} → is-contr (binomial-type X empty)
  binomial-type-over-empty {l} {X} =
    is-contr-equiv
      ( raise-empty l ↪ᵈ X)
      ( left-unit-law-Σ-is-contr
        ( is-contr-component-UU-Level-empty l)
        ( raise-Fin-Type-With-Cardinality-ℕ l zero-ℕ))
      ( is-contr-equiv
        ( empty ↪ᵈ X)
        ( equiv-precomp-decidable-emb-equiv (compute-raise-empty l) X)
        ( is-contr-equiv
          ( is-decidable-emb ex-falso)
          ( left-unit-law-Σ-is-contr (universal-property-empty' X) ex-falso)
          ( is-proof-irrelevant-is-prop
            ( is-prop-is-decidable-emb ex-falso)
            ( is-decidable-emb-ex-falso))))

abstract
  binomial-type-empty-under :
    {l : Level} {X : UU l} →
    type-trunc-Prop X → is-empty (binomial-type empty X)
  binomial-type-empty-under H Y =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ x →
        apply-universal-property-trunc-Prop (pr2 (pr1 Y)) empty-Prop
          ( λ e → map-decidable-emb (pr2 Y) (map-equiv e x)))

abstract
  recursion-binomial-type' :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type' (Maybe A) (Maybe B) ≃
    (binomial-type' A B + binomial-type' A (Maybe B))
  recursion-binomial-type' A B =
    ( ( ( left-distributive-Σ-coproduct) ∘e
        ( equiv-tot
          ( λ P →
            ( ( equiv-coproduct
                ( ( ( equiv-iff
                      ( mere-equiv-Prop (Maybe B) (Maybe (Σ A _)))
                      ( mere-equiv-Prop B (Σ A _))
                      ( map-trunc-Prop (equiv-equiv-Maybe))
                      ( map-trunc-Prop
                        ( λ e → equiv-coproduct e id-equiv))) ∘e
                    ( equiv-trunc-Prop
                      ( equiv-postcomp-equiv
                        ( equiv-coproduct
                          ( id-equiv)
                          ( equiv-is-contr is-contr-raise-unit is-contr-unit))
                        ( Maybe B)))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-torsorial-true-Prop)
                    ( pair (raise-unit-Prop _) raise-star)))
                ( ( equiv-trunc-Prop
                    ( equiv-postcomp-equiv
                      ( right-unit-law-coproduct-is-empty
                        ( Σ A _)
                        ( raise-empty _)
                        ( is-empty-raise-empty))
                      ( Maybe B))) ∘e
                  ( left-unit-law-Σ-is-contr
                    ( is-torsorial-false-Prop)
                    ( pair (raise-empty-Prop _) map-inv-raise)))) ∘e
              ( right-distributive-Σ-coproduct
                ( ind-coproduct _
                  ( λ Q →
                    mere-equiv (Maybe B) ((Σ A _) + (type-Prop (pr1 Q))))
                  ( λ Q →
                    mere-equiv (Maybe B) ((Σ A _) + (type-Prop (pr1 Q))))))) ∘e
            ( equiv-Σ
              ( ind-coproduct _
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( ( Σ A (λ a → type-Decidable-Prop (P a))) +
                      ( type-Prop (pr1 Q))))
                ( λ Q →
                  mere-equiv
                    ( Maybe B)
                    ( ( Σ A (λ a → type-Decidable-Prop (P a))) +
                      ( type-Prop (pr1 Q)))))
              ( split-Decidable-Prop)
              ( ind-Σ
                ( λ Q →
                  ind-Σ
                    ( λ H →
                      ind-coproduct
                        ( _)
                        ( λ q → id-equiv)
                        ( λ q → id-equiv)))))))) ∘e
      ( associative-Σ)) ∘e
    ( equiv-Σ
      ( λ p →
        mere-equiv
          ( Maybe B)
          ( ( Σ A (λ a → type-Decidable-Prop (pr1 p a))) +
            ( type-Decidable-Prop (pr2 p))))
      ( equiv-universal-property-Maybe)
      ( λ u →
        equiv-trunc-Prop
          ( equiv-postcomp-equiv
            ( ( equiv-coproduct
                ( id-equiv)
                ( left-unit-law-Σ (λ y → type-Decidable-Prop (u (inr y))))) ∘e
              ( right-distributive-Σ-coproduct
                ( λ x → type-Decidable-Prop (u x))))
            ( Maybe B))))

abstract
  binomial-type-Maybe :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) →
    binomial-type (Maybe A) (Maybe B) ≃
    (binomial-type A B + binomial-type A (Maybe B))
  binomial-type-Maybe A B =
    ( inv-equiv
      ( equiv-coproduct
        ( compute-binomial-type A B)
        ( compute-binomial-type A (Maybe B))) ∘e
      ( recursion-binomial-type' A B)) ∘e
    ( compute-binomial-type (Maybe A) (Maybe B))
```

## Theorem 17.6.9

If `A` and `B` are finite types of cardinality `n` and `k`, respectively, then the type `(A choose B)` is finite of cardinality `(n choose k)`.

### Proof

The claim that the type `(A choose B)` is finite of cardinality `(n choose k)` is a proposition, so we may assume `e : Fin n ≃ A` and `f : Fin k ≃ B`.
The claim now follows by induction on `n` and `k`, using Lemma 17.6.8. ◻

```agda
equiv-small-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → small-binomial-type A' B' ≃ small-binomial-type A B
equiv-small-binomial-type {l1} {l2} {l3} {l4} {A} {A'} {B} {B'} e f =
  equiv-Σ
    ( λ P → mere-equiv B (fiber P true))
    ( equiv-precomp e bool)
    ( λ P →
      equiv-trunc-Prop
        ( ( equiv-postcomp-equiv
            ( inv-equiv
              ( ( right-unit-law-Σ-is-contr
                  ( λ u →
                    is-contr-map-is-equiv (is-equiv-map-equiv e) (pr1 u))) ∘e
                ( compute-fiber-comp P (map-equiv e) true))) B) ∘e
          ( equiv-precomp-equiv f (fiber P true))))

equiv-binomial-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} →
  (A ≃ A') → (B ≃ B') → binomial-type A' B' ≃ binomial-type A B
equiv-binomial-type e f =
  ( ( inv-equiv (compute-small-binomial-type _ _)) ∘e
    ( equiv-small-binomial-type e f)) ∘e
  ( compute-small-binomial-type _ _)

binomial-type-Fin :
  (n m : ℕ) → binomial-type (Fin n) (Fin m) ≃ Fin (binomial-coefficient-ℕ n m)
binomial-type-Fin zero-ℕ zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-1
binomial-type-Fin zero-ℕ (succ-ℕ m) =
  equiv-is-empty (binomial-type-empty-under (unit-trunc-Prop (inr star))) id
binomial-type-Fin (succ-ℕ n) zero-ℕ =
  equiv-is-contr binomial-type-over-empty is-contr-Fin-1
binomial-type-Fin (succ-ℕ n) (succ-ℕ m) =
  ( ( inv-equiv
      ( inv-compute-coproduct-Fin
        ( binomial-coefficient-ℕ n m)
        ( binomial-coefficient-ℕ n (succ-ℕ m)))) ∘e
    ( equiv-coproduct
      ( binomial-type-Fin n m)
      ( binomial-type-Fin n (succ-ℕ m)))) ∘e
  ( binomial-type-Maybe (Fin n) (Fin m))

has-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (n m : ℕ) →
  has-cardinality-ℕ n A → has-cardinality-ℕ m B →
  has-cardinality-ℕ (binomial-coefficient-ℕ n m) (binomial-type A B)
has-cardinality-binomial-type {A = A} {B} n m H K =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-ℕ-Prop (binomial-coefficient-ℕ n m) (binomial-type A B))
    ( λ e →
      apply-universal-property-trunc-Prop K
        ( has-cardinality-ℕ-Prop
          ( binomial-coefficient-ℕ n m)
          ( binomial-type A B))
        ( λ f →
          unit-trunc-Prop
            ( inv-equiv
              ( binomial-type-Fin n m ∘e equiv-binomial-type e f))))

binomial-type-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (n m : ℕ) →
  Type-With-Cardinality-ℕ l1 n → Type-With-Cardinality-ℕ l2 m →
  Type-With-Cardinality-ℕ (lsuc l1 ⊔ lsuc l2) (binomial-coefficient-ℕ n m)
pr1 (binomial-type-Type-With-Cardinality-ℕ n m A B) =
  binomial-type
    ( type-Type-With-Cardinality-ℕ n A)
    ( type-Type-With-Cardinality-ℕ m B)
pr2 (binomial-type-Type-With-Cardinality-ℕ n m A B) =
  has-cardinality-binomial-type n m
    ( has-cardinality-type-Type-With-Cardinality-ℕ n A)
    ( has-cardinality-type-Type-With-Cardinality-ℕ m B)

has-finite-cardinality-binomial-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-finite-cardinality A → has-finite-cardinality B →
  has-finite-cardinality (binomial-type A B)
pr1 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) =
  binomial-coefficient-ℕ n m
pr2 (has-finite-cardinality-binomial-type (pair n H) (pair m K)) =
  has-cardinality-binomial-type n m H K

abstract
  is-finite-binomial-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (binomial-type A B)
  is-finite-binomial-type H K =
    is-finite-has-finite-cardinality
      ( has-finite-cardinality-binomial-type
        ( has-finite-cardinality-is-finite H)
        ( has-finite-cardinality-is-finite K))

binomial-type-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (binomial-type-Finite-Type A B) =
  small-binomial-type (type-Finite-Type A) (type-Finite-Type B)
pr2 (binomial-type-Finite-Type A B) =
  is-finite-equiv
    ( compute-small-binomial-type (type-Finite-Type A) (type-Finite-Type B))
    ( is-finite-binomial-type
      ( is-finite-type-Finite-Type A)
      ( is-finite-type-Finite-Type B))
```

## Remark 17.6.10

It is perhaps remarkable that the type `Σ(X : 𝒰_B) X ↪ᵈ A` is a good generalisation of the binomial coefficients to types.
Note that when `A` and `B` are finite types of cardinality `n` and `k`, respectively, then the type `B ↪ᵈ A` has a factor `k!` too many elements.
When we seemingly enlarge it by the type `𝒰_B` of all types merely equivalent to `B`, it turns out that we obtain the correct generalisation of the binomial coefficients.

One reason why it works is that the identity type of `Σ(X : 𝒰_B) X ↪ᵈ A` is characterized, via the univalence axiom, by

```text
  ((X,f) = (Y,g)) ≃ Σ(e : X ≃ Y) f ~ g ∘ e.
```

Therefore it follows that for any two decidable embeddings `f, g : B ↪ᵈ A`, if `f` and `g` are the same up to a permutation on `B`, then we get an identification `(B,f) = (B,g)` in the type `Σ(X : 𝒰_B) X ↪ᵈ A`.

From a group theoretic perspective we may observe that the automorphism group `B ≃ B` acts freely on the set of decidable embeddings `B ↪ᵈ A`, and the type `Σ(X : 𝒰_B) X ↪ A` can be viewed as the type of orbits of that action.
Since this action of `Aut(B)` on `B ↪ᵈ A` is free, we see that the number of orbits is `1 / k!` times the number of elements in `B ↪ᵈ A`.
