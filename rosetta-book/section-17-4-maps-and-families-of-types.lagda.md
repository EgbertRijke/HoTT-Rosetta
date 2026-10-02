# Section 17.4 Maps and families of types

```agda
module section-17-4-maps-and-families-of-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import exercise-10-8-fiber-replacement
open import section-11-6-the-structure-identity-principle
open import exercise-13-15-morphisms-over-a-type
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-3-logic-in-type-theory
open import section-15-2-surjective-maps
open import exercise-15-3-equivalences-are-surjective-embeddings
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
```

Using the univalence axiom, we can establish a fundamental relation between maps into a type `A`, and families of types indexed by `A`.
A special case of this relation asserts that the type of all pairs `(X,e)` consisting of a type `X` and an embedding `e : X ↪ A` is equivalent to the type of all subtypes of `A`, i.e., the type of all families `P` of propositions indexed by `A`.

## Theorem 17.4.1

For any type `A` and any univalent universe `𝒰` containing `A`, the map

```text
  (Σ(X : 𝒰) X → A) → (A → 𝒰)
```

given by `(X,f) ↦ fib_f` is an equivalence.

### Proof

The map in the converse direction is given by

```text
  B ↦ (Σ(x : A) B(x), pr1).
```

To verify that this map is a section of the asserted map, we have to prove that

```text
  fib_pr1 = B
```

for any `B : A → 𝒰`.
By function extensionality and the univalence axiom, this is equivalent to

```text
  Π(x : A) fib(pr1,x) ≃ B(x).
```

Such a family of equivalences was constructed in Exercise 10.7.

It remains to verify that

```text
  (X,f) = (Σ(x : A) fib(f,x),pr1).
```

Before we do this, we claim that the identity type

```text
  (X,f) = (Y,g)
```

in the type `Σ(X : 𝒰) X → A` is equivalent to the type of pairs `(e,f)` consisting of an equivalence `e : X ≃ Y` equipped with a homotopy `f ~ g ∘ e`.
This fact follows from Theorem 11.2.2, because the type

```text
  Σ(Y : 𝒰) Σ(g : Y → A) Σ(e : X ≃ Y) f ~ g ∘ e
```

is contractible by the structure identity principle, Theorem 11.6.2.

To finish the proof, it therefore suffices to construct an equivalence

```text
  e : X ≃ Σ(a : A) fib(f,a)
```

equipped with a homotopy `f ~ pr1 ∘ e`.
Such an equivalence `e` equipped with a homotopy was constructed in Exercise 10.8. ◻

```agda
polynomial-endofunctor : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
polynomial-endofunctor l1 l2 = Σ (UU l1) (λ A → (A → UU l2))

module _
  {l1 l2 : Level} (P : polynomial-endofunctor l1 l2)
  where

  shape-polynomial-endofunctor : UU l1
  shape-polynomial-endofunctor = pr1 P

  position-polynomial-endofunctor : shape-polynomial-endofunctor → UU l2
  position-polynomial-endofunctor = pr2 P

type-polynomial-endofunctor' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor' A B X = Σ A (λ x → B x → X)

type-polynomial-endofunctor :
  {l1 l2 l3 : Level} → polynomial-endofunctor l1 l2 → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor (A , B) = type-polynomial-endofunctor' A B

map-polynomial-endofunctor' :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  type-polynomial-endofunctor' A B X → type-polynomial-endofunctor' A B Y
map-polynomial-endofunctor' A B f = tot (λ x α → f ∘ α)

map-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (P : polynomial-endofunctor l1 l2)
  {X : UU l3} {Y : UU l4} (f : X → Y) →
  type-polynomial-endofunctor P X → type-polynomial-endofunctor P Y
map-polynomial-endofunctor (A , B) = map-polynomial-endofunctor' A B

universal-polynomial-endofunctor :
  (l : Level) → polynomial-endofunctor (lsuc l) l
universal-polynomial-endofunctor l = (UU l , id)

Slice : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
Slice l = type-polynomial-endofunctor (universal-polynomial-endofunctor l)

module _
  {l1 l2 : Level} {A : UU l1} (f : Slice l2 A)
  where

  type-Slice : UU l2
  type-Slice = pr1 f

  map-Slice : type-Slice → A
  map-Slice = pr2 f

type-polynomial-endofunctor-UU :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
type-polynomial-endofunctor-UU l = Slice l

map-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-polynomial-endofunctor-UU l A → type-polynomial-endofunctor-UU l B
map-polynomial-endofunctor-UU l =
  map-polynomial-endofunctor (universal-polynomial-endofunctor l)

module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-Slice : (f g : Slice l2 A) → UU (l1 ⊔ l2)
  equiv-Slice f g = equiv-slice (map-Slice f) (map-Slice g)

  id-equiv-Slice : (f : Slice l2 A) → equiv-Slice f f
  id-equiv-Slice f = (id-equiv , refl-htpy)

  equiv-eq-Slice : (f g : Slice l2 A) → f ＝ g → equiv-Slice f g
  equiv-eq-Slice f .f refl = id-equiv-Slice f

module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-torsorial-equiv-Slice : (f : Slice l2 A) → is-torsorial (equiv-Slice f)
    is-torsorial-equiv-Slice (X , f) =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv X)
        ( X , id-equiv)
        ( is-torsorial-htpy f)

  abstract
    is-equiv-equiv-eq-Slice : (f g : Slice l2 A) → is-equiv (equiv-eq-Slice f g)
    is-equiv-equiv-eq-Slice f =
      fundamental-theorem-id
        ( is-torsorial-equiv-Slice f)
        ( equiv-eq-Slice f)

  extensionality-Slice : (f g : Slice l2 A) → (f ＝ g) ≃ equiv-Slice f g
  extensionality-Slice f g = (equiv-eq-Slice f g , is-equiv-equiv-eq-Slice f g)

  eq-equiv-Slice : (f g : Slice l2 A) → equiv-Slice f g → f ＝ g
  eq-equiv-Slice f g = map-inv-equiv (extensionality-Slice f g)

type-exp-UU : (l : Level) {l1 : Level} → UU l1 → UU (lsuc l ⊔ l1)
type-exp-UU l A = A → UU l

map-exp-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-exp-UU l B → type-exp-UU l A
map-exp-UU l f P = P ∘ f

module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  Eq-type-polynomial-endofunctor-UU' :
    type-polynomial-endofunctor-UU l A →
    type-polynomial-endofunctor-UU l A →
    UU (lsuc l ⊔ l1)
  Eq-type-polynomial-endofunctor-UU' (X , f) (Y , g) =
    ( λ a → Σ X (λ x → type-is-small (H (f x) a))) ＝
    ( λ a → Σ Y (λ y → type-is-small (H (g y) a)))

  compute-Eq-type-polynomial-endofunctor-UU' :
    (X Y : type-polynomial-endofunctor-UU l A) →
    (Eq-type-polynomial-endofunctor-UU' X Y) ≃ (X ＝ Y)
  compute-Eq-type-polynomial-endofunctor-UU' (X , f) (Y , g) =
    ( inv-equiv (extensionality-Slice (X , f) (Y , g))) ∘e
    ( inv-equiv (equiv-fam-equiv-equiv-slice f g)) ∘e
    ( equiv-Π-equiv-family
      ( λ a →
        ( equiv-postcomp-equiv
          ( equiv-tot (λ y → inv-equiv-is-small (H (g y) a)))
          ( fiber f a)) ∘e
        ( equiv-precomp-equiv
          ( equiv-tot (λ x → equiv-is-small (H (f x) a)))
          ( Σ Y (λ y → type-is-small (H (g y) a)))) ∘e
        ( equiv-univalence))) ∘e
    ( equiv-funext)

  compute-total-Eq-type-polynomial-endofunctor-UU' :
    (X : type-polynomial-endofunctor-UU l A) →
    Σ ( type-polynomial-endofunctor-UU l A)
      ( Eq-type-polynomial-endofunctor-UU' X) ≃
    Σ (type-polynomial-endofunctor-UU l A) (X ＝_)
  compute-total-Eq-type-polynomial-endofunctor-UU' X =
    equiv-tot (compute-Eq-type-polynomial-endofunctor-UU' X)

  abstract
    is-torsorial-Eq-type-polynomial-endofunctor-UU' :
      (X : type-polynomial-endofunctor-UU l A) →
      is-torsorial (Eq-type-polynomial-endofunctor-UU' X)
    is-torsorial-Eq-type-polynomial-endofunctor-UU' X =
      is-contr-equiv
        ( Σ ( type-polynomial-endofunctor-UU l A) (X ＝_))
        ( compute-total-Eq-type-polynomial-endofunctor-UU' X)
        ( is-torsorial-Id X)

module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  map-type-duality :
    type-polynomial-endofunctor-UU l A → type-exp-UU l A
  map-type-duality (X , f) a =
    Σ X (λ x → type-is-small (H (f x) a))

  abstract
    is-emb-map-type-duality : is-emb map-type-duality
    is-emb-map-type-duality (X , f) =
      fundamental-theorem-id
        ( is-torsorial-Eq-type-polynomial-endofunctor-UU' H (X , f))
        ( λ Y → ap map-type-duality)

  emb-type-duality :
    type-polynomial-endofunctor-UU l A ↪ type-exp-UU l A
  emb-type-duality = (map-type-duality , is-emb-map-type-duality)

module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  map-inv-type-duality :
    type-exp-UU l A → type-polynomial-endofunctor-UU l A
  pr1 (map-inv-type-duality B) =
    type-is-small (is-small-Σ H (λ a → is-small' {l} {B a}))
  pr2 (map-inv-type-duality B) =
    ( pr1) ∘
    ( map-inv-equiv-is-small (is-small-Σ H (λ a → is-small' {l} {B a})))

  compute-map-type-duality :
    (B : type-exp-UU l A) (a : A) →
    map-type-duality
      ( is-locally-small-is-small H)
      ( map-inv-type-duality B)
      ( a) ≃
    B a
  compute-map-type-duality B a =
    equivalence-reasoning
      map-type-duality
        ( is-locally-small-is-small H)
        ( map-inv-type-duality B)
        ( a)
      ≃ fiber
          ( pr1 ∘ map-inv-equiv-is-small (is-small-Σ H (λ a → is-small')))
          ( a)
        by
        equiv-tot
          ( λ x →
            inv-equiv-is-small
              ( is-locally-small-is-small H
                ( pr2 (map-inv-type-duality B) x)
                ( a)))
      ≃ Σ ( fiber pr1 a)
          ( λ b →
            fiber
              ( map-inv-equiv-is-small
                ( is-small-Σ H (λ a → is-small' {l} {B a})))
              ( pr1 b))
        by compute-fiber-comp pr1 _ a
      ≃ fiber pr1 a
        by
        right-unit-law-Σ-is-contr
          ( λ b →
            is-contr-map-is-equiv
              ( is-equiv-map-inv-equiv-is-small
                ( is-small-Σ H (λ a → is-small' {l} {B a})))
              ( pr1 b))
      ≃ B a
        by equiv-fiber-pr1 B a

  abstract
    is-section-map-inv-type-duality :
      is-section
        ( map-type-duality (is-locally-small-is-small H))
        ( map-inv-type-duality)
    is-section-map-inv-type-duality B =
      eq-equiv-fam (compute-map-type-duality B)

  is-retraction-map-inv-type-duality :
    is-retraction
      ( map-type-duality (is-locally-small-is-small H))
      ( map-inv-type-duality)
  is-retraction-map-inv-type-duality X =
    is-injective-is-emb
      ( is-emb-map-type-duality (is-locally-small-is-small H))
      ( is-section-map-inv-type-duality
        ( map-type-duality (is-locally-small-is-small H) X))

  is-equiv-map-type-duality :
    is-equiv (map-type-duality (is-locally-small-is-small H))
  is-equiv-map-type-duality =
    is-equiv-is-invertible
      map-inv-type-duality
      is-section-map-inv-type-duality
      is-retraction-map-inv-type-duality

  type-duality : type-polynomial-endofunctor-UU l A ≃ type-exp-UU l A
  pr1 type-duality = map-type-duality (is-locally-small-is-small H)
  pr2 type-duality = is-equiv-map-type-duality

module _
  {l l1 : Level} {A : UU l1}
  (H : is-locally-small l A)
  (E : is-equiv (map-type-duality H))
  where

  type-is-small-is-equiv-map-type-duality : UU l
  type-is-small-is-equiv-map-type-duality =
    pr1 (map-inv-is-equiv E (λ _ → raise-unit l))

  map-inv-equiv-is-small-is-equiv-map-type-duality :
    type-is-small-is-equiv-map-type-duality → A
  map-inv-equiv-is-small-is-equiv-map-type-duality =
    pr2 (map-inv-is-equiv E (λ _ → raise-unit l))

  abstract
    is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality :
      is-contr-map map-inv-equiv-is-small-is-equiv-map-type-duality
    is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality a =
      is-contr-equiv
        ( raise-unit l)
        ( ( equiv-eq-fam _ _
            ( is-section-map-inv-is-equiv E (λ _ → raise-unit l))
            ( a)) ∘e
          ( equiv-tot
            ( λ x →
              equiv-is-small
                ( H (pr2 (map-inv-is-equiv E (λ _ → raise-unit l)) x) a))))
        ( is-contr-raise-unit)

  abstract
    is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality :
      is-equiv map-inv-equiv-is-small-is-equiv-map-type-duality
    is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality =
      is-equiv-is-contr-map
        is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality

  inv-equiv-is-small-is-equiv-map-type-duality :
    type-is-small-is-equiv-map-type-duality ≃ A
  inv-equiv-is-small-is-equiv-map-type-duality =
    ( map-inv-equiv-is-small-is-equiv-map-type-duality ,
      is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality)

  equiv-is-small-is-equiv-map-type-duality :
    A ≃ type-is-small-is-equiv-map-type-duality
  equiv-is-small-is-equiv-map-type-duality =
    inv-equiv inv-equiv-is-small-is-equiv-map-type-duality

  is-small-is-equiv-map-type-duality : is-small l A
  is-small-is-equiv-map-type-duality =
    ( type-is-small-is-equiv-map-type-duality ,
      equiv-is-small-is-equiv-map-type-duality)

module _
  {l l1 : Level} {A : UU l1}
  (H : is-locally-small l A)
  (E : is-surjective (map-type-duality H))
  where

  is-small-is-surjective-map-type-duality : is-small l A
  is-small-is-surjective-map-type-duality =
    is-small-is-equiv-map-type-duality H
      ( is-equiv-is-emb-is-surjective E (is-emb-map-type-duality H))

Fiber : {l l1 : Level} (A : UU l1) → Slice l A → A → UU (l1 ⊔ l)
Fiber A f = fiber (pr2 f)

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → Slice (l1 ⊔ l) A
pr1 (Pr1 A B) = Σ A B
pr2 (Pr1 A B) = pr1

is-section-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Fiber {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
is-section-Pr1 B = eq-equiv-fam (equiv-fiber-pr1 B)

is-retraction-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fiber {l1 ⊔ l2} A) ~ id
is-retraction-Pr1 {A = A} (X , f) =
  eq-equiv-Slice
    ( Pr1 A (Fiber A (X , f)))
    ( X , f)
    ( equiv-total-fiber f , triangle-map-equiv-total-fiber f)

is-equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fiber {l1 ⊔ l2} A)
is-equiv-Fiber l2 A =
  is-equiv-is-invertible
    ( Pr1 A)
    ( is-section-Pr1 {l2 = l2})
    ( is-retraction-Pr1 {l2 = l2})

equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → Slice (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
pr1 (equiv-Fiber l2 A) = Fiber A
pr2 (equiv-Fiber l2 A) = is-equiv-Fiber l2 A

is-equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
is-equiv-Pr1 {l1} l2 A =
  is-equiv-is-invertible
    ( Fiber A)
    ( is-retraction-Pr1 {l2 = l2})
    ( is-section-Pr1 {l2 = l2})

equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → (A → UU (l1 ⊔ l2)) ≃ Slice (l1 ⊔ l2) A
pr1 (equiv-Pr1 l2 A) = Pr1 A
pr2 (equiv-Pr1 l2 A) = is-equiv-Pr1 l2 A

fiber-Σ :
  {l1 l2 : Level} (X : UU l1) (A : UU l2) →
  (X → A) ≃ Σ (A → UU (l1 ⊔ l2)) (λ Y → X ≃ Σ A Y)
fiber-Σ {l1} {l2} X A =
  ( equiv-Σ
    ( λ Z → X ≃ Σ A Z)
    ( equiv-Fiber l1 A)
    ( λ s → equiv-postcomp-equiv (inv-equiv-total-fiber (pr2 s)) X)) ∘e
  ( equiv-right-swap-Σ) ∘e
  ( inv-left-unit-law-Σ-is-contr
    ( is-contr-is-small-lmax l2 X)
    ( is-small-lmax l2 X)) ∘e
  ( equiv-precomp (inv-equiv-is-small (is-small-lmax l2 X)) A)
```

The following corollary is so important, that we call it again a theorem.

## Theorem 17.4.2

Consider a type `A` and a univalent universe `𝒰` containing `A`.
Furthermore, let `P` be a family of types indexed by `𝒰`, and write

```text
  𝒰_P ≔ Σ(X : 𝒰) P(X).
```

Then the map

```text
  (Σ(X : 𝒰) Σ(f : X → A) Π(a : A) P(fib(f,a))) → (A → 𝒰_P)
```

given by `(X,f,p) ↦ λ a. (fib(f,a),p(a))` is an equivalence.

### Proof

The asserted map is homotopic to the composition of the equivalences

```text
  Σ(X : 𝒰) Σ(f : X → A) Π(a : A) P(fib(f,a))
  ≃ Σ((X,f) : Σ(X : 𝒰) X → A) Π(a : A) P(fib(f,a))
  ≃ Σ(B : A → 𝒰) Π(a : A) P(B(a))
  ≃ A → Σ(X : 𝒰) P(X). ◻
```

```agda
structure : {l1 l2 : Level} (𝒫 : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
structure {l1} 𝒫 = Σ (UU l1) 𝒫

structure-family :
  {l1 l2 l3 : Level} (𝒫 : UU l1 → UU l2) {A : UU l3} →
  (A → UU l1) → UU (l2 ⊔ l3)
structure-family 𝒫 {A} B = (x : A) → 𝒫 (B x)

structured-family :
  {l1 l2 l3 : Level} (𝒫 : UU l1 → UU l2) → UU l3 → UU (lsuc l1 ⊔ l2 ⊔ l3)
structured-family 𝒫 A = A → structure 𝒫

structure-map :
  {l1 l2 l3 : Level} (𝒫 : UU (l1 ⊔ l2) → UU l3) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l2 ⊔ l3)
structure-map 𝒫 {A} {B} f = structure-family 𝒫 (fiber f)

structured-map :
  {l1 l2 l3 : Level}
  (𝒫 : UU (l1 ⊔ l2) → UU l3)
  (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ l3)
structured-map 𝒫 A B = Σ (A → B) (structure-map 𝒫)

hom-structure :
  {l1 l2 l3 : Level} (𝒫 : UU (l1 ⊔ l2) → UU l3) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ l3)
hom-structure 𝒫 A B = Σ (A → B) (structure-map 𝒫)

structure-equality :
  {l1 l2 : Level} (𝒫 : UU l1 → UU l2) → UU l1 → UU (l1 ⊔ l2)
structure-equality 𝒫 A = (x y : A) → 𝒫 (x ＝ y)

Slice-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
Slice-structure l P B = Σ (UU l) (λ A → hom-structure P A B)

equiv-Fiber-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  Slice-structure (l1 ⊔ l) P B ≃ structured-family P B
equiv-Fiber-structure {l1} {l3} l P B =
  ( ( inv-distributive-Π-Σ) ∘e
    ( equiv-Σ
      ( λ C → (b : B) → P (C b))
      ( equiv-Fiber l B)
      ( λ f → equiv-Π-equiv-family (λ b → id-equiv)))) ∘e
  ( inv-associative-Σ)

equiv-fixed-Slice-structure :
  {l : Level} (P : UU l → UU l) (X : UU l) (A : UU l) →
  ( hom-structure P X A) ≃
  ( Σ (A → Σ (UU l) (λ Z → P (Z))) ( λ Y → X ≃ (Σ A (pr1 ∘ Y))))
equiv-fixed-Slice-structure {l} P X A =
  ( ( equiv-Σ
      ( λ Y → X ≃ Σ A (pr1 ∘ Y))
      ( equiv-Fiber-structure l P A)
      ( λ s →
        inv-equiv
          ( equiv-postcomp-equiv (equiv-total-fiber (pr1 (pr2 s))) X))) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( ( inv-left-unit-law-Σ-is-contr
          ( is-torsorial-equiv X)
          ( X , id-equiv)))))
```

Theorem 17.4.2 applies to any subuniverse.
Examples include the subuniverse of `k`-types, for any truncation level `k`, the subuniverse of decidable propositions, the subuniverse of finite types, the subuniverse of inhabited types, and so on.
It also applies to type families over `𝒰` that aren’t families of propositions.
The families `P ≔ is-decidable` and `P ≔ count` are examples.

## Corollary 17.4.3

Consider a type `A` and a univalent universe `𝒰` containing `A`.
Then the map

```text
  (Σ(X : 𝒰) X ↪ A) → (A → Prop_𝒰)
```

given by `(X,f) ↦ fib_f` is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-prop-map : (f : A → B) → is-prop (is-prop-map f)
  is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

  is-prop-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-prop-map-Prop f) = is-prop-map f
  pr2 (is-prop-map-Prop f) = is-prop-is-prop-map f

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-emb-is-prop-map : (f : A → B) → is-prop-map f ≃ is-emb f
  equiv-is-emb-is-prop-map f =
    equiv-iff
      ( is-prop-map-Prop f)
      ( is-emb-Prop f)
      ( is-emb-is-prop-map)
      ( is-prop-map-is-emb)

  equiv-is-prop-map-is-emb : (f : A → B) → is-emb f ≃ is-prop-map f
  equiv-is-prop-map-is-emb f =
    equiv-iff
      ( is-emb-Prop f)
      ( is-prop-map-Prop f)
      ( is-prop-map-is-emb)
      ( is-emb-is-prop-map)

Slice-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-emb l A = Σ (UU l) (λ X → X ↪ A)

equiv-Fiber-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-emb (l1 ⊔ l) A ≃ (A → Prop (l1 ⊔ l))
equiv-Fiber-Prop l A =
  ( equiv-Fiber-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))
```

In other words, a subtype of a type `A` is equivalently described as a type `X` equipped with an embedding `e : X ↪ A`.
This brings us to an important point about equality of subtypes.

## Remark 17.4.4

By function extensionality and propositional extensionality, it follows that two subtypes `P, Q : A → Prop_𝒰` are the same if and only if

```text
  P(a) ↔ Q(a)
```

holds for all `a : A`.
In other words, two subtypes of `A` are the same if and only if they contain the same elements of `A`.

On the other hand, by Corollary 17.4.3 we can also consider two types `X` and `Y` equipped with embeddings `f : X ↪ A` and `g : Y ↪ A` as subtypes of `A`.
Using the structure identity principle, Theorem 11.6.2, we see that the identity type `(X,f) = (Y,g)` in the type `Σ(X : 𝒰) X ↪ A` is equivalent to the type

```text
  Σ(e : X ≃ Y) f ~ g ∘ e.
```

In other words, two subtypes `(X,f)` and `(Y,g)` of `A` are equal if and only if there is an equivalence `X ≃ Y` that is compatible with the embeddings `f : X ↪ A` and `g : Y ↪ X`.
Indeed, this condition is equivalent to the previous condition that two subtypes are the same if and only if they have the same elements.

We see that the combination of the structure identity principle and the univalence axiom automatically characterizes equality of subtypes in the most natural way, and we will see similar natural characterizations of identity types throughout the remainder of this book.

```agda
Subtype : {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Subtype l2 l3 A =
  Σ ( A → Prop l2)
    ( λ P →
      Σ ( Σ (UU l3) (λ X → X ↪ A))
        ( λ i →
          Σ ( pr1 i ≃ Σ A (type-Prop ∘ P))
            ( λ e → map-emb (pr2 i) ~ (pr1 ∘ map-equiv e))))

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  has-same-elements-subtype-Prop :
    {l3 : Level} → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype-Prop Q =
    Π-Prop A (λ x → iff-Prop (P x) (Q x))

  has-same-elements-subtype : {l3 : Level} → subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype Q = type-Prop (has-same-elements-subtype-Prop Q)

  is-prop-has-same-elements-subtype :
    {l3 : Level} (Q : subtype l3 A) →
    is-prop (has-same-elements-subtype Q)
  is-prop-has-same-elements-subtype Q =
    is-prop-type-Prop (has-same-elements-subtype-Prop Q)

  refl-has-same-elements-subtype : has-same-elements-subtype P
  pr1 (refl-has-same-elements-subtype x) = id
  pr2 (refl-has-same-elements-subtype x) = id

  is-torsorial-has-same-elements-subtype :
    is-torsorial has-same-elements-subtype
  is-torsorial-has-same-elements-subtype =
    is-torsorial-Eq-Π (λ x → is-torsorial-iff (P x))

  has-same-elements-eq-subtype :
    (Q : subtype l2 A) → (P ＝ Q) → has-same-elements-subtype Q
  has-same-elements-eq-subtype .P refl =
    refl-has-same-elements-subtype

  is-equiv-has-same-elements-eq-subtype :
    (Q : subtype l2 A) → is-equiv (has-same-elements-eq-subtype Q)
  is-equiv-has-same-elements-eq-subtype =
    fundamental-theorem-id
      is-torsorial-has-same-elements-subtype
      has-same-elements-eq-subtype

  extensionality-subtype :
    (Q : subtype l2 A) → (P ＝ Q) ≃ has-same-elements-subtype Q
  pr1 (extensionality-subtype Q) = has-same-elements-eq-subtype Q
  pr2 (extensionality-subtype Q) = is-equiv-has-same-elements-eq-subtype Q

  eq-has-same-elements-subtype :
    (Q : subtype l2 A) → has-same-elements-subtype Q → P ＝ Q
  eq-has-same-elements-subtype Q =
    map-inv-equiv (extensionality-subtype Q)

module _
  {l1 l2 l3 : Level} {X : UU l1} (S : subtype l2 X) (T : subtype l3 X)
  where

  equiv-has-same-elements-type-subtype :
    has-same-elements-subtype S T → type-subtype S ≃ type-subtype T
  equiv-has-same-elements-type-subtype H =
    equiv-tot (λ x → equiv-iff' (S x) (T x) (H x))

module _
  {l1 : Level} {A : UU l1}
  where

  leq-prop-subtype :
    {l2 l3 : Level} → subtype l2 A → subtype l3 A → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-subtype P Q =
    Π-Prop A (λ x → hom-Prop (P x) (Q x))

  infix 5 _⊆_
  _⊆_ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  P ⊆ Q = type-Prop (leq-prop-subtype P Q)

  is-prop-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → is-prop (P ⊆ Q)
  is-prop-leq-subtype P Q =
    is-prop-type-Prop (leq-prop-subtype P Q)

module _
  {l1 : Level} {A : UU l1}
  where

  equiv-antisymmetric-leq-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → P ⊆ Q → Q ⊆ P →
    (x : A) → is-in-subtype P x ≃ is-in-subtype Q x
  equiv-antisymmetric-leq-subtype P Q H K x =
    equiv-iff-is-prop
      ( is-prop-is-in-subtype P x)
      ( is-prop-is-in-subtype Q x)
      ( H x)
      ( K x)

  antisymmetric-leq-subtype :
    {l2 : Level} (P Q : subtype l2 A) → P ⊆ Q → Q ⊆ P → P ＝ Q
  antisymmetric-leq-subtype P Q H K =
    eq-has-same-elements-subtype P Q (λ x → (H x , K x))

is-set-subtype :
  {l1 l2 : Level} {A : UU l1} → is-set (subtype l2 A)
is-set-subtype P Q =
  is-prop-equiv
    ( extensionality-subtype P Q)
    ( is-prop-has-same-elements-subtype P Q)

subtype-Set : {l1 : Level} (l2 : Level) → UU l1 → Set (l1 ⊔ lsuc l2)
pr1 (subtype-Set l2 A) = subtype l2 A
pr2 (subtype-Set l2 A) = is-set-subtype
```

