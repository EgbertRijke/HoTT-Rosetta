# Section 18.5 Set truncations

```agda
module section-18-5-set-truncations where

open import universe-levels
open import section-2-2-ordinary-function-types
open import exercise-2-3-constant-maps
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-7-3-the-standard-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-1-identity-types-contractible
open import exercise-10-3-contractible-equivalences
open import exercise-10-7-fibers-of-projections
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-6-truncated-sigma-types
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-3-universal-properties
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-7-universal-property-contractible-types
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
open import section-16-3-finite-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-17-5-classical-mathematics-with-the-univalence-axiom
open import section-18-1-equivalence-relations-and-the-replacement-axiom
open import section-18-2-the-universal-property-of-set-quotients
```

An important instance of set quotients in the univalent foundations of mathematics is the notion of set truncation.
Analogous to the propositional truncation, the set truncation of a type `A` is a map `η : A → ‖A‖₀` into a set `‖A‖₀` such that any map `f : A → X` into a set `X` extends uniquely along `η`:

```text
    A
    | \
    |  \
  η |   \ f
    |    \
    |     \
    |      \
    ∨       ∨
  ‖A‖₀ - -> X
```

In other words, the set truncation `η : A → ‖A‖₀` is the universal way of mapping `A` into a set.
We first specify what it means for a map `f : A → B` into a set `B` to be a set truncation of `A`.

## Definition 18.5.1

We say that a map `f : A → B` into a set `B` is a **set truncation** if the precomposition function

```text
  - ∘ f : (B → X) → (A → X)
```

is an equivalence for every set `X`.

```agda
is-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) → (A → type-Set B) → UUω
is-set-truncation B f =
  {l : Level} (C : Set l) → is-equiv (precomp-Set f C)
```

In the following theorem we prove several conditions that are equivalent to being a set truncation.

## Theorem 18.5.2

Consider a map `f : A → B` into a set `B`.
Then the following are equivalent:

1. The map `f` is a set truncation.

2. The map `f` satisfies the **dependent universal property** of the set truncation: For every family `X` of sets over `B`, the precomposition function

   ```text
     - ∘ f : (Π(b : B) X(b)) → (Π(a : A) X(f(a)))
   ```

   is an equivalence.

3. The map `f` is surjective and effective with respect to the equivalence relation `x, y ↦ ‖x = y‖`, i.e., we have equivalences

   ```text
     (f(x) = f(y)) ≃ ‖x = y‖
   ```

   for every `x, y : A`.

### Proof

The fact that (2) implies (1) is immediate.
Moreover, the fact that (1) is equivalent to (3) follows from the fact that any map `h : A → X` into a set `X` comes equipped with a function

```text
  ‖x = y‖ → (h(x) = h(y))
```

for every `x, y : A`.

It remains to prove that (1) implies (2).
Consider a family `X` of sets over `B`, and consider the commuting square

```text
                         (g,s) ↦ (g ∘ f, s ∘ f)

  Σ(g : B → B) Π(b : B) X(g(b)) ----> Σ(h : A → B) Π(a : A) X(h(a))
            |                              |
          ≃ |                              | ≃
            ∨                              ∨
    (B → Σ(b : B) X(b)) ------------> (A → Σ(b : B) X(b))
                           - ∘ f
```

The side maps are equivalences by the distributivity of `Π` over `Σ`, and the bottom map is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows that the top map is an equivalence.
Furthermore, note that the map

```text
  - ∘ f : (B → B) → (A → B)
```

is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows from Theorem 11.1.6 that the map

```text
  - ∘ f : (Π(b : B) X(g(b))) → (Π(a : A) X(g(f(a))))
```

is an equivalence for every `g : B → B`.
Now we take `g ≔ id` to complete the proof that (1) implies (2). ◻

```agda
universal-property-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) → UUω
universal-property-set-truncation {A = A} B f =
  {l : Level} (C : Set l) (g : A → type-Set C) →
  is-contr (Σ (hom-Set B C) (λ h → h ∘ f ~ g))

precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) → UUω
dependent-universal-property-set-truncation B f =
  {l : Level} (X : type-Set B → Set l) → is-equiv (precomp-Π-Set f X)

abstract
  is-set-truncation-universal-property :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    universal-property-set-truncation B f →
    is-set-truncation B f
  is-set-truncation-universal-property B f up-f C =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv
          ( Σ (hom-Set B C) (λ h → h ∘ f ~ g))
          ( equiv-tot (λ h → equiv-funext))
          ( up-f C g))

abstract
  universal-property-is-set-truncation :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f → universal-property-set-truncation B f
  universal-property-is-set-truncation B f is-settr-f C g =
    is-contr-equiv'
      ( Σ (hom-Set B C) (λ h → (h ∘ f) ＝ g))
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (is-settr-f C) g)

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-set-truncation B f → (C : Set l3) (g : A → type-Set C) → hom-Set B C
map-is-set-truncation B f is-settr-f C g =
  pr1 (center (universal-property-is-set-truncation B f is-settr-f C g))

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  (is-settr-f : is-set-truncation B f) →
  (C : Set l3) (g : A → type-Set C) →
  map-is-set-truncation B f is-settr-f C g ∘ f ~ g
triangle-is-set-truncation B f is-settr-f C g =
  pr2 (center (universal-property-is-set-truncation B f is-settr-f C g))

abstract
  dependent-universal-property-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f →
    dependent-universal-property-set-truncation B f
  dependent-universal-property-is-set-truncation {A = A} B f H X =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (h : A → type-Set B) → (a : A) → type-Set (X (h a)))
      ( λ (g : type-Set B → type-Set B) → g ∘ f)
      ( λ g (s : (b : type-Set B) → type-Set (X (g b))) (a : A) → s (f a))
      ( H B)
      ( is-equiv-equiv
        ( inv-distributive-Π-Σ)
        ( inv-distributive-Π-Σ)
        ( ind-Σ (λ g s → refl))
        ( H (Σ-Set B X)))
      ( id)

abstract
  is-set-truncation-dependent-universal-property :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    dependent-universal-property-set-truncation B f →
    is-set-truncation B f
  is-set-truncation-dependent-universal-property B f H X =
    H (λ b → X)

abstract
  is-set-truncation-is-set-quotient :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f) →
    is-set-truncation B f
  is-set-truncation-is-set-quotient {A = A} B f H X =
    is-equiv-comp
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( H X)
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-equivalence-relation
              ( mere-eq-equivalence-relation A) X h)
            ( reflects-mere-eq X h)))

abstract
  is-set-quotient-is-set-truncation :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f)
  is-set-quotient-is-set-truncation {A = A} B f H X =
    is-equiv-right-factor
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-equivalence-relation
              ( mere-eq-equivalence-relation A) X h)
            ( reflects-mere-eq X h)))
      ( H X)
```

## Corollary 18.5.3

On any universe `𝒰`, there is an operation `‖_‖₀ : 𝒰 → Set_𝒰` such that every type `A` in `𝒰` comes equipped with a map

```text
  η : A → ‖A‖₀
```

that satisfies the universal property of the set truncation.
The set `‖A‖₀` is called the **set truncation** of `A`.

### Proof

By Theorem 18.5.2 it follows that a map `f : A → B` into a set `B` is a set truncation if and only if it is a quotient map with respect to the equivalence relation `x, y ↦ ‖x = y‖`.
Given a type `A` in `𝒰`, the quotient of `A` by `x, y ↦ ‖x = y‖` is equivalent to a type in `𝒰` by the replacement axiom. ◻

```agda
trunc-Set : {l : Level} → UU l → Set l
trunc-Set = trunc zero-𝕋

type-trunc-Set : {l : Level} → UU l → UU l
type-trunc-Set = type-trunc zero-𝕋

is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)
is-set-type-trunc-Set = is-trunc-type-trunc

unit-trunc-Set : {l : Level} {A : UU l} → A → type-trunc-Set A
unit-trunc-Set = unit-trunc

unit-trunc-Set' : {l : Level} (A : UU l) → A → type-trunc-Set A
unit-trunc-Set' A = unit-trunc-Set

is-set-truncation-trunc-Set :
  {l1 : Level} (A : UU l1) → is-set-truncation (trunc-Set A) unit-trunc-Set
is-set-truncation-trunc-Set A = is-truncation-trunc

║_║₀ : {l : Level} → UU l → UU l
║_║₀ = type-trunc-Set

dependent-universal-property-trunc-Set :
  {l1 : Level} {A : UU l1} →
  dependent-universal-property-set-truncation (trunc-Set A) unit-trunc-Set
dependent-universal-property-trunc-Set = dependent-universal-property-trunc

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set =
  equiv-dependent-universal-property-trunc

module _
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2)
  (f : (x : A) → type-Set (B (unit-trunc-Set x)))
  where

  Π-trunc-Set : UU (l1 ⊔ l2)
  Π-trunc-Set =
    Σ ( (x : type-trunc-Set A) → type-Set (B x))
      ( λ g → g ∘ unit-trunc-Set ~ f)

  function-dependent-universal-property-trunc-Set :
    (x : type-trunc-Set A) → type-Set (B x)
  function-dependent-universal-property-trunc-Set =
    function-dependent-universal-property-trunc B f

  compute-dependent-universal-property-trunc-Set :
    function-dependent-universal-property-trunc-Set ∘ unit-trunc-Set ~ f
  compute-dependent-universal-property-trunc-Set =
    htpy-dependent-universal-property-trunc B f

  apply-dependent-universal-property-trunc-Set' :
    (x : type-trunc-Set A) → type-Set (B x)
  apply-dependent-universal-property-trunc-Set' =
    map-inv-equiv (equiv-dependent-universal-property-trunc-Set B) f
```

## Corollary 18.5.4

The set truncation `η : A → ‖A‖₀` is surjective and effective with respect to the equivalence relation `x, y ↦ ‖x = y‖`, i.e., we have an equivalence

```text
  (η(x) = η(y)) ≃ ‖x = y‖
```

for each `x, y : A`.

```agda
reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-equivalence-relation
    ( mere-eq-equivalence-relation A)
    ( type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

abstract
  is-set-quotient-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( reflecting-map-mere-eq-unit-trunc-Set A)
  is-set-quotient-trunc-Set A =
    is-set-quotient-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

module _
  {l : Level}
  where

  abstract
    is-surjective-and-effective-unit-trunc-Set :
      (A : UU l) →
      is-surjective-and-effective
        ( mere-eq-equivalence-relation A)
        ( unit-trunc-Set)
    is-surjective-and-effective-unit-trunc-Set A =
      is-surjective-and-effective-is-set-quotient
        ( mere-eq-equivalence-relation A)
        ( trunc-Set A)
        ( unit-trunc-Set ,
          reflects-mere-eq (trunc-Set A) unit-trunc-Set)
        ( λ {l} → is-set-quotient-trunc-Set A)

  abstract
    is-surjective-unit-trunc-Set :
      (A : UU l) → is-surjective (unit-trunc-Set {A = A})
    is-surjective-unit-trunc-Set A =
      pr1 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    is-effective-unit-trunc-Set :
      (A : UU l) →
      is-effective (mere-eq-equivalence-relation A) (unit-trunc-Set {A = A})
    is-effective-unit-trunc-Set A =
      pr2 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    apply-effectiveness-unit-trunc-Set :
      {A : UU l} {x y : A} → unit-trunc-Set x ＝ unit-trunc-Set y → mere-eq x y
    apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
      map-equiv (is-effective-unit-trunc-Set A x y)

  abstract
    apply-effectiveness-unit-trunc-Set' :
      {A : UU l} {x y : A} → mere-eq x y → unit-trunc-Set x ＝ unit-trunc-Set y
    apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
      map-inv-equiv (is-effective-unit-trunc-Set A x y)
```

By this corollary, we may think of the set truncation `‖A‖₀` of `A` as the set of connected components of `A`.
Indeed, if we have an unspecified identification `‖x = y‖` in `A`, then we think of `x` and `y` as being in the same connected component.
For example, any `k`-element set is a type that is in the same connected component of `𝒰` as the type `Fin k`.

## Definition 18.5.5

A type `A` is said to be **connected** if its set truncation `‖A‖₀` is contractible.
We define

```text
  is-conn(A) ≔ is-contr ‖A‖₀.
```

Furthermore, we say that a map `f : A → B` is **connected** if all its fibers are connected.

```agda
is-0-connected-Prop : {l : Level} → UU l → Prop l
is-0-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-0-connected : {l : Level} → UU l → UU l
is-0-connected A = type-Prop (is-0-connected-Prop A)

is-prop-is-0-connected : {l : Level} (A : UU l) → is-prop (is-0-connected A)
is-prop-is-0-connected A = is-prop-type-Prop (is-0-connected-Prop A)

module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  is-connected-Prop : Prop l
  is-connected-Prop = is-contr-Prop (type-trunc k A)

  is-connected : UU l
  is-connected = type-Prop is-connected-Prop

  is-prop-is-connected : is-prop is-connected
  is-prop-is-connected = is-prop-type-Prop is-connected-Prop

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-Prop : Prop (l1 ⊔ l2)
  is-connected-map-Prop =
    Π-Prop B (λ b → is-connected-Prop k (fiber f b))

  is-connected-map : UU (l1 ⊔ l2)
  is-connected-map = type-Prop is-connected-map-Prop

  is-prop-is-connected-map : is-prop is-connected-map
  is-prop-is-connected-map = is-prop-type-Prop is-connected-map-Prop

connected-map : {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
connected-map k A B = type-subtype (is-connected-map-Prop k {A} {B})

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-connected-map : connected-map k A B → A → B
  map-connected-map = inclusion-subtype (is-connected-map-Prop k)

  is-connected-map-connected-map :
    (f : connected-map k A B) → is-connected-map k (map-connected-map f)
  is-connected-map-connected-map =
    is-in-subtype-inclusion-subtype (is-connected-map-Prop k)

  emb-inclusion-connected-map : connected-map k A B ↪ (A → B)
  emb-inclusion-connected-map = emb-subtype (is-connected-map-Prop k)
```

## Remark 18.5.6

In particular, every connected type is inhabited, because if `‖A‖₀` is contractible, then we have equivalences

```text
  ‖A‖ ≃ (‖A‖₀ → ‖A‖) ≃ (A → ‖A‖),
```

and the latter type contains the unit of the propositional truncation.

```agda
abstract
  is-trunc-is-prop :
    {l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

truncated-type-Prop : {l : Level} (k : 𝕋) → Prop l → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-Prop k P) = type-Prop P
pr2 (truncated-type-Prop k P) = is-trunc-is-prop k (is-prop-type-Prop P)

unique-truncated-fam-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (B : A → Truncated-Type l2 k) →
  is-contr
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (x : A) → type-equiv-Truncated-Type (B x) (C (unit-trunc x))))
unique-truncated-fam-trunc {l1} {l2} {k} {A} B =
  is-contr-equiv'
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (C ∘ unit-trunc) ~ B))
    ( equiv-tot
      ( λ C →
        equiv-Π-equiv-family
          ( λ x →
            ( extensionality-Truncated-Type (B x) (C (unit-trunc x))) ∘e
            ( equiv-inv (C (unit-trunc x)) (B x)))))
    ( universal-property-trunc
      ( succ-𝕋 k)
      ( A)
      ( Truncated-Type-Truncated-Type l2 k)
      ( B))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  where

  truncated-fam-trunc : type-trunc (succ-𝕋 k) A → Truncated-Type l2 k
  truncated-fam-trunc =
    pr1 (center (unique-truncated-fam-trunc B))

  fam-trunc : type-trunc (succ-𝕋 k) A → UU l2
  fam-trunc = type-Truncated-Type ∘ truncated-fam-trunc

  compute-truncated-fam-trunc :
    (x : A) →
    type-equiv-Truncated-Type (B x) (truncated-fam-trunc (unit-trunc x))
  compute-truncated-fam-trunc =
    pr2 (center (unique-truncated-fam-trunc B))

  map-compute-truncated-fam-trunc :
    (x : A) → type-Truncated-Type (B x) → (fam-trunc (unit-trunc x))
  map-compute-truncated-fam-trunc x =
    map-equiv (compute-truncated-fam-trunc x)

  total-truncated-fam-trunc : UU (l1 ⊔ l2)
  total-truncated-fam-trunc = Σ (type-trunc (succ-𝕋 k) A) fam-trunc

module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  ( C : total-truncated-fam-trunc B → Truncated-Type l3 k)
  ( f :
    ( x : A)
    ( y : type-Truncated-Type (B x)) →
    type-Truncated-Type
      ( C (unit-trunc x , map-equiv (compute-truncated-fam-trunc B x) y)))
  where

  dependent-universal-property-total-truncated-fam-trunc :
    is-contr
      ( Σ ( (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t))
          ( λ h →
            (x : A) (y : type-Truncated-Type (B x)) →
            h (unit-trunc x , map-compute-truncated-fam-trunc B x y) ＝
            f x y))
  dependent-universal-property-total-truncated-fam-trunc =
    is-contr-equiv _
      ( equiv-Σ
        ( λ g →
          (x : A) →
          g (unit-trunc x) ＝
          map-equiv-Π
            ( λ u → type-Truncated-Type (C (unit-trunc x , u)))
            ( compute-truncated-fam-trunc B x)
            ( λ u → id-equiv)
            ( f x))
        ( equiv-ev-pair)
        ( λ g →
          equiv-Π-equiv-family
            ( λ x →
              ( inv-equiv equiv-funext) ∘e
              ( equiv-Π
                ( λ y →
                  g (unit-trunc x , y) ＝
                  map-equiv-Π
                    ( λ u →
                      type-Truncated-Type (C (unit-trunc x , u)))
                    ( compute-truncated-fam-trunc B x)
                    ( λ u → id-equiv)
                    ( f x)
                    ( y))
                ( compute-truncated-fam-trunc B x)
                ( λ y →
                  equiv-concat'
                    ( g (unit-trunc x , map-compute-truncated-fam-trunc B x y))
                    ( inv
                      ( compute-map-equiv-Π
                        ( λ u → type-Truncated-Type (C (unit-trunc x , u)))
                        ( compute-truncated-fam-trunc B x)
                        ( λ y → id-equiv)
                        ( f x)
                        ( y))))))))
      ( unique-dependent-function-trunc
        ( λ y →
          truncated-type-succ-Truncated-Type k
            ( Π-Truncated-Type k
              ( truncated-fam-trunc B y)
              ( λ u → C (y , u))))
        ( λ y →
          map-equiv-Π
            ( λ u → type-Truncated-Type (C (unit-trunc y , u)))
            ( compute-truncated-fam-trunc B y)
            ( λ u → id-equiv)
            ( f y)))

  function-dependent-universal-property-total-truncated-fam-trunc :
    (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t)
  function-dependent-universal-property-total-truncated-fam-trunc =
    pr1 (center dependent-universal-property-total-truncated-fam-trunc)

  htpy-dependent-universal-property-total-truncated-fam-trunc :
    (x : A) (y : type-Truncated-Type (B x)) →
    function-dependent-universal-property-total-truncated-fam-trunc
        ( unit-trunc x , map-compute-truncated-fam-trunc B x y) ＝
    f x y
  htpy-dependent-universal-property-total-truncated-fam-trunc =
    pr2 (center dependent-universal-property-total-truncated-fam-trunc)

module _
  {l : Level} (k : 𝕋) {A : UU l} (a : A)
  where

  Eq-trunc-Truncated-Type : type-trunc (succ-𝕋 k) A → Truncated-Type l k
  Eq-trunc-Truncated-Type = truncated-fam-trunc (λ y → trunc k (a ＝ y))

  Eq-trunc : type-trunc (succ-𝕋 k) A → UU l
  Eq-trunc x = type-Truncated-Type (Eq-trunc-Truncated-Type x)

  compute-Eq-trunc : (x : A) → type-trunc k (a ＝ x) ≃ Eq-trunc (unit-trunc x)
  compute-Eq-trunc = compute-truncated-fam-trunc (λ y → trunc k (a ＝ y))

  map-compute-Eq-trunc :
    (x : A) → type-trunc k (a ＝ x) → Eq-trunc (unit-trunc x)
  map-compute-Eq-trunc x = map-equiv (compute-Eq-trunc x)

  refl-Eq-trunc : Eq-trunc (unit-trunc a)
  refl-Eq-trunc = map-compute-Eq-trunc a (unit-trunc refl)

  refl-compute-Eq-trunc :
    map-compute-Eq-trunc a (unit-trunc refl) ＝ refl-Eq-trunc
  refl-compute-Eq-trunc = refl

  is-torsorial-Eq-trunc : is-torsorial Eq-trunc
  pr1 (pr1 is-torsorial-Eq-trunc) = unit-trunc a
  pr2 (pr1 is-torsorial-Eq-trunc) = refl-Eq-trunc
  pr2 is-torsorial-Eq-trunc =
    function-dependent-universal-property-total-truncated-fam-trunc
      ( λ y → trunc k (a ＝ y))
      ( Id-Truncated-Type
          ( Σ-Truncated-Type
            ( trunc (succ-𝕋 k) A)
            ( λ b →
              truncated-type-succ-Truncated-Type k
                ( Eq-trunc-Truncated-Type b)))
          ( unit-trunc a , refl-Eq-trunc))
      ( λ y →
        function-dependent-universal-property-trunc
          ( λ q →
            Id-Truncated-Type
              ( Σ-Truncated-Type
                ( trunc (succ-𝕋 k) A)
                ( λ y →
                  truncated-type-succ-Truncated-Type k
                    ( Eq-trunc-Truncated-Type y)))
              ( unit-trunc a , refl-Eq-trunc)
              ( unit-trunc y , map-compute-Eq-trunc y q))
          ( r y))
    where
    r :
      (y : A) (p : a ＝ y) →
      Id
        { A = Σ (type-trunc (succ-𝕋 k) A) Eq-trunc}
        ( unit-trunc a , refl-Eq-trunc)
        ( unit-trunc y , (map-compute-Eq-trunc y (unit-trunc p)))
    r .a refl = refl

  Eq-eq-trunc : (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) → Eq-trunc x
  Eq-eq-trunc .(unit-trunc a) refl = refl-Eq-trunc

  is-equiv-Eq-eq-trunc :
    (x : type-trunc (succ-𝕋 k) A) → is-equiv (Eq-eq-trunc x)
  is-equiv-Eq-eq-trunc =
    fundamental-theorem-id
      ( is-torsorial-Eq-trunc)
      ( Eq-eq-trunc)

  extensionality-trunc :
    (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) ≃ Eq-trunc x
  pr1 (extensionality-trunc x) = Eq-eq-trunc x
  pr2 (extensionality-trunc x) = is-equiv-Eq-eq-trunc x

  effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) ≃ (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  effectiveness-trunc x =
    inv-equiv (extensionality-trunc (unit-trunc x)) ∘e compute-Eq-trunc x

  map-effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) → (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  map-effectiveness-trunc x = map-equiv (effectiveness-trunc x)

  refl-effectiveness-trunc :
    map-effectiveness-trunc a (unit-trunc refl) ＝ refl
  refl-effectiveness-trunc =
    is-retraction-map-inv-equiv (extensionality-trunc (unit-trunc a)) refl

module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  abstract
    is-inhabited-is-connected :
      is-connected (succ-𝕋 k) A → is-inhabited A
    is-inhabited-is-connected H =
      map-universal-property-trunc
        ( truncated-type-Prop k (is-inhabited-Prop A))
        ( unit-trunc-Prop)
        ( center H)

  abstract
    is-connected-eq-is-connected :
      is-connected (succ-𝕋 k) A → {x y : A} → is-connected k (x ＝ y)
    is-connected-eq-is-connected H {x} {y} =
      is-contr-equiv
        ( unit-trunc x ＝ unit-trunc y)
        ( effectiveness-trunc k x y)
        ( is-prop-is-contr H (unit-trunc x) (unit-trunc y))

  abstract
    is-connected-succ-is-connected-eq :
      is-inhabited A → ((x y : A) → is-connected k (x ＝ y)) →
      is-connected (succ-𝕋 k) A
    is-connected-succ-is-connected-eq H K =
      apply-universal-property-trunc-Prop H
        ( is-connected-Prop (succ-𝕋 k) A)
        ( λ a →
          ( unit-trunc a) ,
          ( function-dependent-universal-property-trunc
            ( Id-Truncated-Type
              ( truncated-type-succ-Truncated-Type
                ( succ-𝕋 k)
                ( trunc (succ-𝕋 k) A))
              ( unit-trunc a))
            ( λ x →
              map-universal-property-trunc
                ( Id-Truncated-Type
                  ( trunc (succ-𝕋 k) A)
                  ( unit-trunc a)
                  ( unit-trunc x))
                ( λ where refl → refl)
                ( center (K a x)))))
```

Using the notion of connectivity, we can add one more property to the list of equivalent characterizations of set truncations given in Theorem 18.5.2.

## Theorem 18.5.7

Consider a map `f : A → B` into a set `B`.
Then the following are equivalent:

1. The map `f` is a set truncation.

2. The map `f` is connected.

### Proof

First, suppose that `f` is a set truncation, and consider `b : B`.
Our goal is to show that the type

```text
  ‖fib(f, b)‖₀
```

is contractible.
Since `f` is surjective by Theorem 18.5.2, there exists an element `a : A` equipped with an identification `f(a) = b`.
We are proving a proposition, so it suffices to show that `‖fib(f,f(a))‖₀` is contractible.
At the center of contraction we have

```text
  η(a,refl) : ‖fib(f,f(a))‖₀.
```

In order to construct the contraction, we use the dependent universal property of the set truncation, by which it suffices to construct a function

```text
  Π(x : A) Π(p : f(x) = f(a)) η(a,refl) = η(x,p)
```

Recall from Theorem 18.5.2 that the map `f` is effective, so we have an equivalence `e : ‖x = a‖ ≃ (f(x) = f(a))` for every `x : A`.
Furthermore, equality in set truncations are propositions, so we may even eliminate the propositional truncation from `‖x = a‖`.
Therefore it suffices to prove

```text
  Π(x : A) Π(p : x = a) η(a,refl) = η(x,e(η(p)))
```

This is immediate, since `e(η(refl)) = refl`.
This completes the proof of (1) implies (2).

For the converse, suppose that `f` is connected, and consider a set `X`.
Note that we have a commuting square

```text
                               h ↦ λ b. λ t. h(b,η(t))

          (Π(b : B) ‖fib(f,b)‖₀ → X) ----------> (Π(b : B) fib(f,b) → X)
                      ↑                                     |
  h ↦ λ b. λ u. h(b)  |                                     | h ↦ λ a. h(f(a),(a,refl))
                      |                                     ∨
                   (B → X) ----------------------------> (A → X)
                                       - ∘ f
```

In this commuting square, the map on the left is an equivalence since `‖fib(f,b)‖₀` is contractible for each `b : B`.
The top map is an equivalence because `X` is a set, and the right map is an equivalence by Exercise 13.15.
Therefore it follows that the bottom map is an equivalence, which completes the proof that (2) implies (1). ◻

```agda
is-equiv-diagonal-exponential-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (diagonal-exponential (type-Truncated-Type B) A)
is-equiv-diagonal-exponential-is-connected {k = k} {A} B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( diagonal-exponential (type-Truncated-Type B) (type-trunc k A))
    ( is-equiv-diagonal-exponential-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)

is-connected-is-equiv-diagonal-exponential :
  {l1 : Level} {k : 𝕋} {A : UU l1} →
  ( {l2 : Level} (B : Truncated-Type l2 k) →
    is-equiv (diagonal-exponential (type-Truncated-Type B) A)) →
  is-connected k A
is-connected-is-equiv-diagonal-exponential {k = k} {A} H =
  tot
    ( λ x →
      function-dependent-universal-property-trunc
        ( Id-Truncated-Type' (trunc k A) x))
    ( tot
      ( λ _ → htpy-eq)
      ( center (is-contr-map-is-equiv (H (trunc k A)) unit-trunc)))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-connected-map : UUω
  dependent-universal-property-connected-map =
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    is-equiv (precomp-Π f (λ b → type-Truncated-Type (P b)))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-connected-map k f)
  where

  abstract
    dependent-universal-property-is-connected-map :
      dependent-universal-property-connected-map k f
    dependent-universal-property-is-connected-map P =
      is-equiv-precomp-Π-fiber-condition
        ( λ b → is-equiv-diagonal-exponential-is-connected (P b) (H b))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : connected-map k A B)
  where

  dup-connected-map :
    dependent-universal-property-connected-map k (map-connected-map f)
  dup-connected-map =
    dependent-universal-property-is-connected-map
      ( is-connected-map-connected-map f)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : connected-map k A B)
  where

  equiv-dependent-universal-property-is-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    ((b : B) → type-Truncated-Type (P b)) ≃
    ((a : A) → type-Truncated-Type (P (map-connected-map f a)))
  pr1 (equiv-dependent-universal-property-is-connected-map P) =
    precomp-Π (map-connected-map f) (λ b → type-Truncated-Type (P b))
  pr2 (equiv-dependent-universal-property-is-connected-map P) =
    dependent-universal-property-is-connected-map
      ( is-connected-map-connected-map f)
      ( P)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-connected-map k f)
  where

  ind-is-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    ((a : A) → type-Truncated-Type (P (f a))) →
    (b : B) → type-Truncated-Type (P b)
  ind-is-connected-map P =
    map-inv-is-equiv (dependent-universal-property-is-connected-map H P)

  compute-ind-is-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    (g : (a : A) → type-Truncated-Type (P (f a))) →
    (x : A) → ind-is-connected-map P g (f x) ＝ g x
  compute-ind-is-connected-map P f =
    htpy-eq
      ( is-section-map-inv-is-equiv
        ( dependent-universal-property-is-connected-map H P)
        ( f))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : connected-map k A B)
  where

  ind-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    ((a : A) → type-Truncated-Type (P (map-connected-map f a))) →
    (b : B) → type-Truncated-Type (P b)
  ind-connected-map = ind-is-connected-map (is-connected-map-connected-map f)

  compute-ind-connected-map :
    {l3 : Level} (P : B → Truncated-Type l3 k) →
    (g : (a : A) → type-Truncated-Type (P (map-connected-map f a))) →
    (x : A) → ind-connected-map P g (map-connected-map f x) ＝ g x
  compute-ind-connected-map =
    compute-ind-is-connected-map (is-connected-map-connected-map f)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B}
  (H : dependent-universal-property-connected-map k f)
  where

  center-is-connected-map-dependent-universal-property-connected-map :
    (b : B) → type-trunc k (fiber f b)
  center-is-connected-map-dependent-universal-property-connected-map =
    map-inv-is-equiv
      ( H (λ b → trunc k (fiber f b)))
      ( λ a → unit-trunc (a , refl))

  compute-center-is-connected-map-dependent-universal-property-connected-map :
    (a : A) →
    center-is-connected-map-dependent-universal-property-connected-map (f a) ＝
    unit-trunc (a , refl)
  compute-center-is-connected-map-dependent-universal-property-connected-map =
    htpy-eq
      ( is-section-map-inv-is-equiv
        ( H (λ b → trunc k (fiber f b)))
        ( λ a → unit-trunc (a , refl)))

  contraction-is-connected-map-dependent-universal-property-connected-map :
    (b : B) (u : type-trunc k (fiber f b)) →
    center-is-connected-map-dependent-universal-property-connected-map b ＝ u
  contraction-is-connected-map-dependent-universal-property-connected-map =
    map-Π
      ( λ b →
        function-dependent-universal-property-trunc
          ( Id-Truncated-Type' (trunc k (fiber f b)) _))
      ( extend-lift-family-of-elements-fiber f
        ( λ b u → _ ＝ unit-trunc u)
        ( compute-center-is-connected-map-dependent-universal-property-connected-map))

  abstract
    is-connected-map-dependent-universal-property-connected-map :
      is-connected-map k f
    pr1 (is-connected-map-dependent-universal-property-connected-map b) =
      center-is-connected-map-dependent-universal-property-connected-map b
    pr2 (is-connected-map-dependent-universal-property-connected-map b) =
      contraction-is-connected-map-dependent-universal-property-connected-map b

module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-map-unit-trunc :
    is-connected-map k (unit-trunc {k = k} {A = A})
  is-connected-map-unit-trunc =
    is-connected-map-dependent-universal-property-connected-map k
      dependent-universal-property-trunc

module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-trunc-map-precomp-Π-is-connected-map :
      (k n : 𝕋) →
      is-connected-map k f →
      {l3 : Level} (P : B → Truncated-Type l3 (add+2-𝕋 k n)) →
      is-trunc-map n (precomp-Π f (type-Truncated-Type ∘ P))
    is-trunc-map-precomp-Π-is-connected-map k neg-two-𝕋 H P =
      is-contr-map-is-equiv
        ( dependent-universal-property-is-connected-map H P)
    is-trunc-map-precomp-Π-is-connected-map k (succ-𝕋 n) H P =
      is-trunc-map-succ-precomp-Π
        ( λ g h →
          is-trunc-map-precomp-Π-is-connected-map k n H
            ( λ b → Id-Truncated-Type (P b) (g b) (h b)))

  abstract
    is-trunc-map-precomp-Π-is-connected-map' :
      (k n : 𝕋) →
      is-connected-map k f →
      {l3 : Level} (P : B → Truncated-Type l3 (add+2-𝕋 n k)) →
      is-trunc-map n (precomp-Π f (type-Truncated-Type ∘ P))
    is-trunc-map-precomp-Π-is-connected-map' k n H P =
      is-trunc-map-precomp-Π-is-connected-map k n H
        ( λ x →
          ( type-Truncated-Type (P x)) ,
          ( is-trunc-eq
            ( commutative-add+2-𝕋 n k)
            ( is-trunc-type-Truncated-Type (P x))))
```

## Remark 18.5.8

There are truncation operations for every truncation level.
That is, we can define for every type `A` a map `η : A → ‖A‖ₖ` such that the map

```text
  - ∘ η : (‖A‖ₖ → X) → (A → X)
```

is an equivalence for every `k`-truncated type `X`.
To learn more about general `k`-truncations, we refer to Chapter 7 of [the HoTT Book](https://homotopytypetheory.org/book/).

## Supplement

### Surjective maps are -1-connected

```agda
is-neg-one-connected-map-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-connected-map neg-one-𝕋 f
is-neg-one-connected-map-is-surjective H b =
  is-proof-irrelevant-is-prop is-prop-type-trunc-Prop (H b)
```

### Precomposing functions into a family of k+1-types by a surjective map is a k-truncated map

```agda
is-trunc-map-precomp-Π-is-surjective :
  {l1 l2 l3 : Level} (k : 𝕋) →
  {A : UU l1} {B : UU l2} {f : A → B} → is-surjective f →
  (P : B → Truncated-Type l3 (succ-𝕋 k)) →
  is-trunc-map k (precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-surjective k H =
  is-trunc-map-precomp-Π-is-connected-map'
    ( neg-one-𝕋)
    ( k)
    ( is-neg-one-connected-map-is-surjective H)
```


### Elements of 0-connected types are all merely equal

```agda
abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → all-elements-merely-equal A
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)
```

### A type is 0-connected if it is inhabited and all elements are merely equal

```agda
abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → all-elements-merely-equal A → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K =
    apply-universal-property-trunc-Prop H
      ( is-0-connected-Prop _)
      ( λ a → is-0-connected-mere-eq a (K a))
```

### A type is 0-connected iff any point inclusion is surjective

```agda
abstract
  is-0-connected-is-surjective-point :
    {l1 : Level} {A : UU l1} (a : A) →
    is-surjective (point a) → is-0-connected A
  is-0-connected-is-surjective-point a H =
    is-0-connected-mere-eq a
      ( λ x →
        apply-universal-property-trunc-Prop
          ( H x)
          ( mere-eq-Prop a x)
          ( λ u → unit-trunc-Prop (pr2 u)))

abstract
  is-surjective-point-is-0-connected :
    {l1 : Level} {A : UU l1} (a : A) →
    is-0-connected A → is-surjective (point a)
  is-surjective-point-is-0-connected a H x =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected H a x)
      ( trunc-Prop (fiber (point a) x))
      ( λ where refl → unit-trunc-Prop (star , refl))
```

### If A is 0-connected and B is k+1-truncated then every evaluation map (A → B) → B is k-truncated

```agda
is-trunc-map-ev-is-connected :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
  is-0-connected A → is-trunc (succ-𝕋 k) B →
  is-trunc-map k (ev-function B a)
is-trunc-map-ev-is-connected k {A} {B} a H K =
  is-trunc-map-comp k
    ( ev-function B star)
    ( precomp (point a) B)
    ( is-trunc-map-is-equiv k
      ( universal-property-contr-is-contr star is-contr-unit B))
    ( is-trunc-map-precomp-Π-is-surjective k
      ( is-surjective-point-is-0-connected a H)
      ( λ _ → (B , K)))
```

### The type Type-With-Cardinality-ℕ is connected

```agda
abstract
  is-0-connected-Type-With-Cardinality-ℕ :
    {l : Level} (n : ℕ) → is-0-connected (Type-With-Cardinality-ℕ l n)
  is-0-connected-Type-With-Cardinality-ℕ {l} n =
    is-0-connected-mere-eq
      ( raise-Fin-Type-With-Cardinality-ℕ l n)
      ( λ A →
        map-trunc-Prop
          ( ( eq-equiv-Type-With-Cardinality-ℕ n
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( A)) ∘
            ( map-equiv
              ( equiv-precomp-equiv
                ( inv-equiv (compute-raise l (Fin n)))
                ( type-Type-With-Cardinality-ℕ n A))))
          ( pr2 A))
```
