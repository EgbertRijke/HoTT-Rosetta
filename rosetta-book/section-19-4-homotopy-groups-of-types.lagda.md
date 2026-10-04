# Section 19.4 Homotopy groups of types

```agda
module section-19-4-homotopy-groups-of-types where

open import universe-levels
open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import exercise-8-4-prime-and-prime-counting-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-11-6-the-structure-identity-principle
open import section-18-5-set-truncations
```

Since the identity type gives every type groupoidal structure, we can construct for every type `A` equipped with a base point `a : A` a sequence of groups `π_n(A,a)` indexed by `n ≥ 1`.
In order to construct this sequence of groups, we first define the _loop space_ operation, which takes pointed types to pointed types.

## Definition 19.4.1

The type of **pointed types** in a universe `𝒰` is defined as

```text
𝒰_⋆ ≔ Σ(X : 𝒰) X.
```

```agda
Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A

  point-Pointed-Type : type-Pointed-Type
  point-Pointed-Type = pr2 A

ev-point-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) {B : UU l2} →
  (type-Pointed-Type A → B) → B
ev-point-Pointed-Type A f = f (point-Pointed-Type A)
```

Given two pointed types `A` and `B` with base points `a` and `b` respectively, we define the type of **pointed maps**

```text
(A →∗ B) ≔ Σ(f : A → B) f(a) = b.
```

```agda
Pointed-Fam :
  {l1 : Level} (l : Level) (A : Pointed-Type l1) → UU (lsuc l ⊔ l1)
Pointed-Fam l A =
  Σ (type-Pointed-Type A → UU l) (λ P → P (point-Pointed-Type A))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  fam-Pointed-Fam : type-Pointed-Type A → UU l2
  fam-Pointed-Fam = pr1 B

  point-Pointed-Fam : fam-Pointed-Fam (point-Pointed-Type A)
  point-Pointed-Fam = pr2 B

module _
  {l1 l2 : Level}
  where

  constant-Pointed-Fam :
    (A : Pointed-Type l1) → Pointed-Type l2 → Pointed-Fam l2 A
  constant-Pointed-Fam A B =
    pair (λ _ → type-Pointed-Type B) (point-Pointed-Type B)

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    fiber
      ( ev-point (point-Pointed-Type A) {fam-Pointed-Fam A B})
      ( point-Pointed-Fam A B)

  Π∗ : UU (l1 ⊔ l2)
  Π∗ = pointed-Π

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  where

  function-pointed-Π :
    pointed-Π A B → (x : type-Pointed-Type A) → fam-Pointed-Fam A B x
  function-pointed-Π = pr1

  preserves-point-function-pointed-Π :
    (f : pointed-Π A B) →
    function-pointed-Π f (point-Pointed-Type A) ＝ point-Pointed-Fam A B
  preserves-point-function-pointed-Π = pr2

module _
  {l1 l2 : Level}
  where

  pointed-map : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  pointed-map A B = pointed-Π A (constant-Pointed-Fam A B)

  infixr 5 _→∗_
  _→∗_ = pointed-map

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-pointed-map : A →∗ B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map = pr1

  preserves-point-pointed-map :
    (f : A →∗ B) →
    map-pointed-map f (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-map = pr2

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Fam l3 B) (f : A →∗ B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  pr1 precomp-Pointed-Fam = fam-Pointed-Fam B C ∘ map-pointed-map f
  pr2 precomp-Pointed-Fam =
    tr
      ( fam-Pointed-Fam B C)
      ( inv (preserves-point-pointed-map f))
      ( point-Pointed-Fam B C)

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  pr1 (precomp-pointed-Π g) x =
    function-pointed-Π g (map-pointed-map f x)
  pr2 (precomp-pointed-Π g) =
    ( inv
      ( apd
        ( function-pointed-Π g)
        ( inv (preserves-point-pointed-map f)))) ∙
    ( ap
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-pointed-map f)))
      ( preserves-point-function-pointed-Π g))

module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  map-comp-pointed-map :
    B →∗ C → A →∗ B → type-Pointed-Type A → type-Pointed-Type C
  map-comp-pointed-map g f =
    map-pointed-map g ∘ map-pointed-map f

  preserves-point-comp-pointed-map :
    (g : B →∗ C) (f : A →∗ B) →
    (map-comp-pointed-map g f (point-Pointed-Type A)) ＝ point-Pointed-Type C
  preserves-point-comp-pointed-map g f =
    ( ap (map-pointed-map g) (preserves-point-pointed-map f)) ∙
    ( preserves-point-pointed-map g)

  comp-pointed-map : B →∗ C → A →∗ B → A →∗ C
  pr1 (comp-pointed-map g f) = map-comp-pointed-map g f
  pr2 (comp-pointed-map g f) = preserves-point-comp-pointed-map g f

  infixr 15 _∘∗_

  _∘∗_ : B →∗ C → A →∗ B → A →∗ C
  _∘∗_ = comp-pointed-map

module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →∗ A
  pr1 id-pointed-map = id
  pr2 id-pointed-map = refl

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  unpointed-htpy-pointed-Π : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-Π = function-pointed-Π f ~ function-pointed-Π g

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f g : A →∗ B)
  where

  unpointed-htpy-pointed-map : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-map = map-pointed-map f ~ map-pointed-map g

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  coherence-point-unpointed-htpy-pointed-Π' :
    function-pointed-Π f (point-Pointed-Type A) ＝
    function-pointed-Π g (point-Pointed-Type A) →
    UU l2
  coherence-point-unpointed-htpy-pointed-Π' G =
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G)

  coherence-point-unpointed-htpy-pointed-Π :
    unpointed-htpy-pointed-Π f g → UU l2
  coherence-point-unpointed-htpy-pointed-Π G =
    coherence-point-unpointed-htpy-pointed-Π'
      ( G (point-Pointed-Type A))

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  pointed-htpy : UU (l1 ⊔ l2)
  pointed-htpy =
    Σ ( function-pointed-Π f ~ function-pointed-Π g)
      ( coherence-point-unpointed-htpy-pointed-Π f g)

  infix 6 _~∗_

  _~∗_ : UU (l1 ⊔ l2)
  _~∗_ = pointed-htpy

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-pointed-htpy : function-pointed-Π f ~ function-pointed-Π g
  htpy-pointed-htpy = pr1 H

  coherence-point-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
  coherence-point-pointed-htpy = pr2 H

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-pointed-htpy : pointed-htpy f f
  pr1 refl-pointed-htpy = refl-htpy
  pr2 refl-pointed-htpy = refl

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-retraction : (B →∗ A) → UU l1
  is-pointed-retraction g = g ∘∗ f ~∗ id-pointed-map

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-retraction : UU (l1 ⊔ l2)
  pointed-retraction =
    Σ (B →∗ A) (is-pointed-retraction f)

  module _
    (r : pointed-retraction)
    where

    pointed-map-pointed-retraction : B →∗ A
    pointed-map-pointed-retraction = pr1 r

    is-pointed-retraction-pointed-retraction :
      is-pointed-retraction f pointed-map-pointed-retraction
    is-pointed-retraction-pointed-retraction = pr2 r

    map-pointed-retraction : type-Pointed-Type B → type-Pointed-Type A
    map-pointed-retraction = map-pointed-map pointed-map-pointed-retraction

    preserves-point-pointed-map-pointed-retraction :
      map-pointed-retraction (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-pointed-map-pointed-retraction =
      preserves-point-pointed-map pointed-map-pointed-retraction

    is-retraction-pointed-retraction :
      is-retraction (map-pointed-map f) map-pointed-retraction
    is-retraction-pointed-retraction =
      htpy-pointed-htpy is-pointed-retraction-pointed-retraction

    retraction-pointed-retraction : retraction (map-pointed-map f)
    pr1 retraction-pointed-retraction = map-pointed-retraction
    pr2 retraction-pointed-retraction = is-retraction-pointed-retraction

    coherence-point-is-retraction-pointed-retraction :
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-pointed-retraction ∘∗ f)
        ( id-pointed-map)
        ( is-retraction-pointed-retraction)
    coherence-point-is-retraction-pointed-retraction =
      coherence-point-pointed-htpy is-pointed-retraction-pointed-retraction

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (g : type-Pointed-Type B → type-Pointed-Type A)
  (H : is-retraction (map-pointed-map f) g)
  where

  abstract
    uniquely-preserves-point-is-retraction-pointed-map :
      is-contr
        ( Σ ( g (point-Pointed-Type B) ＝ point-Pointed-Type A)
            ( coherence-square-identifications
              ( H (point-Pointed-Type A))
              ( ap g (preserves-point-pointed-map f))
              ( refl)))
    uniquely-preserves-point-is-retraction-pointed-map =
      is-contr-map-is-equiv
        ( is-equiv-concat (ap g (preserves-point-pointed-map f)) _)
        ( H (point-Pointed-Type A) ∙ refl)

  preserves-point-is-retraction-pointed-map :
    g (point-Pointed-Type B) ＝ point-Pointed-Type A
  preserves-point-is-retraction-pointed-map =
    inv (ap g (preserves-point-pointed-map f)) ∙ H (point-Pointed-Type A)

  pointed-map-is-retraction-pointed-map :
    B →∗ A
  pr1 pointed-map-is-retraction-pointed-map = g
  pr2 pointed-map-is-retraction-pointed-map =
    preserves-point-is-retraction-pointed-map

  coherence-point-is-retraction-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-is-retraction-pointed-map ∘∗ f)
      ( id-pointed-map)
      ( H)
  coherence-point-is-retraction-pointed-map =
    ( is-section-inv-concat (ap g (preserves-point-pointed-map f)) _) ∙
    ( inv right-unit)

  is-pointed-retraction-is-retraction-pointed-map :
    is-pointed-retraction f pointed-map-is-retraction-pointed-map
  pr1 is-pointed-retraction-is-retraction-pointed-map =
    H
  pr2 is-pointed-retraction-is-retraction-pointed-map =
    coherence-point-is-retraction-pointed-map

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-equiv : UU (l1 ⊔ l2)
  is-pointed-equiv = is-equiv (map-pointed-map f)

  is-prop-is-pointed-equiv : is-prop is-pointed-equiv
  is-prop-is-pointed-equiv = is-property-is-equiv (map-pointed-map f)

  is-pointed-equiv-Prop : Prop (l1 ⊔ l2)
  is-pointed-equiv-Prop = is-equiv-Prop (map-pointed-map f)

  module _
    (H : is-pointed-equiv)
    where

    map-inv-is-pointed-equiv : type-Pointed-Type B → type-Pointed-Type A
    map-inv-is-pointed-equiv = map-inv-is-equiv H

    is-section-map-inv-is-pointed-equiv :
      is-section (map-pointed-map f) map-inv-is-pointed-equiv
    is-section-map-inv-is-pointed-equiv = is-section-map-inv-is-equiv H

    is-retraction-map-inv-is-pointed-equiv :
      is-retraction (map-pointed-map f) map-inv-is-pointed-equiv
    is-retraction-map-inv-is-pointed-equiv =
      is-retraction-map-inv-is-equiv H

    preserves-point-map-inv-is-pointed-equiv :
      map-inv-is-pointed-equiv (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-map-inv-is-pointed-equiv =
      preserves-point-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    pointed-map-inv-is-pointed-equiv : B →∗ A
    pointed-map-inv-is-pointed-equiv =
      pointed-map-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    coherence-point-is-retraction-map-inv-is-pointed-equiv :
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-inv-is-pointed-equiv ∘∗ f)
        ( id-pointed-map)
        ( is-retraction-map-inv-is-pointed-equiv)
    coherence-point-is-retraction-map-inv-is-pointed-equiv =
      coherence-point-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

    is-pointed-retraction-pointed-map-inv-is-pointed-equiv :
      is-pointed-retraction f pointed-map-inv-is-pointed-equiv
    is-pointed-retraction-pointed-map-inv-is-pointed-equiv =
      is-pointed-retraction-is-retraction-pointed-map f
        ( map-inv-is-pointed-equiv)
        ( is-retraction-map-inv-is-pointed-equiv)

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-section : (B →∗ A) → UU l2
  is-pointed-section g = f ∘∗ g ~∗ id-pointed-map

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-section : UU (l1 ⊔ l2)
  pointed-section =
    Σ (B →∗ A) (is-pointed-section f)

  module _
    (s : pointed-section)
    where

    pointed-map-pointed-section : B →∗ A
    pointed-map-pointed-section = pr1 s

    is-pointed-section-pointed-section :
      is-pointed-section f pointed-map-pointed-section
    is-pointed-section-pointed-section = pr2 s

    map-pointed-section : type-Pointed-Type B → type-Pointed-Type A
    map-pointed-section = map-pointed-map pointed-map-pointed-section

    preserves-point-pointed-map-pointed-section :
      map-pointed-section (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-pointed-map-pointed-section =
      preserves-point-pointed-map pointed-map-pointed-section

    is-section-pointed-section :
      is-section (map-pointed-map f) map-pointed-section
    is-section-pointed-section =
      htpy-pointed-htpy is-pointed-section-pointed-section

    section-pointed-section : section (map-pointed-map f)
    pr1 section-pointed-section = map-pointed-section
    pr2 section-pointed-section = is-section-pointed-section

    coherence-point-is-section-pointed-section :
      coherence-point-unpointed-htpy-pointed-Π
        ( f ∘∗ pointed-map-pointed-section)
        ( id-pointed-map)
        ( is-section-pointed-section)
    coherence-point-is-section-pointed-section =
      coherence-point-pointed-htpy is-pointed-section-pointed-section

pointed-equiv :
  {l1 l2 : Level} → Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
pointed-equiv A B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → map-equiv e (point-Pointed-Type A) ＝ point-Pointed-Type B)

infix 6 _≃∗_

_≃∗_ : {l1 l2 : Level} → Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
_≃∗_ = pointed-equiv

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (e : A ≃∗ B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-pointed-equiv = map-equiv equiv-pointed-equiv

  preserves-point-pointed-equiv :
    map-pointed-equiv (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →∗ B
  pr1 pointed-map-pointed-equiv = map-pointed-equiv
  pr2 pointed-map-pointed-equiv = preserves-point-pointed-equiv

  is-equiv-map-pointed-equiv : is-equiv map-pointed-equiv
  is-equiv-map-pointed-equiv = is-equiv-map-equiv equiv-pointed-equiv

  is-pointed-equiv-pointed-equiv :
    is-pointed-equiv pointed-map-pointed-equiv
  is-pointed-equiv-pointed-equiv = is-equiv-map-pointed-equiv

  pointed-map-inv-pointed-equiv : B →∗ A
  pointed-map-inv-pointed-equiv =
    pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  map-inv-pointed-equiv : type-Pointed-Type B → type-Pointed-Type A
  map-inv-pointed-equiv =
    map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  preserves-point-map-inv-pointed-equiv :
    map-inv-pointed-equiv (point-Pointed-Type B) ＝ point-Pointed-Type A
  preserves-point-map-inv-pointed-equiv =
    preserves-point-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-section-map-inv-pointed-equiv :
    is-section
      ( map-pointed-equiv)
      ( map-inv-pointed-equiv)
  is-section-map-inv-pointed-equiv =
    is-section-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-pointed-retraction-pointed-map-inv-pointed-equiv :
    is-pointed-retraction
      ( pointed-map-pointed-equiv)
      ( pointed-map-inv-pointed-equiv)
  is-pointed-retraction-pointed-map-inv-pointed-equiv =
    is-pointed-retraction-pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  is-retraction-map-inv-pointed-equiv :
    is-retraction
      ( map-pointed-equiv)
      ( map-inv-pointed-equiv)
  is-retraction-map-inv-pointed-equiv =
    is-retraction-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)

  coherence-point-is-retraction-map-inv-pointed-equiv :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-inv-pointed-equiv ∘∗ pointed-map-pointed-equiv)
      ( id-pointed-map)
      ( is-retraction-map-inv-pointed-equiv)
  coherence-point-is-retraction-map-inv-pointed-equiv =
    coherence-point-is-retraction-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv)
      ( is-pointed-equiv-pointed-equiv)
```

## Definition 19.4.2

Consider a universe `𝒰`.
We define the **loop space** operation

```text
Ω : 𝒰_⋆ → 𝒰_⋆
```

by `Ω(A,a) ≔ (a = a,refl)`.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Ω : UU l
  type-Ω = point-Pointed-Type A ＝ point-Pointed-Type A

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = (type-Ω , refl-Ω)
```

Furthermore, we define for every `A : 𝒰_⋆` the **iterated loop space** `Ω^n(A)` recursively by

```text
Ω^0(A) ≔ A
Ω^{n+1}(A) ≔ Ω(Ω^n(A)).
```

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space n = iterate n Ω

  type-iterated-loop-space : ℕ → Pointed-Type l → UU l
  type-iterated-loop-space n A = type-Pointed-Type (iterated-loop-space n A)

  point-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) → type-iterated-loop-space n A
  point-iterated-loop-space n A = point-Pointed-Type (iterated-loop-space n A)
```

## Example 19.4.3

If `A` is a pointed `1`-type, then the loop space `Ω(A)` is a set.
Furthermore, it has the structure of a group.
Its unit is `refl`, and the group operation is given by concatenation of identifications.
This satisfies the group laws, since the group laws are just a special case of the groupoid laws for identity types, constructed in Section 5.2.
Thus we see that the loop space of a pointed `1`-type is a group.

```agda
module _
  {l : Level} (k : 𝕋) (A : Pointed-Type l)
  where

  is-trunc-Ω : is-trunc (succ-𝕋 k) (type-Pointed-Type A) → is-trunc k (type-Ω A)
  is-trunc-Ω H = H (point-Pointed-Type A) (point-Pointed-Type A)

is-trunc-iterated-loop-space :
  {l : Level} (n : ℕ) (k : 𝕋) (A : Pointed-Type l) →
  is-trunc (iterate-succ-𝕋 n k) (type-Pointed-Type A) →
  is-trunc k (type-iterated-loop-space n A)
is-trunc-iterated-loop-space zero-ℕ k A H = H
is-trunc-iterated-loop-space (succ-ℕ n) k A H =
  is-trunc-Ω k
    ( iterated-loop-space n A)
    ( is-trunc-iterated-loop-space n (succ-𝕋 k) A H)
```

If `A` is a pointed type, but not assumed to be `1`-truncated, then we can still obtain a group by taking the set truncation of its loop space.

## Definition 19.4.4

Consider a pointed type `A` with base point `a : A`, and let `n ≥ 1`.
Then we define the **`n`-th homotopy group** `π_n(A)` of `A` at `a` to be the group with underlying set

```text
π_n(A) ≔ ‖Ω^n(A)‖_0
```

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  set-homotopy-group : Set l
  set-homotopy-group = trunc-Set (type-iterated-loop-space n A)

  type-homotopy-group : UU l
  type-homotopy-group = type-Set set-homotopy-group

  is-set-type-homotopy-group : is-set type-homotopy-group
  is-set-type-homotopy-group = is-set-type-Set set-homotopy-group

  point-homotopy-group : type-homotopy-group
  point-homotopy-group = unit-trunc-Set (point-iterated-loop-space n A)

  pointed-type-homotopy-group : Pointed-Type l
  pr1 pointed-type-homotopy-group = type-homotopy-group
  pr2 pointed-type-homotopy-group = point-homotopy-group
```

The unit of the group is `η(refl)` and the group operation is the unique binary operation such that

```text
η(r)η(s) = η(r ∙ s)
```

for every `r,s : Ω^n(A)`.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω x y = x ∙ y

  left-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω (refl-Ω A) x ＝ x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω x (refl-Ω A) ＝ x
  right-unit-law-mul-Ω x = right-unit

  coherence-unit-laws-mul-Ω :
    left-unit-law-mul-Ω refl ＝ right-unit-law-mul-Ω refl
  coherence-unit-laws-mul-Ω = refl

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = inv

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → mul-Ω (inv-Ω x) x ＝ refl-Ω A
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → mul-Ω x (inv-Ω x) ＝ refl-Ω A
  right-inverse-law-mul-Ω x = right-inv x

  associative-mul-Ω :
    (x y z : type-Ω A) →
    mul-Ω (mul-Ω x y) z ＝ mul-Ω x (mul-Ω y z)
  associative-mul-Ω = assoc

module _
  {l1 : Level} {A : UU l1} {x y : A}
  where

  equiv-tr-Ω : x ＝ y → Ω (A , x) ≃∗ Ω (A , y)
  equiv-tr-Ω refl = (id-equiv , refl)

  equiv-tr-type-Ω : x ＝ y → type-Ω (A , x) ≃ type-Ω (A , y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (equiv-tr-Ω p)

  tr-type-Ω : x ＝ y → type-Ω (A , x) → type-Ω (A , y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  tr-Ω : x ＝ y → Ω (A , x) →∗ Ω (A , y)
  tr-Ω p = pointed-map-pointed-equiv (equiv-tr-Ω p)

  is-equiv-tr-type-Ω : (p : x ＝ y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : x ＝ y) → tr-type-Ω p refl ＝ refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : x ＝ y) (u v : type-Ω (A , x)) →
    tr-type-Ω p (mul-Ω (A , x) u v) ＝
    mul-Ω (A , y) (tr-type-Ω p u) (tr-type-Ω p v)
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : x ＝ y) (u : type-Ω (A , x)) →
    tr-type-Ω p (inv-Ω (A , x) u) ＝
    inv-Ω (A , y) (tr-type-Ω p u)
  preserves-inv-tr-Ω refl u = refl

  eq-conjugation-tr-type-Ω :
    (p : x ＝ y) (q : type-Ω (A , x)) →
    tr-type-Ω p q ＝ inv p ∙ (q ∙ p)
  eq-conjugation-tr-type-Ω refl q = inv right-unit

  compute-eq-conjugation-tr-type-Ω-refl :
    (p : x ＝ y) →
    preserves-refl-tr-Ω p ∙ inv (left-inv p) ＝ eq-conjugation-tr-type-Ω p refl
  compute-eq-conjugation-tr-type-Ω-refl refl = refl
```

The group `π_1(A)` of a pointed type is called the **fundamental group** of `A` at its base point `a : A`.

## Remark 19.4.5

Note that for `n = 0`, we can still define the set

```text
π_0(A) ≔ ‖A‖_0.
```

However, this set does not necessarily come equipped with the structure of a group.

## Proposition 19.4.6

For any pointed type `A` and any `n ≥ 1` we have an isomorphism

```text
π_{n+1}(A) ≅ π_n(Ω(A)).
```

### Proof

_Proof._ First, observe that we have a pointed equivalence

```text
Ω(Ω^n(A)) ≃_⋆ Ω^n(Ω(A)).
```

This equivalence is constructed by induction on `n`, and also preserves the concatenation operation.
Using this equivalence, we obtain a group isomorphism

```text
π_{n+1}(A) ≐ ‖Ω(Ω^n(A))‖_0 ≅ ‖Ω^n(Ω(A))‖_0 ≐ π_n(Ω(A)).
```

 ◻

Homotopy groups are important algebraic invariants of a type.
For example, they can be used to show that two pointed types `A` and `B` are not equivalent by showing that two types `A` and `B` have non-isomorphic homotopy groups.
The study of homotopy groups of types is an intricate and complicated subject, analogous to algebraic topology.
Since the homotopy groups of types are obtained in such a canonical manner from the identity types, which are inductively generated by just the reflexivity identification, the subject of studying homotopy groups of types is also called _synthetic homotopy theory_.
In the final section of this book we will show that the fundamental group of the circle, which is introduced as a _higher inductive type_, is `ℤ`.
In this section we will show that equivalent types have isomorphic homotopy groups, and that the homotopy groups `π_n(A)` are abelian if `n ≥ 2`.

## Definition 19.4.7

Consider a pointed map `f : A →∗ B` between two pointed types `A` and `B`, where `p : f(a) = b`.
Then we define the pointed map

```text
Ω(f) : Ω(A) →∗ Ω(B)
```

by `Ω(f)(r) ≔ (p⁻¹ ∙ ap_{f}(r)) ∙ p`.
The identification witnessing that this is indeed a pointed map is obtained from the fact that `ap_{f}(refl) ≐ refl` and `p⁻¹ ∙ p = refl`.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) p)

  preserves-refl-map-Ω : map-Ω refl ＝ refl
  preserves-refl-map-Ω = preserves-refl-tr-Ω (pr2 f)

  pointed-map-Ω : Ω A →∗ Ω B
  pr1 pointed-map-Ω = map-Ω
  pr2 pointed-map-Ω = preserves-refl-map-Ω

  preserves-mul-map-Ω :
    {x y : type-Ω A} → map-Ω (mul-Ω A x y) ＝ mul-Ω B (map-Ω x) (map-Ω y)
  preserves-mul-map-Ω {x} {y} =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-concat (map-pointed-map f) x y)) ∙
    ( preserves-mul-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x)
      ( ap (map-pointed-map f) y))

  preserves-inv-map-Ω :
    (x : type-Ω A) → map-Ω (inv-Ω A x) ＝ inv-Ω B (map-Ω x)
  preserves-inv-map-Ω x =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-inv (map-pointed-map f) x)) ∙
    ( preserves-inv-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x))
```

Similarly, we define `Ω^n(f) : Ω^n(A) →∗ Ω^n(B)` recursively by

```text
Ω^0(f) ≔ f
Ω^{n+1}(f) ≔ Ω(Ω^n(f)).
```

The functorial action of `Ω^n` together with the functorial action of set truncation yield a functorial action

```text
π_n(f) : π_n(A) → π_n(B)
```

for every pointed map `f : A →∗ B`.

## Remark 19.4.8

Since action of paths preserves path concatenation, it follows that `Ω^n(f)` preserves path concatenation, for each `n ≥ 1`.
Consequently, the maps

```text
π_n(f) : π_n(A) → π_n(B)
```

are group homomorphisms.

## Proposition 19.4.9

Consider a pointed equivalence `e : A ≃_⋆ B` between two pointed types `A` and `B`.
Then we obtain group isomorphisms

```text
π_n(e) : π_n(A) ≅ π_n(B)
```

for all `n ≥ 1`.

### Proof

_Proof._ For any pointed equivalence `e : A ≃_⋆ B` it follows that `π_n(e)` is also an equivalence.
Using Lemma 19.3.1, the claim now follows. ◻

## Supplement

### The pointed type of endomorphisms

```agda
endo : {l : Level} → UU l → UU l
endo A = A → A

endo-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (endo-Pointed-Type A) = A → A
pr2 (endo-Pointed-Type A) = id
```

### Extensionality of pointed dependent function types by pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  abstract
    is-torsorial-pointed-htpy :
      is-torsorial (pointed-htpy f)
    is-torsorial-pointed-htpy =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy _)
        ( function-pointed-Π f , refl-htpy)
        ( is-torsorial-Id _)

  pointed-htpy-eq :
    (g : pointed-Π A B) → f ＝ g → f ~∗ g
  pointed-htpy-eq .f refl = refl-pointed-htpy f

  abstract
    is-equiv-pointed-htpy-eq :
      (g : pointed-Π A B) → is-equiv (pointed-htpy-eq g)
    is-equiv-pointed-htpy-eq =
      fundamental-theorem-id
        ( is-torsorial-pointed-htpy)
        ( pointed-htpy-eq)

  extensionality-pointed-Π :
    (g : pointed-Π A B) → (f ＝ g) ≃ (f ~∗ g)
  pr1 (extensionality-pointed-Π g) = pointed-htpy-eq g
  pr2 (extensionality-pointed-Π g) = is-equiv-pointed-htpy-eq g

  eq-pointed-htpy :
    (g : pointed-Π A B) → f ~∗ g → f ＝ g
  eq-pointed-htpy g = map-inv-equiv (extensionality-pointed-Π g)
```
