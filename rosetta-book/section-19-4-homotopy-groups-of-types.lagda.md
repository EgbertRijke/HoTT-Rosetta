# Section 19.4 Homotopy groups of types

```agda
module section-19-4-homotopy-groups-of-types where

open import universe-levels
open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-11-6-the-structure-identity-principle
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
(A →_⋆ B) ≔ Σ(f : A → B) f(a) = b.
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

## Example 19.4.3

If `A` is a pointed `1`-type, then the loop space `Ω(A)` is a set.
Furthermore, it has the structure of a group.
Its unit is `refl`, and the group operation is given by concatenation of identifications.
This satisfies the group laws, since the group laws are just a special case of the groupoid laws for identity types, constructed in Section 5.2.
Thus we see that the loop space of a pointed `1`-type is a group.

If `A` is a pointed type, but not assumed to be `1`-truncated, then we can still obtain a group by taking the set truncation of its loop space.

## Definition 19.4.4

Consider a pointed type `A` with base point `a : A`, and let `n ≥ 1`.
Then we define the **`n`-th homotopy group** `π_n(A)` of `A` at `a` to be the group with underlying set

```text
π_n(A) ≔ ‖Ω^n(A)‖_0
```

The unit of the group is `η(refl)` and the group operation is the unique binary operation such that

```text
η(r)η(s) = η(r ∙ s)
```

for every `r,s : Ω^n(A)`.
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

Consider a pointed map `f : A →_⋆ B` between two pointed types `A` and `B`, where `p : f(a) = b`.
Then we define the pointed map

```text
Ω(f) : Ω(A) →_⋆ Ω(B)
```

by `Ω(f)(r) ≔ (p⁻¹ ∙ ap_{f}(r)) ∙ p`.
The identification witnessing that this is indeed a pointed map is obtained from the fact that `ap_{f}(refl) ≐ refl` and `p⁻¹ ∙ p = refl`.

Similarly, we define `Ω^n(f) : Ω^n(A) →_⋆ Ω^n(B)` recursively by

```text
Ω^0(f) ≔ f
Ω^{n+1}(f) ≔ Ω(Ω^n(f)).
```

The functorial action of `Ω^n` together with the functorial action of set truncation yield a functorial action

```text
π_n(f) : π_n(A) → π_n(B)
```

for every pointed map `f : A →_⋆ B`.

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

### Composing pointed maps

```agda
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
```

### The identity pointed map

```agda
module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →∗ A
  pr1 id-pointed-map = id
  pr2 id-pointed-map = refl
```

### Unpointed homotopies between pointed dependent functions and pointed maps

```agda
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
```

### The base point coherence of unpointed homotopies between pointed maps

```agda
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
```

### Pointed homotopies

```agda
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
```

### The reflexive pointed homotopy

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-pointed-htpy : pointed-htpy f f
  pr1 refl-pointed-htpy = refl-htpy
  pr2 refl-pointed-htpy = refl
```

### The pointed type of endomorphisms

```agda
endo : {l : Level} → UU l → UU l
endo A = A → A

endo-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (endo-Pointed-Type A) = A → A
pr2 (endo-Pointed-Type A) = id
```

### Pointed sections

```agda
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
