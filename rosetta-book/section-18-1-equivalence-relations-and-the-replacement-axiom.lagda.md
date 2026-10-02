# Section 18.1 Equivalence relations and the replacement axiom

```agda
module section-18-1-equivalence-relations-and-the-replacement-axiom where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-12-1-propositions
open import section-12-2-subtypes
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-17-4-maps-and-families-of-types
```

## Definition 18.1.1

Consider a type `A` and a universe `𝒰`.
Let `R : A → (A → Prop_𝒰)` be a binary relation on `A` valued in the propositions in `𝒰`.
We say that `R` is an **equivalence relation** if `R` comes equipped with

```text
  ρ : Π(x : A) R(x,x)
  σ : Π(x, y : A) R(x,y) → R(y,x)
  τ : Π(x, y, z : A) R(x,y) → (R(y,z) → R(x,z)),
```

witnessing that `R` is reflexive, symmetric, and transitive.
We write `Eq-Rel_𝒰(A)` for the type of all equivalence relations on `A` valued in the propositions in `𝒰`.

```agda
Relation-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Relation-Prop l A = A → A → Prop l

type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Relation l2 A
type-Relation-Prop R x y = pr1 (R x y)

is-prop-type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  (x y : A) → is-prop (type-Relation-Prop R x y)
is-prop-type-Relation-Prop R x y = pr2 (R x y)

total-space-Relation-Prop :
  {l : Level} {l1 : Level} {A : UU l1} → Relation-Prop l A → UU (l ⊔ l1)
total-space-Relation-Prop {A = A} R =
  Σ (A × A) λ (a , a') → type-Relation-Prop R a a'

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-reflexive-Relation-Prop : UU (l1 ⊔ l2)
  is-reflexive-Relation-Prop = is-reflexive (type-Relation-Prop R)

  is-prop-is-reflexive-Relation-Prop : is-prop is-reflexive-Relation-Prop
  is-prop-is-reflexive-Relation-Prop =
    is-prop-Π (λ x → is-prop-type-Relation-Prop R x x)

  is-reflexive-prop-Relation-Prop : Prop (l1 ⊔ l2)
  is-reflexive-prop-Relation-Prop =
    (is-reflexive-Relation-Prop , is-prop-is-reflexive-Relation-Prop)

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-symmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-symmetric-Relation-Prop = is-symmetric (type-Relation-Prop R)

  is-prop-is-symmetric-Relation-Prop : is-prop is-symmetric-Relation-Prop
  is-prop-is-symmetric-Relation-Prop =
    is-prop-Π
      ( λ x →
        is-prop-Π (λ y → is-prop-Π (λ r → is-prop-type-Relation-Prop R y x)))

  is-symmetric-prop-Relation-Prop : Prop (l1 ⊔ l2)
  is-symmetric-prop-Relation-Prop =
    (is-symmetric-Relation-Prop , is-prop-is-symmetric-Relation-Prop)

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-transitive-Relation-Prop : UU (l1 ⊔ l2)
  is-transitive-Relation-Prop = is-transitive (type-Relation-Prop R)

  is-prop-is-transitive-Relation-Prop : is-prop is-transitive-Relation-Prop
  is-prop-is-transitive-Relation-Prop =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y → 
            is-prop-Π
              ( λ z → 
                is-prop-function-type
                  ( is-prop-function-type (is-prop-type-Relation-Prop R x z)))))

is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Relation-Prop R ×
  is-symmetric-Relation-Prop R ×
  is-transitive-Relation-Prop R

equivalence-relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
equivalence-relation l A = Σ (Relation-Prop l A) is-equivalence-relation

prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → Relation-Prop l2 A
prop-equivalence-relation = pr1

sim-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → A → A → UU l2
sim-equivalence-relation R = type-Relation-Prop (prop-equivalence-relation R)

abstract
  is-prop-sim-equivalence-relation :
    {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (x y : A) →
    is-prop (sim-equivalence-relation R x y)
  is-prop-sim-equivalence-relation R =
    is-prop-type-Relation-Prop (prop-equivalence-relation R)

is-prop-is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  is-prop (is-equivalence-relation R)
is-prop-is-equivalence-relation R =
  is-prop-product
    ( is-prop-is-reflexive-Relation-Prop R)
    ( is-prop-product
      ( is-prop-is-symmetric-Relation-Prop R)
      ( is-prop-is-transitive-Relation-Prop R))

is-equivalence-relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Prop (l1 ⊔ l2)
pr1 (is-equivalence-relation-Prop R) = is-equivalence-relation R
pr2 (is-equivalence-relation-Prop R) = is-prop-is-equivalence-relation R

is-equivalence-relation-prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) →
  is-equivalence-relation (prop-equivalence-relation R)
is-equivalence-relation-prop-equivalence-relation R = pr2 R

refl-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-reflexive (sim-equivalence-relation R)
refl-equivalence-relation R =
  pr1 (is-equivalence-relation-prop-equivalence-relation R)

symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-symmetric (sim-equivalence-relation R)
symmetric-equivalence-relation R =
  pr1 (pr2 (is-equivalence-relation-prop-equivalence-relation R))

transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) → is-transitive (sim-equivalence-relation R)
transitive-equivalence-relation R =
  pr2 (pr2 (is-equivalence-relation-prop-equivalence-relation R))

inhabited-subtype-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} →
  equivalence-relation l2 A → A → inhabited-subtype l2 A
pr1 (inhabited-subtype-equivalence-relation R x) = prop-equivalence-relation R x
pr2 (inhabited-subtype-equivalence-relation R x) =
  unit-trunc-Prop (x , refl-equivalence-relation R x)
```

## Definition 18.1.2

Let `R : A → (A → Prop_𝒰)` be an equivalence relation.
A subtype `P : A → Prop_𝒰` is said to be an **equivalence class** if it satisfies the condition

```text
  is-equivalence-class(P) ≔ ∃_{(x:A)}∀_{(y:A)}P(y) ↔ R(x,y).
```

We define `A/R` to be the type of equivalence classes, i.e., we define

```text
  A/R ≔ Σ(P : A → Prop_𝒰) is-equivalence-class(P).
```

Furthermore, we define **equivalence class of `x : A`** to be

```text
  [x]_R ≔ R(x),
```

which is indeed an equivalence class.
Sometimes we will write `q_R : A → A/R` for the map `x ↦ [x]_R`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-equivalence-class-Prop : subtype l2 A → Prop (l1 ⊔ l2)
  is-equivalence-class-Prop P =
    ∃ A (λ x → has-same-elements-subtype-Prop P (prop-equivalence-relation R x))

  is-equivalence-class : subtype l2 A → UU (l1 ⊔ l2)
  is-equivalence-class P = type-Prop (is-equivalence-class-Prop P)

  is-prop-is-equivalence-class :
    (P : subtype l2 A) → is-prop (is-equivalence-class P)
  is-prop-is-equivalence-class P =
    is-prop-type-Prop (is-equivalence-class-Prop P)
```

### The condition on inhabited subtypes of `A` of being an equivalence class

```agda
  is-equivalence-class-inhabited-subtype-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-equivalence-class-inhabited-subtype-equivalence-relation Q =
    is-equivalence-class-Prop (subtype-inhabited-subtype Q)
```

### The type of equivalence classes

```agda
  equivalence-class : UU (l1 ⊔ lsuc l2)
  equivalence-class = type-subtype is-equivalence-class-Prop

  class : A → equivalence-class
  pr1 (class x) = prop-equivalence-relation R x
  pr2 (class x) =
    unit-trunc-Prop
      ( x , refl-has-same-elements-subtype (prop-equivalence-relation R x))

  emb-equivalence-class : equivalence-class ↪ subtype l2 A
  emb-equivalence-class = emb-subtype is-equivalence-class-Prop

  subtype-equivalence-class : equivalence-class → subtype l2 A
  subtype-equivalence-class = inclusion-subtype is-equivalence-class-Prop

  is-equivalence-class-equivalence-class :
    (C : equivalence-class) → is-equivalence-class (subtype-equivalence-class C)
  is-equivalence-class-equivalence-class =
    is-in-subtype-inclusion-subtype is-equivalence-class-Prop

  is-inhabited-subtype-equivalence-class :
    (C : equivalence-class) → is-inhabited-subtype (subtype-equivalence-class C)
  is-inhabited-subtype-equivalence-class (Q , H) =
    apply-universal-property-trunc-Prop H
      ( is-inhabited-subtype-Prop (subtype-equivalence-class (Q , H)))
      ( λ u →
        unit-trunc-Prop
          ( pr1 u ,
            backward-implication
              ( pr2 u (pr1 u))
              ( refl-equivalence-relation R (pr1 u))))

  inhabited-subtype-equivalence-class :
    (C : equivalence-class) → inhabited-subtype l2 A
  pr1 (inhabited-subtype-equivalence-class C) = subtype-equivalence-class C
  pr2 (inhabited-subtype-equivalence-class C) =
    is-inhabited-subtype-equivalence-class C

  is-in-equivalence-class : equivalence-class → (A → UU l2)
  is-in-equivalence-class P x = type-Prop (subtype-equivalence-class P x)

  abstract
    is-prop-is-in-equivalence-class :
      (x : equivalence-class) (a : A) →
      is-prop (is-in-equivalence-class x a)
    is-prop-is-in-equivalence-class P x =
      is-prop-type-Prop (subtype-equivalence-class P x)

  is-in-equivalence-class-Prop : equivalence-class → (A → Prop l2)
  pr1 (is-in-equivalence-class-Prop P x) = is-in-equivalence-class P x
  pr2 (is-in-equivalence-class-Prop P x) = is-prop-is-in-equivalence-class P x

  abstract
    is-set-equivalence-class : is-set equivalence-class
    is-set-equivalence-class =
      is-set-type-subtype is-equivalence-class-Prop is-set-subtype

  equivalence-class-Set : Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Set = equivalence-class
  pr2 equivalence-class-Set = is-set-equivalence-class

  unit-im-equivalence-class :
    hom-slice (prop-equivalence-relation R) subtype-equivalence-class
  pr1 unit-im-equivalence-class = class
  pr2 unit-im-equivalence-class x = refl

  is-surjective-class : is-surjective class
  is-surjective-class C =
    map-trunc-Prop
      ( tot
        ( λ x p →
          inv
            ( eq-type-subtype
              ( is-equivalence-class-Prop)
              ( eq-has-same-elements-subtype
                ( pr1 C)
                ( prop-equivalence-relation R x)
                ( p)))))
      ( pr2 C)

  is-image-equivalence-class :
    is-image
      ( prop-equivalence-relation R)
      ( emb-equivalence-class)
      ( unit-im-equivalence-class)
  is-image-equivalence-class =
    is-image-is-surjective
      ( prop-equivalence-relation R)
      ( emb-equivalence-class)
      ( unit-im-equivalence-class)
      ( is-surjective-class)
```

In other words, `A/R` is the image of the map `R : A → (A → Prop_𝒰)`.
In the following proposition we characterize the identity type of `A/R`.
As a corollary, we obtain equivalences

```text
  ([x]_R = [y]_R) ≃ R(x,y),
```

justifying that the quotient `A/R` is defined to be the type of equivalence classes.
Note that in our characterization of the identity type of `A/R` we make use of propositional extensionality.

## Proposition 18.1.3

Let `R : A → (A → Prop_𝒰)` be an equivalence relation.
Furthermore, consider `x : A` and an equivalence class `P`.
Then the canonical map

```text
  ([x]_R = P) → P(x)
```

is an equivalence.

### Proof

By Theorem 11.2.2 it suffices to show that the total space

```text
  Σ(P : A/R) P(x)
```

is contractible.
The center of contraction is of course `[x]_R`, which satisfies `[x]_R(x)` by reflexivity of `R`.
It remains to construct a contraction.
Since `Σ(P : A/R) P(x)` is a subtype of `A/R`, we construct a contraction by showing that

```text
  [x]_R = P
```

whenever `P(x)` holds.
Since `P` is an equivalence class there exists an element `y : A` such that `P = [y]_R`.
Note that our goal is a proposition, so we may assume that we have such a `y`.
From the assumption that `P(x)` holds, it follows that `R(x,y)` holds.
To complete the proof, it therefore is suffices to show that

```text
  [x]_R = [y]_R,
```

assuming that `R(x,y)` holds.
By function extensionality and propositional extensionality, it is equivalent to show that

```text
  Π(z : A) R(x,z) ↔ R(y,z),
```

which follows directly from the assumption that `R` is an equivalence relation. ◻

## Corollary 18.1.4

Consider an equivalence relation `R` on a type `A`, and let `x, y : A`.
Then there is an equivalence

```text
  ([x]_R = [y]_R) ≃ R(x,y).
```

## Remark 18.1.5

Notice that type of equivalence classes of an equivalence relation in `𝒰` is a type in the universe `𝒰⁺` that contains `𝒰` and every type in `𝒰`, or indeed in any universe `𝒱` containing `𝒰` and every type in `𝒰`.
Indeed, the type

```text
  Prop_𝒰 ≐ Σ(X : 𝒰) is-prop(X)
```

of propositions in `𝒰` is a type in `𝒱`.
It follows that the type `A → Prop_𝒰` is a type in `𝒱`.
The type of equivalence classes of an equivalence relation `R` on `A` in `𝒰` is a subtype of `A → Prop_𝒰` in `𝒰`, so we conclude that `A/R` is a type in `𝒱`.

In classical mathematics, on the other hand, we consider the class of equivalence classes of an equivalence relation to be a (small) set.
We will introduce the replacement axiom in order to ensure that set quotients in type theory are small.

Recall that in set theory, the replacement axiom asserts that for any family of sets `{X_i}_{i ∈ I}` indexed by a set `I`, there is a set `X[I]` consisting of precisely those sets `x` for which there exists an `i ∈ I` such that `x ∈ X_i`.
In other words: the image of a set-indexed family of sets is again a set.
Without the replacement axiom, `X[I]` would be a class.

In type theory, we may similarly ask whether the image of a map `X : I → 𝒰` is `𝒰`-small, assuming that `I` is `𝒰`-small.
The replacement axiom settles a more general variant of this question.
The key observation is that the identity types of `𝒰` are `𝒰`-small by the univalence axiom.
In other words, univalent universes are *locally small* in the following sense.

## Definition 18.1.6

Consider a universe `𝒰`.
A type `A` is said to be **locally `𝒰`-small** if the identity type `x = y` is `𝒰`-small for every `x, y : A`.
We write

```text
  is-locally-small_𝒰(A) ≔ Π(x, y : A) is-small_𝒰(x = y).
```

Similarly, a map `f : A → B` is said to be **locally `𝒰`-small** if all of its fibers are locally `𝒰`-small.

## Example 18.1.7

1. Any `𝒰`-small type is also locally `𝒰`-small.

2. Any proposition is locally small with respect to any universe `𝒰`.

3. Any univalent universe `𝒰` is locally `𝒰`-small, because by the univalence axiom we have an equivalence

   ```text
     (A = B) ≃ (A ≃ B)
   ```
    
   for each `A, B : 𝒰`, and the type `A ≃ B` is in `𝒰`.

4. For any family `B` of locally `𝒰`-small types over a `𝒰`-small type `A`, the dependent product `Π(x : A) B(x)` is locally `𝒰`-small.

We are now ready to assume the replacement axiom.

## Axiom 18.1.8

For any universe `𝒰`, we assume that for any map `f : A → B` from a `𝒰`-small type `A` into a locally `𝒰`-small type `B`, the image of `f` is `𝒰`-small.

## Example 18.1.9

For any type `A : 𝒰`, the type `𝒰_A` of all types in `𝒰` merely equivalent to `A` is equivalent to the image of the constant map `const_A : unit → 𝒰` is small.
Since `unit` is small and `𝒰` is locally `𝒰`-small, it follows from the replacement axiom that `𝒰_A` is `𝒰`-small.

## Example 18.1.10

The type `𝔽` of all finite types in `𝒰` is equivalent to be the image of the map

```text
  Fin : ℕ → 𝒰.
```

Since `ℕ` is `𝒰`-small and `𝒰` is locally `𝒰`-small, it follows from the replacement axiom that `𝔽` is `𝒰`-small.

## Example 18.1.11

Consider a type `A` in `𝒰` and an equivalence relation `R` on `A` in `𝒰`.
Then the type `A/R` is `𝒰`-small, since it is equivalent to the image of

```text
  R : A → (A → Prop_𝒰),
```

which maps the `𝒰`-small type `A` into the locally `𝒰`-small type `A → Prop_𝒰`.

