# Section 15.3 Cantor's diagonal argument

```agda
module section-15-3-cantors-diagonal-argument where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-10-3-contractible-maps
open import section-11-1-families-of-equivalences
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
```

Now that we have introduced surjective maps, we are in position to give Cantor’s famous diagonal argument, which he used to show that there are infinite sets of different cardinality.
The diagonal argument gives a proof that there is no surjective map from `X` to its power set `𝒫(X)`.
The power set of a type `X` is of course defined with respect to a universe `𝒰`, as the type of families of propositions in `𝒰` indexed by `X`.

## Definition 15.3.1

Consider a type `X`, and a universe `𝒰`.
We define the **`𝒰`-power set** of `X` to be

```text
  𝒫_{U}(X) ≔ X → Prop_𝒰.
```

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = subtype
```

## Theorem 15.3.2

For any type `X` and any universe `𝒰`, there is no surjective function

```text
  f : X → 𝒫_{U}(X)
```

### Proof

Consider a function `f : X → (X → Prop_𝒰)`, and suppose that `f` is surjective.
Following Cantor’s diagonalization argument, we define the subset `P : X → Prop_𝒰` by

```text
  P(x) ≔ ¬ f(x,x).
```

Our goal is to reach a contradiction and `f` is assumed to be surjective.
Therefore, it suffices to show that

```text
  ‖Σ(x : X) f(x) = P‖ → ∅.
```

The empty type is a proposition, so by the universal property of the propositional truncation it is equivalent to show that

```text
  (Σ(x : X) f(x) = P) → ∅.
```

Consider an element `x : X` equipped with an identification `f(x) = P`.
Our goal is to construct an element of the empty type, i.e, to reach a contradiction.
By the identification `f(x) = P` it follows that

```text
  f(x,y) ↔ P(y)
```

for all `y : X`.
In particular, it follows that `f(x,x) ↔ P(x)`.
However, since `P(x)` is defined as `¬ f(x,x)`, we obtain that `f(x,x) ↔ ¬ f(x,x)`.
By Exercise 4.3 this gives us the desired contradiction. ◻

```agda
is-irrefutable : {l : Level} → UU l → UU l
is-irrefutable X = ¬¬ X

is-prop-is-irrefutable : {l : Level} {X : UU l} → is-prop (is-irrefutable X)
is-prop-is-irrefutable = is-prop-double-negation

is-irrefutable-prop-Type : {l : Level} → UU l → Prop l
is-irrefutable-prop-Type X = (is-irrefutable X , is-prop-is-irrefutable)

is-double-negation-dense-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-double-negation-dense-map-Prop {B = B} f =
  Π-Prop B (is-irrefutable-prop-Type ∘ fiber f)

is-double-negation-dense-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-double-negation-dense-map f = type-Prop (is-double-negation-dense-map-Prop f)

is-prop-is-double-negation-dense-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-double-negation-dense-map f)
is-prop-is-double-negation-dense-map f =
  is-prop-type-Prop (is-double-negation-dense-map-Prop f)

iff-eq : {l1 : Level} {P Q : Prop l1} → P ＝ Q → (type-Prop P ↔ type-Prop Q)
pr1 (iff-eq refl) = id
pr2 (iff-eq refl) = id

double-negation-type-Prop :
  {l : Level} (A : UU l) → Prop l
double-negation-type-Prop A = neg-type-Prop (¬ A)

double-negation-Prop :
  {l : Level} (P : Prop l) → Prop l
double-negation-Prop P = double-negation-type-Prop (type-Prop P)

infix 25 ¬¬'_

¬¬'_ : {l : Level} (P : Prop l) → Prop l
¬¬'_ = double-negation-Prop

abstract
  intro-double-negation-type-trunc-Prop :
    {l : Level} {A : UU l} → type-trunc-Prop A → ¬¬ A
  intro-double-negation-type-trunc-Prop {A = A} =
    map-universal-property-trunc-Prop
      ( double-negation-type-Prop A)
      ( intro-double-negation)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-dense-map-is-surjective :
    {f : A → B} → is-surjective f → is-double-negation-dense-map f
  is-double-negation-dense-map-is-surjective H =
    intro-double-negation-type-trunc-Prop ∘ H

module _
  {l1 l2 : Level} {X : UU l1} (f : X → powerset l2 X)
  where

  subtype-theorem-Cantor : powerset l2 X
  subtype-theorem-Cantor x = neg-Prop (f x x)

  abstract
    not-in-image-subtype-theorem-Cantor : ¬ (fiber f subtype-theorem-Cantor)
    not-in-image-subtype-theorem-Cantor (ξ , α) =
      no-fixed-points-neg (type-Prop (f ξ ξ)) (iff-eq (htpy-eq α ξ))

    theorem-double-negation-dense-Cantor : ¬ (is-double-negation-dense-map f)
    theorem-double-negation-dense-Cantor H =
      H subtype-theorem-Cantor not-in-image-subtype-theorem-Cantor

    theorem-Cantor : ¬ (is-surjective f)
    theorem-Cantor =
      map-neg
        ( is-double-negation-dense-map-is-surjective)
        ( theorem-double-negation-dense-Cantor)
```
