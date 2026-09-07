# Section 14.1 The universal property of propositional truncations

```agda
module section-14-1-the-universal-property-of-propositional-truncations where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import exercise-4-3-negation
open import exercise-10-1-identity-types-contractible
open import exercise-12-6-truncated-sigma-types
```

<!-- rosetta-item: section-14.1 -->

The propositional truncation of a type `A` is a proposition `‖A‖` equipped with a map
```text
η:A→ ‖A‖.
```
This map ensures that if we have an element `a:A`, then the proposition `‖A‖` that `A` is inhabited holds.
The complete specification of the propositional truncation includes the universal property of the map `η`.
In this section we will specify in full generality when a map `f:A→ P` into a proposition `P` is a propositional truncation.

## Definition 14.1.1

<!-- rosetta-item: definition-14.1.1 -->

Let `A` be a type, and let `f:A→ P` be a map into a proposition `P`.
We say that `f` **is a propositional truncation** of `A` if for every proposition `Q`, the precomposition map
```text
_∘ f:(P→ Q)→ (A→ Q)
```
is an equivalence.
This property of `f` is called the **universal property of the propositional truncation of `A`**.

<!-- rosetta-agda-block: definition-14.1.1-propositional-truncation -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P)
  where

  precomp-Prop :
    {l3 : Level} (Q : Prop l3) →
    (type-Prop P → type-Prop Q) → A → type-Prop Q
  precomp-Prop Q g = g ∘ f

  is-propositional-truncation : Typeω
  is-propositional-truncation =
    {l : Level} (Q : Prop l) → is-equiv (precomp-Prop Q)
```
<!-- rosetta-item-end: definition-14.1.1 -->

## Remark 14.1.2

<!-- rosetta-item: remark-14.1.2; latex-label: ex:prop_equiv -->

Using the fact that equivalences are maps that have contractible fibers, we can reformulate the universal property of the propositional truncation.
Note that the fiber of the precomposition map `_∘ f:(P→ Q) → (A → Q)` at a map `g:A→ Q` is the type.
```text
Σ(h:P→ Q) h∘ f=g
```
Therefore we see that if `f` satisfies the universal property of the propositional truncation, then these fibers are contractible.
In other words, for each map `g:A→ Q` into a proposition `Q` there is a unique map `h:P→ Q` for which `h∘ f=g`.
We also say that every map `g:A→ Q` into a proposition `Q` *extends* uniquely along `f`, as indicated in the diagram
<!-- rosetta-diagram: cbd3f685da87; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
 [P] ----> [Q]

Arrows:
- A --f--> P
- A --g--> Q
- P --unlabeled--> Q
```

<!-- rosetta-agda-block: remark-14.1.2-unique-extensions -->

```agda
module _
  {l1 l2 : Level} {A : Type l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  universal-property-propositional-truncation : Typeω
  universal-property-propositional-truncation =
    {l : Level} (Q : Prop l) (g : A → type-Prop Q) →
    is-contr (Σ ((type-Prop P → type-Prop Q)) (λ h → h ∘ f ＝ g))
```

<!-- rosetta-agda-block: remark-14.1.2-contractible-extensions-from-truncation -->

```agda
abstract
  universal-property-is-propositional-truncation :
    {l1 l2 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    universal-property-propositional-truncation P f
  universal-property-is-propositional-truncation P f H Q =
    is-contr-map-is-equiv (H Q)
```

<!-- rosetta-agda-block: remark-14.1.2-truncation-from-contractible-extensions -->

```agda
abstract
  is-propositional-truncation-universal-property :
    {l1 l2 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P) →
    universal-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-universal-property P f H Q =
    is-equiv-is-contr-map (H Q)
```

<!-- rosetta-agda-block: remark-14.1.2-extension-map-and-equation -->

```agda
abstract
  map-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    (Q : Prop l3) (g : A → type-Prop Q) → (type-Prop P → type-Prop Q)
  map-is-propositional-truncation P f is-ptr-f Q g =
    pr1
      ( center
        ( universal-property-is-propositional-truncation P f is-ptr-f Q g))

  eq-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P) →
    (is-ptr-f : is-propositional-truncation P f) →
    (Q : Prop l3) (g : A → type-Prop Q) →
    map-is-propositional-truncation P f is-ptr-f Q g ∘ f ＝ g
  eq-is-propositional-truncation P f is-ptr-f Q g =
    pr2
      ( center
        ( universal-property-is-propositional-truncation P f is-ptr-f Q g))
```
<!-- rosetta-item-end: remark-14.1.2 -->

## Remark 14.1.3

<!-- rosetta-item: remark-14.1.3; latex-label: rmk:simplified-up-trunc-Prop -->

For any two propositions `P` and `P'`, a map `f:P→ P'` is an equivalence if and only if there is a function `g:P'→ P`.
To see this, simply note that any such function `g` is an inverse of `f`, because any two elements in `P` and any two elements in `P'` are equal.

Note that the type `X→ Q` is a proposition, for any type `X` and any proposition `Q`.
Using the previous observation, it therefore follows that the map `(P→ Q)→ (A→ Q)` is an equivalence as soon as there is a map in the converse direction.
In other words, to prove that a map `f:A→ P` into a proposition `P` satisfies the universal property of the propositional truncation of `A`, it suffices to construct a function
```text
(A→ Q)→ (P→ Q)
```
for every proposition `Q`.

<!-- rosetta-agda-block: remark-14.1.3-extension-property -->

```agda
module _
  {l1 l2 : Level} {A : Type l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  extension-property-propositional-truncation : Typeω
  extension-property-propositional-truncation =
    {l : Level} (Q : Prop l) → (A → type-Prop Q) → (type-Prop P → type-Prop Q)
```

<!-- rosetta-agda-block: remark-14.1.3-truncation-from-extension -->

```agda
abstract
  is-propositional-truncation-extension-property :
    { l1 l2 : Level} {A : Type l1} (P : Prop l2)
    ( f : A → type-Prop P) →
    extension-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-extension-property P f up-P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( up-P Q)
```

<!-- rosetta-agda-block: remark-14.1.3-extension-from-truncation -->

```agda
extension-property-is-propositional-truncation :
  {l1 l2 : Level} {A : Type l1} (P : Prop l2) (f : A → type-Prop P) →
  is-propositional-truncation P f →
  extension-property-propositional-truncation P f
extension-property-is-propositional-truncation P f H =
  map-is-propositional-truncation P f H
```
<!-- rosetta-item-end: remark-14.1.3 -->

In the following proposition we show that the propositional truncation of a type `A` is uniquely determined up to equivalence, if it exists.
In other words, any two propositional truncations of a type `A` must be equivalent.

## Proposition 14.1.4

<!-- rosetta-item: proposition-14.1.4 -->

Let `A` be a type, and consider two maps
```text
f:A→ P and f':A→ P'
```
into two propositions `P` and `P'`.
If any two of the following three assertions hold, so does the third:

1.  The map `f` is a propositional truncation of `A`.

2.  The map `f'` is a propositional truncation of `A`.

3.  There is a (unique) equivalence `P≃ P'`.

### Proof

<!-- rosetta-item: subheading-14.1-proof -->

*Proof.* We first show that (i) and (ii) together imply (iii).
If `f` and `f'` are both propositional truncations of `A`, then we have maps `P→ P'` and `P'→ P` by the universal properties of `f` and `f'`.
Since `P` and `P'` are both propositions, it follows that `P≃ P'`.
For the uniqueness claim, note that the type `P≃ P'` is itself a proposition.

Finally we show that (iii) implies that (i) holds if and only if (ii) holds.
Suppose we have an equivalence `P≃ P'`, let `Q` be an arbitrary proposition, and consider the triangle
<!-- rosetta-diagram: 82048488c0ff; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
             [(A→ Q)]

[(P→ Q)]                  [(P'→ Q)]

Arrows:
- (A→ Q) --unlabeled--> (P→ Q)
- (A→ Q) --unlabeled--> (P'→ Q)
- (P→ Q) --unlabeled--> (P'→ Q)
```
where the fact that `(P→ Q)↔ (P'→ Q)` holds follows from the assumption that `P` is equivalent to `P'`.
We see from this triangle that
```text
((A→ Q)→ (P→ Q))↔((A → Q) → (P'→ Q)),
```
and this implies that (i) holds if and only if (ii) holds. ◻

<!-- rosetta-agda-block: proposition-14.1.4-propositional-equivalence-type -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop H K =
    is-prop-Σ
      ( is-prop-function-type K)
      ( λ f →
        is-prop-product
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ g → is-prop-is-contr (is-contr-Π (λ y → K (f (g y)) y))))
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ h → is-prop-is-contr (is-contr-Π (λ x → H (h (f x)) x)))))
```

<!-- rosetta-agda-block: proposition-14.1.4-equivalence-of-truncations -->

```agda
equiv-is-propositional-truncation :
  {l1 l2 l3 : Level} {A : Type l1} (P : Prop l2) (P' : Prop l3) →
  (f : A → type-Prop P) (f' : A → type-Prop P') →
  is-propositional-truncation P f → is-propositional-truncation P' f' →
  type-Prop P ≃ type-Prop P'
equiv-is-propositional-truncation P P' f f' H K =
  equiv-iff-is-prop
    ( is-prop-type-Prop P)
    ( is-prop-type-Prop P')
    ( map-is-propositional-truncation P f H P' f')
    ( map-is-propositional-truncation P' f' K P f)
```

<!-- rosetta-agda-block: proposition-14.1.4-transfer-of-truncation -->

```agda
abstract
  is-ptruncation-is-ptruncation-is-equiv :
    {l1 l2 l3 : Level} {A : Type l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : (type-Prop P → type-Prop P')) →
    is-equiv h → is-propositional-truncation P f →
    is-propositional-truncation P' f'
  is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
    is-propositional-truncation-extension-property P' f'
      ( λ R g →
        ( map-is-propositional-truncation P f is-ptr-f R g) ∘
        ( map-section-is-equiv is-equiv-h))

abstract
  is-ptruncation-is-equiv-is-ptruncation :
    {l1 l2 l3 : Level} {A : Type l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : (type-Prop P → type-Prop P')) →
    is-propositional-truncation P' f' → is-equiv h →
    is-propositional-truncation P f
  is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
    is-propositional-truncation-extension-property P f
      ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)
```
<!-- rosetta-item-end: proposition-14.1.4 -->

## Remark 14.1.5

<!-- rosetta-item: remark-14.1.5 -->

One might be tempted to think that a type is inhabited if and only if it is nonempty.
Recall that a type `A` is nonempty if it satisfies the property `¬¬ A`.
Indeed, the type `¬¬ A` is a proposition, and it comes equipped with a map `A→¬¬ A`.
It is therefore natural to wonder whether the map `A→¬¬ A` satisfies the universal property of the propositional truncation.

Recall that we have shown in Exercise 4.3 that any map `A→¬¬ Q` extends to a map `¬¬ A→¬¬ Q`, as indicated in the diagram
<!-- rosetta-diagram: bc6d1f4223fe; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]
  |
[¬¬ A]---->[¬¬ Q]

Arrows:
- A --unlabeled--> ¬¬ A
- A --unlabeled--> ¬¬ Q
- ¬¬ A --unlabeled--> ¬¬ Q
```
It follows that the natural map
```text
(¬¬ A→¬¬ Q)→ (A→ ¬¬ Q)
```
given by precomposition by `A→¬¬ A` is an equivalence.
However, this only gives us a universal property with respect to doubly negated propositions and there is no way to prove the more general universal property of the propositional truncation for the map `A→¬¬ A`.
In fact, propositional truncations are not guaranteed to exist in Martin Löf’s dependent type theory, the way it is set up in Chapter I.
We will therefore add new rules to the type theory to ensure their existence.

<!-- rosetta-agda-block: remark-14.1.5-double-negation-proposition -->

```agda
is-prop-double-negation :
  {l : Level} {A : Type l} → is-prop (¬¬ A)
is-prop-double-negation = is-prop-neg
```

<!-- rosetta-agda-block: remark-14.1.5-double-negation-universal-property -->

```agda
is-equiv-precomp-double-negation :
  {l1 l2 : Level} (A : Type l1) (Q : Type l2) →
  is-equiv (precomp (double-negation-introduction {P = A}) (¬¬ Q))
is-equiv-precomp-double-negation A Q =
  is-equiv-has-converse-is-prop
    ( is-prop-function-type is-prop-double-negation)
    ( is-prop-function-type is-prop-double-negation)
    ( double-negation-kleisli-map)

equiv-precomp-double-negation :
  {l1 l2 : Level} (A : Type l1) (Q : Type l2) →
  ((¬¬ A) → (¬¬ Q)) ≃ (A → (¬¬ Q))
pr1 (equiv-precomp-double-negation A Q) =
  precomp (double-negation-introduction {P = A}) (¬¬ Q)
pr2 (equiv-precomp-double-negation A Q) =
  is-equiv-precomp-double-negation A Q
```
<!-- rosetta-item-end: remark-14.1.5 -->
