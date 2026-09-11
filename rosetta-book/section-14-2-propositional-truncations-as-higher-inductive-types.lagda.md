# Section 14.2 Propositional truncations as higher inductive types

```agda
module section-14-2-propositional-truncations-as-higher-inductive-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-11-1-families-of-equivalences
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import section-14-1-the-universal-property-of-propositional-truncations
open import exercise-10-3-contractible-equivalences
open import section-11-4-embeddings
open import exercise-9-1-groupoid-operations-equivalences
```

<!-- rosetta-item: section-14.2 -->

We have given a specification of the propositional truncation of a type `A`, and we have seen that this specification by a universal property determines the propositional truncation up to equivalence if it exists.
However, the propositional truncation is not guaranteed to exist, so we will add new rules to the type theory that ensure that any type has a propositional truncation.
We do this by presenting the propositional truncation of a type `A` as a higher inductive type.
The propositional truncation `‖A‖` of a type `A` was one of the first examples of a higher inductive type, along with the circle, which we will discuss in Chapters 21 and 22.

The idea of higher inductive types is similar to the idea of ordinary inductive types, with the added feature that constructors of higher inductive types can also be used to generate *identifications*.
In other words, higher inductive types may be specified by two kinds of constructors:

1.  The *point constructors* are used to generate elements of the higher inductive types.

2.  The *path constructors* are used to generate identifications between elements of the higher inductive type.

The induction principle of the higher inductive type then tells us how to construct sections of families over it.
The rules for higher inductive types therefore come in four sets, just as the rules for ordinary inductive types in Chapter 4: the formation rule, the constructors, the induction principle, and the computation rules.

### The formation rules and the constructors

<!-- rosetta-item: subheading-14.2-the-formation-rules-and-the-constructors -->

The formation rule of the propositional truncation postulates that for every type `A` we can form the propositional truncation of `A`.
The formation rule is therefore as follows:

<!-- rosetta-proof-tree: f37dfce44a83; review: pending -->

*Proof tree (automatic faithful draft).*

```text
 Γ⊢ A type
───────────
Γ⊢ ‖A‖ type
```

Furthermore, we will assume that all universes are closed under propositional truncations.
In other words, for any universe `𝒰` we will assume the rules

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 19605e39c500; review: pending -->

*Proof tree (automatic faithful draft).*

```text

───────────
X:𝒰⊢ ‖X‖̌:𝒰
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 5c8275c99809; review: pending -->

*Proof tree (automatic faithful draft).*

```text

────────────────────────
X:𝒰⊢ T(‖X‖̌)≐‖T(X)‖ type
```

### Assumed proposition-level formation in Agda universes

<!-- rosetta-agda-block: section-14.2-assumed-formation -->

```agda
postulate
  type-trunc-Prop : {l : Level} → Type l → Type l

║_║₋₁ : {l : Level} → Type l → Type l
║_║₋₁ = type-trunc-Prop
```


The constructors of a (higher) inductive type tell what structure the type comes equipped with.
In the case of a higher inductive type there may be point constructors and path constructors.
The point constructors generate elements of the higher inductive type, and the path constructors generate identifications between those elements.
In the case of the propositional truncation, there is one point constructor and one path constructor:
```text
η : A → ‖A‖
α : Π(x,y:‖A‖) x=y.
```

### Assumed point constructor

<!-- rosetta-agda-block: section-14.2-assumed-point-constructor -->

```agda
postulate
  unit-trunc-Prop : {l : Level} {A : Type l} → A → ║ A ║₋₁
```

The point constructor `η` is sometimes called the **unit** of the propositional truncation.
It gives us that any element of `A` also generates an element of `‖A‖`.
The path constructor `α` simply identifies any two elements of `‖A‖`.
Therefore it follows immediately that `‖A‖` is a proposition.

### Assumed path constructor

<!-- rosetta-agda-block: section-14.2-assumed-path-constructor -->

```agda
postulate
  all-elements-equal-type-trunc-Prop :
    {l : Level} {A : Type l} → all-elements-equal (║ A ║₋₁)
```


## Lemma 14.2.1

<!-- rosetta-item: lemma-14.2.1 -->

For any type `A`, the type `‖A‖` is a proposition.`□`

<!-- rosetta-agda-block: lemma-14.2.1-truncation-is-proposition -->

```agda
is-prop-type-trunc-Prop : {l : Level} {A : Type l} → is-prop (║ A ║₋₁)
is-prop-type-trunc-Prop =
  is-prop-all-elements-equal all-elements-equal-type-trunc-Prop
```

<!-- rosetta-agda-block: lemma-14.2.1-bundled-truncation -->

```agda
trunc-Prop : {l : Level} → Type l → Prop l
pr1 (trunc-Prop A) = type-trunc-Prop A
pr2 (trunc-Prop A) = is-prop-type-trunc-Prop
```
<!-- rosetta-item-end: lemma-14.2.1 -->

### The induction principle and computation rules

<!-- rosetta-item: subheading-14.2-the-induction-principle-and-computation-rules -->

The induction principle for the propositional truncation tells us how to construct dependent functions
```text
h:Π(t:‖A‖) Q(t).
```
The induction principle will imply that such a dependent function `h` is entirely determined by its behavior on the constructors of `‖A‖`.
The type `‖A‖` has two constructors: a point constructor `η` and a path constructor `α`, so we have two cases to consider:

1.  Applying `h` to points of the form `η(a)` gives us a dependent function
```text
h∘ η : Π(a:A) Q(η(a)).
```
The induction principle of `‖A‖` has therefore the requirement that we can construct
```text
f:Π(a:A) Q(η(a))
```

2.  To apply `h` to the paths `α(x,y)`, we need to use the dependent action on paths from Definition 5.4.2.
For each `x,y:‖A‖` we obtain an identification
```text
apd_{h}(α(x,y)):tr_Q(α(x,y),h(x))=h(y)
```
    in the type `Q(y)`. Note, however, that `h(x)` and `h(y)` are not determined by our choice of `f:Π(a:A) Q(η(a))`. The second requirement of the induction principle of `‖A‖` is therefore that, no matter what values `h` takes, they must always be related via the dependent action on paths of `h`. This second requirement is therefore that
```text
tr_P(α(x,y),u)=v
```
    for any `u:Q(x)` and `v:Q(y)`.

## Definition 14.2.2

<!-- rosetta-item: definition-14.2.2 -->

The **induction principle** of the propositional truncation `‖A‖` of `A` asserts that for any family `Q` of types over `‖A‖`, if we have
```text
f:Π(a:A) Q(η(a))
```
and if we can construct identifications
```text
tr_Q(α(x,y),u)=v
```
for any `u:Q(x)`, `v:Q(y)` and any `x,y:‖A‖`, then we obtain a dependent function
```text
h:Π(t:‖A‖) Q(t)
```
equipped with a homotopy `h∘η~ f`.

<!-- rosetta-agda-block: definition-14.2.2-higher-inductive-specification -->

```agda
case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : Type l1}
  ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
  ( B : type-Prop P → Type l) → Type (l ⊔ l2)
case-paths-induction-principle-propositional-truncation P α f B =
  (p q : type-Prop P) (x : B p) (y : B q) → tr B (α p q) x ＝ y

induction-principle-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : Type l1}
  (P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
  Type (lsuc l ⊔ l1 ⊔ l2)
induction-principle-propositional-truncation l {l1} {l2} {A} P α f =
  ( B : type-Prop P → Type l) →
  ( g : (x : A) → (B (f x))) →
  ( β : case-paths-induction-principle-propositional-truncation P α f B) →
  Σ ((p : type-Prop P) → B p) (λ h → (x : A) → h (f x) ＝ g x)
```

### Assumed higher-inductive elimination and its computation homotopy

<!-- rosetta-agda-block: definition-14.2.2-assumed-induction -->

```agda
postulate
  induction-trunc-Prop :
    {l l1 : Level} {A : Type l1} →
    induction-principle-propositional-truncation l
      (trunc-Prop A) all-elements-equal-type-trunc-Prop unit-trunc-Prop
```

<!-- rosetta-agda-block: definition-14.2.2-induction-and-computation -->

```agda
ind-trunc-Prop' :
  {l l1 : Level} {A : Type l1} (P : ║ A ║₋₁ → Type l)
  (f : (x : A) → P (unit-trunc-Prop x))
  (H : (x y : ║ A ║₋₁) (u : P x) (v : P y) →
    tr P (all-elements-equal-type-trunc-Prop x y) u ＝ v) →
  (x : ║ A ║₋₁) → P x
ind-trunc-Prop' P f H = pr1 (induction-trunc-Prop P f H)

compute-ind-trunc-Prop' :
  {l l1 : Level} {A : Type l1} (P : ║ A ║₋₁ → Type l)
  (f : (x : A) → P (unit-trunc-Prop x))
  (H : (x y : ║ A ║₋₁) (u : P x) (v : P y) →
    tr P (all-elements-equal-type-trunc-Prop x y) u ＝ v) →
  (ind-trunc-Prop' P f H ∘ unit-trunc-Prop) ~ f
compute-ind-trunc-Prop' P f H = pr2 (induction-trunc-Prop P f H)
```
<!-- rosetta-item-end: definition-14.2.2 -->

## Remark 14.2.3

<!-- rosetta-item: remark-14.2.3 -->

In fact, a family `Q` over `‖A‖` satisfies the second requirement in the induction principle of the propositional truncation if and only if `Q` is a family of propositions.
To see this, simply note that transporting along `α(x,y)` is an embedding.
Therefore we have
```text
(tr_Q(α(x,y),u)=tr_Q(α(x,y),v))≃ (u=v)
```
for any `u,v:Q(x)`.
By assumption, there is an identification on the left hand side, so any two elements `u` and `v` in `Q(x)` are equal.

Since the induction principle of the propositional truncation is only applicable to families of propositions over `‖A‖`, it also follows that there are no interesting computation rules to state: any identification in a proposition just holds.

<!-- rosetta-agda-block: remark-14.2.3-path-clause-propositions -->

```agda
abstract
  is-prop-case-paths-induction-principle-propositional-truncation :
    { l : Level} {l1 l2 : Level} {A : Type l1}
    ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
    ( B : type-Prop P → Type l) →
    case-paths-induction-principle-propositional-truncation P α f B →
    ( p : type-Prop P) → is-prop (B p)
  is-prop-case-paths-induction-principle-propositional-truncation P α f B β p =
    is-prop-is-proof-irrelevant (λ x → pair (tr B (α p p) x) (β p p x))

  case-paths-induction-principle-propositional-truncation-is-prop :
    { l : Level} {l1 l2 : Level} {A : Type l1}
    ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
    ( B : type-Prop P → Type l) →
    ( (p : type-Prop P) → is-prop (B p)) →
    case-paths-induction-principle-propositional-truncation P α f B
  case-paths-induction-principle-propositional-truncation-is-prop
    P α f B is-prop-B p q x y =
    eq-is-prop (is-prop-B q)
```

<!-- rosetta-agda-block: remark-14.2.3-transport-identifications -->

```agda
is-emb-tr-trunc-Prop :
  {l1 l2 : Level} {A : Type l1} (P : ║ A ║₋₁ → Type l2)
  (x y : ║ A ║₋₁) → is-emb (tr P (all-elements-equal-type-trunc-Prop x y))
is-emb-tr-trunc-Prop P x y =
  is-emb-is-equiv (is-equiv-tr P (all-elements-equal-type-trunc-Prop x y))

equiv-identifications-tr-trunc-Prop :
  {l1 l2 : Level} {A : Type l1} (P : ║ A ║₋₁ → Type l2)
  (x y : ║ A ║₋₁) (u v : P x) →
  (tr P (all-elements-equal-type-trunc-Prop x y) u ＝
    tr P (all-elements-equal-type-trunc-Prop x y) v) ≃ (u ＝ v)
pr1 (equiv-identifications-tr-trunc-Prop P x y u v) =
  map-section-is-equiv (is-emb-tr-trunc-Prop P x y u v)
pr2 (equiv-identifications-tr-trunc-Prop P x y u v) =
  is-equiv-map-section-is-equiv (is-emb-tr-trunc-Prop P x y u v)
```

<!-- rosetta-agda-block: remark-14.2.3-propositional-induction -->

```agda
module _
  {l l1 : Level} {A : Type l1} (P : ║ A ║₋₁ → Prop l)
  where

  abstract
    ind-trunc-Prop :
      ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
      (( y : ║ A ║₋₁) → type-Prop (P y))
    ind-trunc-Prop f =
      ind-trunc-Prop' (type-Prop ∘ P) f
        ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y)))

    compute-ind-trunc-Prop :
        is-section (precomp-Π unit-trunc-Prop (type-Prop ∘ P)) (ind-trunc-Prop)
    compute-ind-trunc-Prop h =
      eq-is-prop (is-prop-Π (λ x → is-prop-type-Prop (P (unit-trunc-Prop x))))
```
<!-- rosetta-item-end: remark-14.2.3 -->

### The universal property

<!-- rosetta-item: subheading-14.2-the-universal-property -->

We have now completed the description of the propositional truncation as a higher inductive type, so it is time to show that it meets the specification we gave for the propositional truncations.
In other words, we have to show that the map `η:A→‖A‖` satisfies the universal property of the propositional truncation.

## Theorem 14.2.4

<!-- rosetta-item: theorem-14.2.4 -->

The map `η:A→‖A‖` satisfies the universal property of the propositional truncation.

### Proof

<!-- rosetta-item: subheading-14.2-proof -->

*Proof.* In order to prove that `η:A→‖A‖` satisfies the universal property of the propositional truncation of `A`, it suffices to construct a map
```text
(A→ Q)→ (‖A‖→ Q)
```
for any proposition `Q`.
Consider a map `f:A→ Q`.
Then we will construct a function `‖A‖→ Q` by the induction principle of the propositional truncation.
We have to provide a function `A→ Q`, which we have assumed already, and we have to show that
```text
tr_{λ x. Q}(α(x,y),u)=v.
```
for any `u,v:Q` and any `x,y:‖A‖`.
However, we have such identifications by the assumption that `Q` is a proposition, so the proof is complete. ◻

<!-- rosetta-agda-block: theorem-14.2.4-recursion -->

```agda
module _
  {l l1 : Level} {A : Type l1} (P : Prop l)
  where

  abstract
    rec-trunc-Prop :
      (A → type-Prop P) → (║ A ║₋₁ → type-Prop P)
    rec-trunc-Prop = ind-trunc-Prop (λ _ → P)

    compute-rec-trunc-Prop :
      is-section (precomp unit-trunc-Prop (type-Prop P)) (rec-trunc-Prop)
    compute-rec-trunc-Prop = compute-ind-trunc-Prop (λ _ → P)
```

<!-- rosetta-agda-block: theorem-14.2.4-universal-property -->

```agda
abstract
  is-propositional-truncation-trunc-Prop :
    {l : Level} (A : Type l) →
    is-propositional-truncation (trunc-Prop A) unit-trunc-Prop
  is-propositional-truncation-trunc-Prop A =
    is-propositional-truncation-extension-property
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( λ Q → ind-trunc-Prop (λ x → Q))
```

<!-- rosetta-agda-block: theorem-14.2.4-unique-extensions -->

```agda
abstract
  universal-property-trunc-Prop :
    {l : Level} (A : Type l) →
    universal-property-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  universal-property-trunc-Prop A =
    universal-property-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

abstract
  map-universal-property-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} (P : Prop l2) →
    (A → type-Prop P) → (║ A ║₋₁ → type-Prop P)
  map-universal-property-trunc-Prop {A = A} P f =
    map-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)
      ( P)
      ( f)
```
<!-- rosetta-item-end: theorem-14.2.4 -->

One simple application of the universal property of the propositional truncation is that `‖_‖` acts on functions in a functorial way.

## Proposition 14.2.5

<!-- rosetta-item: proposition-14.2.5 -->

There is a map
```text
‖_‖:(A→ B)→ (‖A‖→‖B‖)
```
for any two types `A` and `B`, such that
```text
‖id‖ ~ id
‖g∘ f‖ ~ ‖g‖∘‖f‖.
```

### Proof

<!-- rosetta-item: subheading-14.2-proof-2 -->

*Proof.* For any `f:A→ B`, the map `‖f‖:‖A‖→‖B‖` is defined to be the unique extension
<!-- rosetta-diagram: 5d4d1dc58188; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [A] ----> [B]
  |         |
[‖A‖]---->[‖B‖]

Arrows:
- A --η--> ‖A‖
- A --f--> B
- B --η--> ‖B‖
- ‖A‖ --‖f‖--> ‖B‖
```
To see that `‖_‖` preserves identity maps and compositions, simply note that `id[‖A‖]` is an extension of `id[A]`, and that `‖g‖∘‖f‖` is an extension of `g∘ f`.
Hence the homotopies are obtained by uniqueness. ◻

<!-- rosetta-agda-block: proposition-14.2.5-functorial-map -->

```agda
abstract
  unique-map-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) →
    is-contr
      ( Σ ( (║ A ║₋₁ → ║ B ║₋₁))
          ( λ h → (h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)))
  unique-map-trunc-Prop {l1} {l2} {A} {B} f =
    is-contr-equiv'
      ( Σ (║ A ║₋₁ → ║ B ║₋₁)
        (λ h → (h ∘ unit-trunc-Prop) ＝ (unit-trunc-Prop ∘ f)))
      ( equiv-tot (λ _ → equiv-funext))
      ( universal-property-trunc-Prop A (trunc-Prop B) (unit-trunc-Prop ∘ f))

abstract
  map-trunc-Prop :
    {l1 l2 : Level} {A : Type l1} {B : Type l2} →
    (A → B) → (║ A ║₋₁ → ║ B ║₋₁)
  map-trunc-Prop f =
    pr1 (center (unique-map-trunc-Prop f))
```

<!-- rosetta-agda-block: proposition-14.2.5-extension-homotopy-and-uniqueness -->

```agda
abstract
  htpy-map-trunc-Prop :
    { l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) →
    ( (map-trunc-Prop f) ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)
  htpy-map-trunc-Prop f =
    pr2 (center (unique-map-trunc-Prop f))

  htpy-uniqueness-map-trunc-Prop :
    { l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) →
    ( h : (║ A ║₋₁ → ║ B ║₋₁)) →
    ( ( h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)) →
    (map-trunc-Prop f) ~ h
  htpy-uniqueness-map-trunc-Prop f h H =
    htpy-eq (ap pr1 (contraction (unique-map-trunc-Prop f) (pair h H)))
```

<!-- rosetta-agda-block: proposition-14.2.5-identity-law -->

```agda
abstract
  id-map-trunc-Prop :
    { l1 : Level} {A : Type l1} → map-trunc-Prop (id {A = A}) ~ id
  id-map-trunc-Prop {l1} {A} =
    htpy-uniqueness-map-trunc-Prop id id refl-htpy
```

<!-- rosetta-agda-block: proposition-14.2.5-composition-law -->

```agda
abstract
  preserves-comp-map-trunc-Prop :
    { l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3}
    ( g : B → C) (f : A → B) →
    ( map-trunc-Prop (g ∘ f)) ~
    ( (map-trunc-Prop g) ∘ (map-trunc-Prop f))
  preserves-comp-map-trunc-Prop g f =
    htpy-uniqueness-map-trunc-Prop
      ( g ∘ f)
      ( (map-trunc-Prop g) ∘ (map-trunc-Prop f))
      ( ( (map-trunc-Prop g) ·l (htpy-map-trunc-Prop f)) ∙h
        ( ( htpy-map-trunc-Prop g) ·r f))
```
<!-- rosetta-item-end: proposition-14.2.5 -->
