# Section 20.6 Russell's paradox in type theory

```agda
{-# OPTIONS --lossy-unification #-}
module section-20-6-russells-paradox-in-type-theory where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-20-1-the-type-of-well-founded-trees
open import section-20-2-observational-equality-of-w-types
open import section-20-3-functoriality-of-w-types
open import section-20-4-the-elementhood-relation-on-w-types

open import exercise-4-3-double-negation-logic
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-7-product-functor-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-12-7-truncated-products
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
```

Russell’s paradox tells us that there cannot be a set of all sets.
If there were such a set `S`, then we could form the set

```text
R ≔ {x ∈ S| x ∉ x},
```

for which we have `R ∈ R ↔ R ∉ R`, a contradiction.
To reproduce Russell’s paradox in type theory, we first recall a crucial difference between the type theoritic judgment `a : A` and the set theoretic proposition `x ∈ y`.
Although the judgment `a : A` plays a similar role in type theory as the elementhood relation, types and their elements are fundamentally different entities, whereas in Zermelo-Fraenkel set theory there are only sets, and the proposition `x ∈ y` can be formed for any two sets `x` and `y`.
In type theory, there is no relation on the universe that is similar to the elementhood relation.

However, we have seen in Section 20.5 that it is possible to define an elementhood relation on arbitrary W-types.
We will use this elementhood relation on the W-type `W(𝒰, Ty)` to derive a paradox analogous to Russell’s paradox, and we will see that `𝒰` cannot be equivalent to a type in `𝒰`.

The type `W(𝒰, Ty)` possesses a lot of further structure.
In fact, it can be used to encode constructive set theory in type theory.
There is, however, one significant difference with ordinary set theory: the elementhood relation is type-valued.
In other words, there may be many ways in which `x ∈ y` holds.
The type `W(𝒰, Ty)` is therefore also called the type of **multisets**.
It was first studied by Aczel in \[citation: `AczelCZF`\], with refinements in \[citation: `AczelGambinoCZF`\], and in the setting of univalent mathematics it has been studied extensively by Gylterud in \[citation: `GylterudMultisets`\].

## Definition 20.6.1

Consider a `𝒰` with universal type family `Ty`.
We define the type

```text
M_𝒰 ≔ W(𝒰, Ty),
```

and the elements of `M_𝒰` are called **multisets in `𝒰`**.

```agda
𝕍 : (l : Level) → UU (lsuc l)
𝕍 l = 𝕎 (UU l) (λ X → X)
```

We will write

```text
{f(x)| x : A}
```

for the multiset in `𝒰` of the form `tree(A, f)`.
More generally, given an element `t(x_0, …, x_n) : M_𝒰` in context `x_0 : A_0, …, x_n : A_n(x_0, …, x_{n-1})`, where each `A_i` is in `𝒰`, we will write

```text
{t(x_0, …, x_n) | x_0 : A_0, …, x_n : A_n(x_0, …, x_{n-1})}
```

for the multiset in `𝒰` of the form

```text
tree(Σ(x_0 : A_0) ⋯ A_n(x_0, …, x_{n-1}), λ (x_0, …, x_n). t(x_0, …, x_n)).
```

Given a multiset `X ≐ {f(x) | x : A}` in `𝒰`, the **cardinality** of `X` is the type `A`, and the **elements** of `X` are the multisets `f(x)` in `𝒰`, for each `x : A`.

In the notation of multisets, the elementhood relation ` ∈ : M_𝒰 → M_𝒰 → 𝒰⁺` is defined 

```text
(X ∈ {g(y) | y : B}) ≐ Σ(y : B) g(y) = X.
```

In other words, a multiset `X` is in a multiset of the form `{g(y) | y : B}` if and only if `X` comes equipped with an element `y : B` and an identification `g(y) = X`.

```agda
infix 6 _∈-𝕍_ _∉-𝕍_

_∈-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∈-𝕍 Y = X ∈-𝕎 Y

_∉-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∉-𝕍 Y = is-empty (X ∈-𝕍 Y)
```

```agda
comprehension-𝕍 :
  {l : Level} (X : 𝕍 l) (P : shape-𝕎 X → UU l) → 𝕍 l
comprehension-𝕍 X P =
  tree-𝕎 (Σ (shape-𝕎 X) P) (component-𝕎 X ∘ pr1)
```

The W-type of multisets is extensional by Theorem 20.5.2 and the univalence axiom.

Recall from Definition 17.1.3 that for a universe `𝒰`, we say that a type `A` is (essentially) `𝒰`-small if `A` comes equipped with an element of type

```text
is-small_𝒰(A) ≔ Σ(X : 𝒰) A ≃ X.
```

Our goal in this section is to show, via Russell’s paradox, that the universe `𝒰` is not `𝒰`-small, i.e., that there cannot be a type `U : 𝒰` equipped with an equivalence `𝒰 ≃ U`.
We will use a similar condition of smallness for multisets.

## Definition 20.6.2

Let `𝒰` and `𝒱` be universes.
We say that a multiset `{f(x) | x:A}` in `𝒱` **is `𝒰`-small** if the type `A` is `𝒰`-small and if each mulitset `f(x)` in `𝒱` is `𝒰`-small.
In other words, the type family

```text
is-small_{M_𝒰} : M_𝒱 → 𝒱 ⊔ 𝒰⁺
```

is defined recursively by

```text
is-small_{M_𝒰}({f(x) | x : A}) ≔ is-small_𝒰(A) × Π(x : A) is-small_{M_𝒰}(f(x)).
```

```agda
is-small-𝕍-Prop : (l : Level) {l1 : Level} → 𝕍 l1 → Prop (l1 ⊔ lsuc l)
is-small-𝕍-Prop l (tree-𝕎 A α) =
  product-Prop (is-small-Prop l A) (Π-Prop A (λ x → is-small-𝕍-Prop l (α x)))

is-small-𝕍 : (l : Level) {l1 : Level} → 𝕍 l1 → UU (l1 ⊔ lsuc l)
is-small-𝕍 l X = type-Prop (is-small-𝕍-Prop l X)

is-prop-is-small-𝕍 : {l l1 : Level} (X : 𝕍 l1) → is-prop (is-small-𝕍 l X)
is-prop-is-small-𝕍 {l} X = is-prop-type-Prop (is-small-𝕍-Prop l X)
```

We will need quite a few properties of smallness before we can reproduce Russell’s paradox.
We begin with a simple lemma.

## Lemma 20.6.3

Consider a `𝒰`-small multiset `{f(x) | x : A}` in `𝒱`, and let `B` be a family of `𝒰`-small types over `A`.
Then the multiset

```text
{f(x) | x : A, y : B(x)}
```

is again `𝒰`-small.

### Proof
If the multiset `{f(x) | x : A}` is `𝒰`-small, then the type `A` is `𝒰`-small.
By the assumption that `B` is a family of `𝒰`-small types together with the fact that `𝒰`-small types are closed under formation of `Σ`-types, it follows that the type

```text
Σ(x : A) B(x)
```

is `𝒰`-small.
Furthermore, since each `f(x)` is `𝒰`-small, we conclude that the multiset `{f(x) | x : A,y : B(x)}` is `𝒰`-small. ◻

```agda
is-small-comprehension-𝕍 :
  (l : Level) {l1 : Level} {X : 𝕍 l1} {P : shape-𝕎 X → UU l1} →
  is-small-𝕍 l X → ((x : shape-𝕎 X) → is-small l (P x)) →
  is-small-𝕍 l (comprehension-𝕍 X P)
is-small-comprehension-𝕍 l {l1} {tree-𝕎 A α} {P} (pair (pair X e) H) K =
  pair
    ( is-small-Σ (pair X e) K)
    ( λ t → H (pr1 t))
```

The main purpose of the following lemma is to know that the elementhood relation takes values in the `𝒰`-small types, when it is applied to `𝒰`-small multisets.
We will use the univalence axiom to prove this fact.

## Proposition 20.6.4

Consider two univalent universes `𝒰` and `𝒱`, and let `X` and `Y` be `𝒰`-small multisets in `𝒱`.
We make two claims:

1. The type `X = Y` is `𝒰`-small.

2. The type `X ∈ Y` is `𝒰`-small.

### Proof
For the first claim, let `X ≐ {f(x) | x : A}` and let `Y ≐ {g(y) | y : B}`.
The proof is by induction.
Via Theorem 20.2.3 it follows that the type `X=Y` is equivalent to the type

```text
Σ(p : A = B) Π(x : A) f(x) = g(equiv-eq(p)).
```

The type `A = B` is `𝒰`-small because it is equivalent to the type `A ≃ B`, which is `𝒰`-small.
Therefore it suffices to show that the type

```text
Π(x : A) f(x) = g(equiv-eq(p))
```

is `𝒰`-small, for every `p : A = B`.
Here we proceed by identification elimination, and the type `Π(x : A) f(x) = g(x)` is a product of `𝒰`-small types by the induction hypothesis.
This concludes the proof of the first claim.

For the second claim, let `Y ≐ {g(y) | y : B}`.
Then the type

```text
Σ(y : B) g(y) = X
```

is a dependent sum of `𝒰`-small types, indexed by an `𝒰`-small type, which is again `𝒰`-small. ◻

```agda
is-small-eq-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ＝ Y)
is-small-eq-𝕍 l
  {l1} {tree-𝕎 A α} {tree-𝕎 B β} (pair (pair X e) H) (pair (pair Y f) K) =
  is-small-equiv
    ( Eq-𝕎 (tree-𝕎 A α) (tree-𝕎 B β))
    ( equiv-Eq-𝕎-eq (tree-𝕎 A α) (tree-𝕎 B β))
    ( is-small-Σ
      ( is-small-equiv
        ( A ≃ B)
        ( equiv-univalence)
        ( pair
          ( X ≃ Y)
          ( equiv-precomp-equiv (inv-equiv e) Y ∘e equiv-postcomp-equiv f A)))
      ( σ))
  where
  σ : (x : A ＝ B) → is-small l ((z : A) → Eq-𝕎 (α z) (β (tr id x z)))
  σ refl =
    is-small-Π
      ( pair X e)
      ( λ x →
        is-small-equiv
          ( α x ＝ β x)
          ( inv-equiv (equiv-Eq-𝕎-eq (α x) (β x)))
          ( is-small-eq-𝕍 l (H x) (K x)))
```

```agda
is-small-∈-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∈-𝕍 Y)
is-small-∈-𝕍 l {l1} {tree-𝕎 A α} {tree-𝕎 B β} H (pair (pair Y f) K) =
  is-small-Σ
    ( pair Y f)
    ( λ b → is-small-eq-𝕍 l (K b) H)

is-small-∉-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∉-𝕍 Y)
is-small-∉-𝕍 l {l1} {X} {Y} H K =
  is-small-Π
    ( is-small-∈-𝕍 l {l1} {X} {Y} H K)
    ( λ x → Raise l empty)
```

The condition that a multiset `{f(x) | x : A}` in `𝒱` is `𝒰`-small suggests that there is an ‘equivalent’ multiset in `𝒰`.

## Definition 20.6.5

Given two universes `𝒰` and `𝒱`, we define an inclusion function

```text
i : (Σ(X : M_𝒱) is-small_{M_𝒰}(X)) → M_𝒰,
```

of the `𝒰`-small multisets in `𝒱` into the multisets in `𝒰`, inductively by

```text
i({f(x) | x : A}) ≔ {i(f(e⁻¹(y))) | y : B}.
```

for any multiset `{f(x) | x : A}` of which the type `A` is equipped with an equivalence `e : A ≃ B` for some `B` in `𝒰`, and such that the multiset `f(x)` in `𝒱` is `𝒰`-small for each `x : A`.

```agda
resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) → is-small-𝕍 l2 X → 𝕍 l2
resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  tree-𝕎 A'
    ( λ x' → resize-𝕍 (α (map-inv-equiv e x')) (H2 (map-inv-equiv e x')))
```

## Proposition 20.6.6

The inclusion function `i` of `𝒰`-small multisets in `𝒱` into the multisets in `𝒰` satisfies the following properties

1. For each `𝒰`-small multiset `X` in `𝒱`, the multiset `i(X)` in `𝒰` is `𝒱`-small.

2. The induced map

```text
(Σ(X : M_𝒱) is-small_{M_𝒰}(X)) → (Σ(Y : M_𝒰) is-small_{M_𝒱}(Y))
```

is an equivalence.

Consequently, the inclusion function `i` is an embedding.

### Proof
To see that `i({f(x) | x : A})` is `𝒱`-small for each `𝒰`-small multiset `{f(x) | x : A}` in `𝒱`, note that the assumption that `{f(x) | x : A}` is `𝒰`-small gives us an equivalence `e : A ≃ B` and an element `H(x) : is-small_{M_𝒰}(f(x))` for each `x : A`.
The type `B` is the indexing type of `i({f(x) | x : A})`, and `B` is `𝒱`-small because it is equivalent to the type `A` in `𝒱`.
Furthermore, each multiset `i(f(e⁻¹(y)))` is `𝒱`-small by the inductive hypothesis.
This completes the proof of the first claim.

We therefore have inclusion functions

```text
(Σ(X : M_𝒱) is-small_{M_𝒰}(X)) <--i--> (Σ(Y : M_𝒰) is-small_{M_𝒱}(Y))
```

To see that the maps `i` and `i` are mutual inverses, it suffices to show that `i(i(X)) = X`.
This follows by induction from the following calculation, where we assume an equivalence `e : A ≃ B` into a `B` in `𝒰`.

```text
i(i({f(x) | x : A})) ≐ i({i(f(e⁻¹(y))) | y : B})
                     ≐ {i(i(f(e⁻¹(e(x))))) | x : A}
                     = {i(i(f(x))) | x : A}
                     = {f(x) | x : A}.
```

For the last claim, note that we have factored `i` as an equivalence followed by an embedding

```text
(Σ(X : M_𝒱) is-small_{M_𝒰}(X)) --> (Σ(Y : M_𝒰) is-small_{M_𝒱}(Y)) --> M_𝒱
```

and therefore `i` is an embedding. ◻

```agda
is-small-resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) (H : is-small-𝕍 l2 X) →
  is-small-𝕍 l1 (resize-𝕍 X H)
is-small-resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  pair
    ( pair A (inv-equiv e))
    ( λ a' →
      is-small-resize-𝕍
        ( α (map-inv-equiv e a'))
        ( H2 (map-inv-equiv e a')))
```

```agda
resize-𝕍' :
  {l1 l2 : Level} →
  Σ (𝕍 l1) (is-small-𝕍 l2) → Σ (𝕍 l2) (is-small-𝕍 l1)
resize-𝕍' (pair X H) = pair (resize-𝕍 X H) (is-small-resize-𝕍 X H)

abstract
  resize-resize-𝕍 :
    {l1 l2 : Level} {x : 𝕍 l1} (H : is-small-𝕍 l2 x) →
    resize-𝕍 (resize-𝕍 x H) (is-small-resize-𝕍 x H) ＝ x
  resize-resize-𝕍 {x = tree-𝕎 A α} ((A' , e) , H) =
    eq-Eq-𝕎
      ( resize-𝕍
        ( resize-𝕍 (tree-𝕎 A α) ((A' , e) , H))
        ( is-small-resize-𝕍 (tree-𝕎 A α) ((A' , e) , H)))
      ( tree-𝕎 A α)
      ( pair
        ( refl)
        ( λ z →
          Eq-𝕎-eq
            ( resize-𝕍
              ( resize-𝕍
                ( α (map-inv-equiv e (map-equiv e z)))
                ( H (map-inv-equiv e (map-equiv e z))))
              ( is-small-resize-𝕍
                ( α (map-inv-equiv e (map-equiv e z)))
                ( H (map-inv-equiv e (map-equiv e z)))))
            ( α z)
            ( ( ap
                ( λ t →
                  resize-𝕍
                    ( resize-𝕍 (α t) (H t))
                    ( is-small-resize-𝕍 (α t) (H t)))
                ( is-retraction-map-inv-equiv e z)) ∙
              ( resize-resize-𝕍 (H z)))))

abstract
  resize-resize-𝕍' :
    {l1 l2 : Level} → (resize-𝕍' {l2} {l1} ∘ resize-𝕍' {l1} {l2}) ~ id
  resize-resize-𝕍' {l1} {l2} (pair X H) =
    eq-type-subtype
      ( is-small-𝕍-Prop l2)
      ( resize-resize-𝕍 H)

is-equiv-resize-𝕍' :
  {l1 l2 : Level} → is-equiv (resize-𝕍' {l1} {l2})
is-equiv-resize-𝕍' {l1} {l2} =
  is-equiv-is-invertible
    ( resize-𝕍' {l2} {l1})
    ( resize-resize-𝕍')
    ( resize-resize-𝕍')

equiv-resize-𝕍' :
  {l1 l2 : Level} → Σ (𝕍 l1) (is-small-𝕍 l2) ≃ Σ (𝕍 l2) (is-small-𝕍 l1)
equiv-resize-𝕍' {l1} {l2} = pair resize-𝕍' is-equiv-resize-𝕍'
```

```agda
eq-resize-𝕍 :
  {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
  (x ＝ y) ≃ (resize-𝕍 x H ＝ resize-𝕍 y K)
eq-resize-𝕍 {l1} {l2} H K =
  ( extensionality-type-subtype'
    ( is-small-𝕍-Prop l1)
    ( resize-𝕍' (pair _ H))
    ( resize-𝕍' (pair _ K))) ∘e
  ( ( equiv-ap (equiv-resize-𝕍') (pair _ H) (pair _ K)) ∘e
    ( inv-equiv
      ( extensionality-type-subtype'
        ( is-small-𝕍-Prop l2)
        ( pair _ H)
        ( pair _ K))))
```

Furthermore, the embedding `i` induces equivalences on the elementhood relation on multisets.

## Proposition 20.6.7

Consider a multiset `X` in `𝒰` and a multiset `Y` in `𝒱`.
Furthermore, suppose that `X` is `𝒱`-small and that `Y` is `𝒰`-small.
Then we have

```text
(i(X) ∈ Y) ≃ (X ∈ i(Y)).
```

### Proof
Let `X ≐ {f(x) | x : A}` and `Y ≐ {g(y) | y : B}`.
By the assumption that `Y` is `𝒰`-small we have an equivalence `e : B ≃ B'` to a type `B'` in `𝒰`.
Then we have the equivalences

```text
i(X) ∈ {g(y) | y : B} ≐ Σ(y : B) g(y) = i(X)
                      ≃ Σ(y : B) i(g(y)) = X
                      ≃ Σ(y' : B') i(g(e⁻¹(y'))) = X
                      ≐ X ∈ i(Y).
```

◻

<!-- This agda block does not perfectly match the natural language statement. -->
```agda
abstract
  equiv-elementhood-resize-𝕍 :
    {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
    (x ∈-𝕍 y) ≃ (resize-𝕍 x H ∈-𝕍 resize-𝕍 y K)
  equiv-elementhood-resize-𝕍 {x = X} {tree-𝕎 B β} H (pair (pair B' e) K) =
    equiv-Σ
      ( λ y' →
        ( component-𝕎 (resize-𝕍 (tree-𝕎 B β) (pair (pair B' e) K)) y') ＝
        ( resize-𝕍 X H))
      ( e)
      ( λ b →
        ( equiv-concat
          ( ap
            ( λ t → resize-𝕍 (β t) (K t))
            ( is-retraction-map-inv-equiv e b))
          ( resize-𝕍 X H)) ∘e
        ( eq-resize-𝕍 (K b) H))
```

We are now almost in position to reproduce Russell’s paradox.
We will need one more ingredient: the universal tree, i.e., the multiset of all multisets in `𝒰`.

## Definition 20.6.8

Let `𝒰` be a universe.
Then we define the **universal tree** `Y_𝒰` to be the multiset

```text
Y_𝒰 := {i(X) | X : M_𝒰}
```

in `𝒰⁺`, where `i : M_𝒰 → M_{𝒰⁺}` is the inclusion of the multisets in `𝒰` to the multisets in `𝒰⁺` given by the fact that each multiset in `𝒰` is `𝒰⁺`-small.

```agda
is-small-multiset-𝕍 :
  {l1 l2 : Level} →
  ((A : UU l1) → is-small l2 A) → (X : 𝕍 l1) → is-small-𝕍 l2 X
is-small-multiset-𝕍 {l1} {l2} H (tree-𝕎 A α) =
  pair (H A) (λ x → is-small-multiset-𝕍 H (α x))
```

```agda
universal-multiset-𝕍 : (l : Level) → 𝕍 (lsuc l)
universal-multiset-𝕍 l =
  tree-𝕎
    ( 𝕍 l)
    ( λ X → resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
```

## Proposition 20.6.9

Consider two universes `𝒰` and `𝒱`, and suppose that `𝒰` as well as each `X : 𝒰` are `𝒱`-small.
Then the universal tree `Y_𝒰` is also `𝒱`-small.

### Proof
To show that the universal tree `{i(X) | X : M_𝒰}` is `𝒱`-small, we first have to show that the type `M_𝒰` is `𝒱`-small.
This follows from the more general fact that the subuniverse of `𝒱`-small types is closed under the formation of W-types.
Indeed, if a type `A` is `𝒱`-small, and if `B(x)` is `𝒱`-small for each `x : A`, then we have an equivalence `α : A ≃ A'` to a type `A'` in `𝒱`, and for each `x' : A'` we have an equivalence `B(α⁻¹(x'))≃ B'(x')` in `𝒱`.
These equivalences induce an equivalence

```text
W(A, B) ≃ W(A', B')
```

into the type `W(A', B')`, which is in `𝒱`.
This concludes the proof that `M_𝒰` is `𝒱`-small.

It remains to show that the multiset `i(X)` in `𝒰⁺` is `𝒱`-small, for each `X : M_𝒰`.
Equivalently, we have to show that each multiset `X` in `𝒰` is `𝒱`-small.
This follows by recursion: given a multiset `{f(x) | x : A}`, the type `A` is `𝒱`-small by assumption, and the multiset `f(x)` is `𝒱`-small by the induction hypothesis. ◻

```agda
is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)
```

```agda
is-small-universal-multiset-𝕍 :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕍 l (universal-multiset-𝕍 l1)
is-small-universal-multiset-𝕍 l {l1} (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      ( equiv-𝕎
        ( λ u → type-is-small (H (map-inv-equiv e u)))
        ( e)
        ( λ X →
          tr
            ( λ t → X ≃ pr1 (H t))
            ( inv (is-retraction-map-inv-equiv e X))
            ( pr2 (H X)))))
    ( f)
    where
    f :
      (X : 𝕍 l1) →
      is-small-𝕍 l (resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
    f (tree-𝕎 A α) =
      pair
        ( pair
          ( type-is-small (H A))
          ( equiv-is-small (H A) ∘e inv-equiv (compute-raise (lsuc l1) A)))
        ( λ x → f (α (map-inv-raise x)))
```

We are finally ready to employ **Russell’s paradox** to prove that a univalent universe cannot be equivalent to any type it contains.

## Theorem 20.6.10

Consider a univalent universe `𝒰`.
Then `𝒰` cannot be `𝒰`-small.

### Proof
Suppose that `𝒰` is `𝒰`-small, and consider the multiset

```text
R ≔ {i(X) | X : M_𝒰, H : X ∉ X}
```

in `𝒰⁺`, where `i : M_𝒰 → M_{𝒰⁺}` is the inclusion of the multisets in `𝒰` to the multisets in `𝒰⁺` given by the fact that each multiset in `𝒰` is `𝒰⁺`-small.

First, we note that `R` is `𝒰`-small.
This follows from Lemma 20.6.3, using the fact that the universal tree `{i(X) | X : M_𝒰}` is `𝒰`-small by Proposition 20.6.9, and the fact that `X ∈ X` is `𝒰`-small by Proposition 20.6.4.

Since `R` is `𝒰`-small, there is a multiset `R' : M_𝒰` such that `i(R') = R`.
Now it follows that

```text
R ∈ R ≃ Σ(X : M_𝒰) Σ(H : X ∉ X) i(X) = R
      ≃ Σ(X : M_𝒰) Σ(H : X ∉ X) X = R'
      ≃ R' ∉ R'
      ≃ R ∉ R.
```

In the second step we used Proposition 20.6.6, where we showed that `i` is an embedding, and in the last step we used Proposition 20.6.7.
Now we obtain a contradiction, because it follows from Exercise 4.3 that no type is (logically) equivalent to its own negation. ◻

```agda
Russell : (l : Level) → 𝕍 (lsuc l)
Russell l =
  comprehension-𝕍
    ( universal-multiset-𝕍 l)
    ( λ X → X ∉-𝕍 X)
```

```agda
module _
  {l1 l2 : Level} (H : is-small-universe l2 l1)
  where

  is-small-Russell : is-small-𝕍 l2 (Russell l1)
  is-small-Russell =
    is-small-comprehension-𝕍 l2
      { lsuc l1}
      { universal-multiset-𝕍 l1}
      { λ X → X ∉-𝕍 X}
      ( is-small-universal-multiset-𝕍 l2 H)
      ( λ X → is-small-∉-𝕍 l2 (K X) (K X))
    where
    K = is-small-multiset-𝕍 (pr2 H)

  resize-Russell : 𝕍 l2
  resize-Russell = resize-𝕍 (Russell l1) (is-small-Russell)

  is-small-resize-Russell :
    is-small-𝕍 (lsuc l1) (resize-Russell)
  is-small-resize-Russell =
    is-small-resize-𝕍 (Russell l1) (is-small-Russell)

  equiv-Russell-in-Russell :
    (Russell l1 ∈-𝕍 Russell l1) ≃ (resize-Russell ∈-𝕍 resize-Russell)
  equiv-Russell-in-Russell =
    equiv-elementhood-resize-𝕍 (is-small-Russell) (is-small-Russell)
```

```agda
module _
  {l : Level} (H : is-small l (UU l))
  where

  equiv-in-notin-Russell :
    (Russell l ∈-𝕍 Russell l) ≃ (Russell l ∉-𝕍 Russell l)
  equiv-in-notin-Russell =
    ( equiv-precomp (equiv-Russell-in-Russell K) empty) ∘e
    ( left-unit-law-Σ-is-contr
      { B = (λ t → (pr1 t) ∉-𝕍 (pr1 t))}
      ( is-torsorial-Id' (resize-Russell K))
      ( resize-Russell K , refl)) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot
      ( λ t →
        ( commutative-product) ∘e
        ( equiv-product-right
          ( inv-equiv
            ( ( equiv-concat' _ (resize-resize-𝕍 (is-small-Russell K))) ∘e
              ( eq-resize-𝕍
                ( is-small-multiset-𝕍 is-small-lsuc t)
                ( is-small-resize-Russell K))))))) ∘e
    ( associative-Σ)
    where
      K : is-small-universe l l
      K = (H , (λ X → (X , id-equiv)))

  iff-in-notin-Russell :
    (Russell l ∈-𝕍 Russell l) ↔ (Russell l ∉-𝕍 Russell l)
  iff-in-notin-Russell =
    iff-equiv equiv-in-notin-Russell

  paradox-Russell : empty
  paradox-Russell =
    no-fixed-points-neg (Russell l ∈-𝕍 Russell l) iff-in-notin-Russell
```