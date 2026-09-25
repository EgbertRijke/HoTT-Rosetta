# Section 17.1 Equivalent forms of the univalence axiom

```agda
module section-17-1-equivalent-forms-of-the-univalence-axiom where

open import universe-levels
open import section-2-2-ordinary-function-types
open import exercise-2-3-constant-maps
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import exercise-12-8-retracts-of-truncated-types
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
```

By the fundamental theorem of identity types, Theorem 11.2.2, it is immediate that the univalence axiom comes in three equivalent forms.

## Theorem 17.1.1

Consider a universe `𝒰`.
The following are equivalent:

1. The universe `𝒰` is **univalent**: For any two types `A, B : 𝒰`, the map

   ```text
     equiv-eq : (A = B) → (A ≃ B)
   ```
    
   given by `equiv-eq(refl) ≔ id`, is an equivalence.

2. The type

   ```text
     Σ(B : 𝒰) A ≃ B
   ```
    
   is contractible for each `A : 𝒰`.

3. For any type `A : 𝒰`, the family of types `A ≃ X` indexed by `X : 𝒰` is an identity system on `𝒰`.
   In other words, the universe `𝒰` satisfies the principle of **equivalence induction**: For every `A : 𝒰` and for every type family of types `P(X,e)` indexed by `X : 𝒰` and `e : A ≃ X`, the map

   ```text
     (Π(X : 𝒰) Π(e : A ≃ X) P(X,e)) → P(A,id)
   ```
    
   given by `f ↦ f(A,id)` has a section.

### Proof

The claim is a special case of Theorem 11.2.2, the fundamental theorem of identity types. ◻

```agda
module _
  {l : Level}
  where

  equiv-eq : {A B : UU l} → A ＝ B → A ≃ B
  equiv-eq = equiv-tr id

  map-eq : {A B : UU l} → A ＝ B → A → B
  map-eq = map-equiv ∘ equiv-eq

  map-inv-eq : {A B : UU l} → A ＝ B → B → A
  map-inv-eq = map-eq ∘ inv

  compute-equiv-eq-refl :
    {A : UU l} → equiv-eq (refl {x = A}) ＝ id-equiv
  compute-equiv-eq-refl = refl

instance-univalence : {l : Level} (A B : UU l) → UU (lsuc l)
instance-univalence A B = is-equiv (equiv-eq {A = A} {B = B})

based-univalence-axiom : {l : Level} (A : UU l) → UU (lsuc l)
based-univalence-axiom {l} A = (B : UU l) → instance-univalence A B

univalence-axiom-Level : (l : Level) → UU (lsuc l)
univalence-axiom-Level l = (A B : UU l) → instance-univalence A B

univalence-axiom : UUω
univalence-axiom = {l : Level} → univalence-axiom-Level l

abstract
  is-torsorial-equiv-based-univalence :
    {l : Level} (A : UU l) →
    based-univalence-axiom A → is-torsorial (λ (B : UU l) → A ≃ B)
  is-torsorial-equiv-based-univalence A UA =
    fundamental-theorem-id' (λ B → equiv-eq) UA

abstract
  based-univalence-is-torsorial-equiv :
    {l : Level} (A : UU l) →
    is-torsorial (λ (B : UU l) → A ≃ B) → based-univalence-axiom A
  based-univalence-is-torsorial-equiv A c =
    fundamental-theorem-id c (λ B → equiv-eq)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  where

  compute-equiv-eq-ap :
    (p : x ＝ y) → equiv-eq (ap B p) ＝ equiv-tr B p
  compute-equiv-eq-ap refl = refl

  compute-map-eq-ap :
    (p : x ＝ y) → map-eq (ap B p) ＝ tr B p
  compute-map-eq-ap p = ap map-equiv (compute-equiv-eq-ap p)
```

One way to see that the univalence axiom is plausible, is by observing that all type constructors preserve equivalences.
For example, in Theorem 11.1.6 we showed that for any type family `B` over `A` and any type family `B'` over `A'`, if we have an equivalence `e : A ≃ A'` and family of equivalences `f : Π(x : A) B(x) ≃ B'(e(x))`, then we obtain an equivalence

```text
  (Σ(x : A) B(x)) ≃ (Σ(x' : A') B'(x')).
```

Under the same assumptions, we showed in Exercise 13.12 that we obtain an equivalence

```text
  (Π(x : A) B(x)) ≃ (Π(x' : A') B'(x')).
```

Furthermore, for any two elements `x, y : A` any equivalence `e : A ≃ A'` induces an equivalence `(x = y) ≃ (e(x) = e(y))` by Theorem 11.4.2.
In other words, all the standard type formers within a universe `𝒰` are *equivalence invariant*.
Since identity types are not assumed to be propositions, we have the possibility to postulate the univalence axiom.

## Axiom 17.1.2

We will assume that all the universes generated by Postulate 6.2.1 are univalent.
Given a univalent universe `𝒰`, we will write `eq-equiv` for the inverse of `equiv-eq`.

```agda
module _
  {l : Level} {A B : UU l}
  where

  postulate
    eq-equiv : A ≃ B → A ＝ B

    is-section-eq-equiv : is-section equiv-eq eq-equiv

    is-retraction-eq-equiv' : is-retraction equiv-eq eq-equiv

    coh-eq-equiv' :
      coherence-is-coherently-invertible
        ( equiv-eq)
        ( eq-equiv)
        ( is-section-eq-equiv)
        ( is-retraction-eq-equiv')

univalence : univalence-axiom
univalence A B =
  is-equiv-is-invertible eq-equiv is-section-eq-equiv is-retraction-eq-equiv'

module _
  {l : Level} {A B : UU l}
  where

  equiv-univalence : (A ＝ B) ≃ (A ≃ B)
  pr1 equiv-univalence = equiv-eq
  pr2 equiv-univalence = univalence A B

  abstract
    is-retraction-eq-equiv : is-retraction (equiv-eq {A = A} {B}) eq-equiv
    is-retraction-eq-equiv =
      is-retraction-map-inv-is-equiv (univalence A B)

module _
  {l : Level}
  where

  is-equiv-eq-equiv : (A B : UU l) → is-equiv (eq-equiv {A = A} {B})
  is-equiv-eq-equiv A B =
    is-equiv-is-invertible equiv-eq is-retraction-eq-equiv' is-section-eq-equiv

  compute-eq-equiv-id-equiv : (A : UU l) → eq-equiv {A = A} id-equiv ＝ refl
  compute-eq-equiv-id-equiv A = is-retraction-eq-equiv refl

  equiv-eq-equiv : (A B : UU l) → (A ≃ B) ≃ (A ＝ B)
  pr1 (equiv-eq-equiv A B) = eq-equiv
  pr2 (equiv-eq-equiv A B) = is-equiv-eq-equiv A B

module _
  {l : Level}
  where

  abstract
    is-torsorial-equiv :
      (A : UU l) → is-torsorial (λ (X : UU l) → A ≃ X)
    is-torsorial-equiv A =
      is-torsorial-equiv-based-univalence A (univalence A)

    is-torsorial-equiv' :
      (A : UU l) → is-torsorial (λ (X : UU l) → X ≃ A)
    is-torsorial-equiv' A =
      is-contr-equiv'
        ( Σ (UU l) (λ X → X ＝ A))
        ( equiv-tot (λ X → equiv-univalence))
        ( is-torsorial-Id' A)
```

As a first application of the univalence axiom, let us show that for any type `A` the type of types in a univalent universe `𝒰` that are equivalent to `A` is a proposition.

## Definition 17.1.3

Consider a univalent universe `𝒰`.
A type `X` is said to be **`𝒰`-small** if it comes equipped with an element of type

```text
  is-small_𝒰(A) ≔ Σ(X : 𝒰) A ≃ X.
```

Similarly, a map `f : A → B` is said to be **`𝒰`-small** if all of its fibers are `𝒰`-small.

```agda
is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  type-is-small : UU l
  type-is-small = pr1 H

  equiv-is-small : A ≃ type-is-small
  equiv-is-small = pr2 H

  inv-equiv-is-small : type-is-small ≃ A
  inv-equiv-is-small = inv-equiv equiv-is-small

  map-equiv-is-small : A → type-is-small
  map-equiv-is-small = map-equiv equiv-is-small

  map-inv-equiv-is-small : type-is-small → A
  map-inv-equiv-is-small = map-inv-equiv equiv-is-small

  is-section-map-inv-equiv-is-small :
    is-section map-equiv-is-small map-inv-equiv-is-small
  is-section-map-inv-equiv-is-small =
    is-section-map-inv-equiv equiv-is-small

  is-retraction-map-inv-equiv-is-small :
    is-retraction map-equiv-is-small map-inv-equiv-is-small
  is-retraction-map-inv-equiv-is-small =
    is-retraction-map-inv-equiv equiv-is-small

  is-equiv-map-inv-equiv-is-small : is-equiv map-inv-equiv-is-small
  is-equiv-map-inv-equiv-is-small = is-equiv-map-inv-equiv equiv-is-small

  coherence-map-inv-equiv-is-small :
    coherence-is-coherently-invertible
      ( map-equiv-is-small)
      ( map-inv-equiv-is-small)
      ( is-section-map-inv-equiv-is-small)
      ( is-retraction-map-inv-equiv-is-small)
  coherence-map-inv-equiv-is-small =
    coherence-map-inv-equiv equiv-is-small

is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-small-map l {B = B} f = (b : B) → is-small l (fiber f b)
```

## Example 17.1.4

1. Any type in `𝒰` is `𝒰`-small.

2. Any contractible type is `𝒰`-small with respect to any universe `𝒰`.

3. For any family `P` of `𝒰`-small types over a `𝒰`-small type `A`, the dependent product `Π(x : A) B(x)` is `𝒰`-small.

4. The type of `𝒰`-small types in `𝒱` is equivalent to the type of `𝒱`-small types in `𝒰`.
   This follows from the equivalence

   ```text
     (Σ(Y : 𝒱) Σ(X : 𝒰) Y ≃ X) ≃ (Σ(X : 𝒰) Σ(Y : 𝒱) X ≃ Y).
   ```

5. Any finite type is `𝒰`-small for any universe `𝒰`.
   Consequently, we get equivalences

   ```text
     (Σ(X : 𝒰) is-finite(X)) ≃ (Σ(Y : 𝒱) is-finite(Y))
   ```
    
   for any two univalent universes `𝒰` and `𝒱`. This observation is the reason why we usually write `𝔽` for the type of finite types (in `𝒰`), without referring to its universe.

6. In Theorem 20.6.10 we will show that `𝒰` cannot be `𝒰`-small, i.e., that there cannot be a type `U : 𝒰` equipped with an equivalence `U ≃ 𝒰`.

```agda
data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

module _
  {l l1 : Level} {A : UU l1}
  where

  map-inv-raise : raise l A → A
  map-inv-raise (map-raise x) = x

  is-section-map-inv-raise : (map-raise ∘ map-inv-raise) ~ id
  is-section-map-inv-raise (map-raise x) = refl

  is-retraction-map-inv-raise : (map-inv-raise ∘ map-raise) ~ id
  is-retraction-map-inv-raise x = refl

  is-equiv-map-raise : is-equiv (map-raise {l} {l1} {A})
  is-equiv-map-raise =
    is-equiv-is-invertible
      map-inv-raise
      is-section-map-inv-raise
      is-retraction-map-inv-raise

compute-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
pr1 (compute-raise l A) = map-raise
pr2 (compute-raise l A) = is-equiv-map-raise

inv-compute-raise : (l : Level) {l1 : Level} (A : UU l1) → raise l A ≃ A
inv-compute-raise l A = inv-equiv (compute-raise l A)

Raise : (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
pr1 (Raise l A) = raise l A
pr2 (Raise l A) = compute-raise l A

module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-small-lmax : is-small (l1 ⊔ l2) X
  is-small-lmax = (raise l2 X , compute-raise l2 X)

raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star

raise-terminal-map : {l1 l2 : Level} (A : UU l1) → A → raise-unit l2
raise-terminal-map {l2 = l2} A = const A raise-star

abstract
  is-contr-raise-unit : {l1 : Level} → is-contr (raise-unit l1)
  is-contr-raise-unit {l1} =
    is-contr-equiv' unit (compute-raise l1 unit) is-contr-unit

is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
is-small-is-contr l H = (raise-unit l , equiv-is-contr H is-contr-raise-unit)

is-small-unit : {l : Level} → is-small l unit
is-small-unit = is-small-is-contr _ is-contr-unit

Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Small-Type l1 l2 = Σ (UU l2) (is-small l1)

module _
  {l1 l2 : Level} (A : Small-Type l1 l2)
  where

  type-Small-Type : UU l2
  type-Small-Type = pr1 A

  is-small-type-Small-Type : is-small l1 type-Small-Type
  is-small-type-Small-Type = pr2 A

  small-type-Small-Type : UU l1
  small-type-Small-Type = type-is-small is-small-type-Small-Type

  equiv-is-small-type-Small-Type :
    type-Small-Type ≃ small-type-Small-Type
  equiv-is-small-type-Small-Type =
    equiv-is-small is-small-type-Small-Type

is-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) →
  is-small (l3 ⊔ l4) ((x : A) → B x)
pr1 (is-small-Π {B = B} (X , e) H) =
  (x : X) → pr1 (H (map-inv-equiv e x))
pr2 (is-small-Π {B = B} (X , e) H) =
  equiv-Π
    ( λ (x : X) → pr1 (H (map-inv-equiv e x)))
    ( e)
    ( λ a →
      ( equiv-tr
      ( λ t → pr1 (H t))
        ( inv (is-retraction-map-inv-equiv e a))) ∘e
      ( pr2 (H a)))

Π-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Small-Type l3 l4) → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Small-Type A B) = (a : type-Small-Type A) → type-Small-Type (B a)
pr2 (Π-Small-Type A B) =
  is-small-Π (is-small-type-Small-Type A) (λ a → is-small-type-Small-Type (B a))

is-small-function-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A → B)
is-small-function-type H K = is-small-Π H (λ a → K)

equiv-Small-Type :
  (l1 l2 : Level) → Small-Type l1 l2 ≃ Small-Type l2 l1
equiv-Small-Type l1 l2 =
  ( equiv-tot (λ X → equiv-tot (λ Y → equiv-inv-equiv))) ∘e
  ( equiv-left-swap-Σ)
```

## Proposition 17.1.5

For any univalent universe `𝒰` and any type `A`, the type `is-small_𝒰(A)` is a proposition.

### Proof

By Proposition 12.1.3 it suffices to show that

```text
  is-small_𝒰(A) → is-contr(is-small_𝒰(A)).
```

Let `X : 𝒰` be a type equipped with `e : A ≃ X`.
Then we have an equivalence

```text
  (Σ(Y : 𝒰) A ≃ Y) ≃ (Σ(Y : 𝒰) X ≃ Y).
```

The latter type is contractible by Theorem 17.1.1. ◻

```agda
module _
  (l : Level) {l1 : Level} (A : UU l1)
  where

  is-proof-irrelevant-is-small : is-proof-irrelevant (is-small l A)
  is-proof-irrelevant-is-small (X , e) =
    is-contr-equiv'
      ( Σ (UU l) (λ Y → X ≃ Y))
      ( equiv-tot (equiv-precomp-equiv e))
      ( is-torsorial-equiv X)

  is-prop-is-small : is-prop (is-small l A)
  is-prop-is-small = is-prop-is-proof-irrelevant is-proof-irrelevant-is-small

  is-small-Prop : Prop (lsuc l ⊔ l1)
  is-small-Prop = (is-small l A , is-prop-is-small)
```

## Corollary 17.1.6

Consider a univalent universe `𝒰` and a univalent universe `𝒱` containing all types in `𝒰`.
Then the universe inclusion `i : 𝒰 → 𝒱` is an embedding.

### Proof

Since `𝒱` is assumed to be univalent, it follows that

```text
  fib(i,A) ≃ is-small_𝒰(A)
```

for any type `A : 𝒱`.
The type `is-small_𝒰(A)` is a proposition since `𝒰` is univalent.
Hence the claim follows by Theorem 12.2.3. ◻

Note: This lemma is specific to the way universes are handled in the book. In Agda, the inclusion of a universe into a larger one is `raise`.

```agda
module _
  (l2 : Level) {l1 : Level}
  where

  abstract
    is-proof-irrelevant-map-raise :
      (X : UU (l1 ⊔ l2)) → is-proof-irrelevant (fiber (raise l2 {l1}) X)
    is-proof-irrelevant-map-raise X (A , p) =
      is-contr-equiv
        ( Σ (UU l1) (λ A' → A' ≃ A))
        ( equiv-tot
          ( λ A' →
            ( equiv-postcomp-equiv (inv-compute-raise l2 A) A') ∘e
            ( equiv-precomp-equiv (compute-raise l2 A') (raise l2 A)) ∘e
            ( equiv-univalence) ∘e
            ( equiv-concat' (raise l2 A') (inv p))))
        ( is-torsorial-equiv' A)

  abstract
    is-prop-map-raise : is-prop-map (raise l2 {l1})
    is-prop-map-raise X =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-map-raise X)

  abstract
    is-emb-raise : is-emb (raise l2 {l1})
    is-emb-raise = is-emb-is-prop-map is-prop-map-raise

  emb-raise : UU l1 ↪ UU (l1 ⊔ l2)
  emb-raise = (raise l2 , is-emb-raise)
```

## Supplement

### Univalence for type families

```agda
equiv-fam :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-fam {A = A} B C = (a : A) → B a ≃ C a

id-equiv-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → equiv-fam B B
id-equiv-fam B a = id-equiv

equiv-eq-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → B ＝ C → equiv-fam B C
equiv-eq-fam B .B refl = id-equiv-fam B

abstract
  is-torsorial-equiv-fam :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    is-torsorial (λ (C : A → UU l2) → equiv-fam B C)
  is-torsorial-equiv-fam B =
    is-torsorial-Eq-Π (λ x → is-torsorial-equiv (B x))

abstract
  is-equiv-equiv-eq-fam :
    {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → is-equiv (equiv-eq-fam B C)
  is-equiv-equiv-eq-fam B =
    fundamental-theorem-id
      ( is-torsorial-equiv-fam B)
      ( equiv-eq-fam B)

extensionality-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → (B ＝ C) ≃ equiv-fam B C
pr1 (extensionality-fam B C) = equiv-eq-fam B C
pr2 (extensionality-fam B C) = is-equiv-equiv-eq-fam B C

eq-equiv-fam :
  {l1 l2 : Level} {A : UU l1} {B C : A → UU l2} → equiv-fam B C → B ＝ C
eq-equiv-fam {B = B} {C} = map-inv-is-equiv (is-equiv-equiv-eq-fam B C)
```

### Computations with univalence

```agda
compute-equiv-eq-concat :
  {l : Level} {A B C : UU l} (p : A ＝ B) (q : B ＝ C) →
  equiv-eq q ∘e equiv-eq p ＝ equiv-eq (p ∙ q)
compute-equiv-eq-concat refl refl = eq-equiv-eq-map-equiv refl

compute-eq-equiv-comp-equiv :
  {l : Level} {A B C : UU l} (f : A ≃ B) (g : B ≃ C) →
  eq-equiv f ∙ eq-equiv g ＝ eq-equiv (g ∘e f)
compute-eq-equiv-comp-equiv f g =
  is-injective-equiv
    ( equiv-univalence)
    ( ( inv ( compute-equiv-eq-concat (eq-equiv f) (eq-equiv g))) ∙
      ( ( ap
          ( λ e → (map-equiv e g) ∘e (equiv-eq (eq-equiv f)))
          ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ( ap
            ( λ e → g ∘e map-equiv e f)
            ( right-inverse-law-equiv equiv-univalence)) ∙
          ( ap
            ( λ e → map-equiv e (g ∘e f))
            ( inv (right-inverse-law-equiv equiv-univalence))))))

compute-map-eq-ap-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A} (p : x ＝ y) →
  map-eq (ap B (inv p)) ∘ map-eq (ap B p) ~ id
compute-map-eq-ap-inv refl = refl-htpy

commutativity-inv-equiv-eq :
  {l : Level} {A B : UU l} (p : A ＝ B) →
  inv-equiv (equiv-eq p) ＝ equiv-eq (inv p)
commutativity-inv-equiv-eq refl = eq-equiv-eq-map-equiv refl

commutativity-inv-eq-equiv :
  {l : Level} {A B : UU l} (f : A ≃ B) →
  inv (eq-equiv f) ＝ eq-equiv (inv-equiv f)
commutativity-inv-eq-equiv f =
  is-injective-equiv
    ( equiv-univalence)
    ( ( inv (commutativity-inv-equiv-eq (eq-equiv f))) ∙
      ( ( ap
          ( λ e → (inv-equiv (map-equiv e f)))
          ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ap
          ( λ e → map-equiv e (inv-equiv f))
          ( inv (right-inverse-law-equiv equiv-univalence)))))
```
