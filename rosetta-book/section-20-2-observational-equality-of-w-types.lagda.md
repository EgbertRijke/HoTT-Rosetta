# Section 20.2 Observational equality of W-types

```agda
module section-20-2-observational-equality-of-w-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-20-1-the-type-of-well-founded-trees
```

## Agda pre-requisites

### The type of polynomial endofunctors

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
```

### The action on types of a polynomial endofunctor

```agda
type-polynomial-endofunctor' :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor' A B X = Σ A (λ x → B x → X)

type-polynomial-endofunctor :
  {l1 l2 l3 : Level} → polynomial-endofunctor l1 l2 → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor (A , B) = type-polynomial-endofunctor' A B
```

### Algebras for polynomial endofunctors

```agda
algebra-polynomial-endofunctor :
  (l : Level) {l1 l2 : Level} →
  polynomial-endofunctor l1 l2 →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor l P =
  Σ (UU l) (λ X → type-polynomial-endofunctor P X → X)

module _
  {l l1 l2 : Level} {P : polynomial-endofunctor l1 l2}
  where

  type-algebra-polynomial-endofunctor :
    algebra-polynomial-endofunctor l P → UU l
  type-algebra-polynomial-endofunctor X = pr1 X

  structure-algebra-polynomial-endofunctor :
    (X : algebra-polynomial-endofunctor l P) →
    type-polynomial-endofunctor P (type-algebra-polynomial-endofunctor X) →
    type-algebra-polynomial-endofunctor X
  structure-algebra-polynomial-endofunctor X = pr2 X
```

## End of Agda pre-requisites

Each element `x : W(A, B)` has symbol `symbol(x) : A` and a family of components `component(x) : B(symbol(x)) → W(A, B)`.
Therefore, we have a map

```text
η : W(A, B) → Σ(x : A) (B(x) → W(A, B))
```

given by `η(x) ≔ (symbol(x), component(x))`.

```agda
map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B → type-polynomial-endofunctor' A B (𝕎 A B)
map-inv-structure-𝕎-Alg (tree-𝕎 x α) = pair x α
```

## Proposition 20.2.1

The map `η : W(A, B) → Σ(x : A) (B(x) → W(A, B))` is an equivalence.

### Proof
We define

```text
ε : (Σ(x : A) (B(x) → W(A, B))) → W(A, B)
```

by `ε(x, α) ≔ tree(x, α)`.
The fact that `ε` is an inverse of `η` follows easily. ◻

```agda
structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor' A B (𝕎 A B) → 𝕎 A B
structure-𝕎-Alg (pair x α) = tree-𝕎 x α

𝕎-Alg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  algebra-polynomial-endofunctor (l1 ⊔ l2) (A , B)
𝕎-Alg A B = pair (𝕎 A B) structure-𝕎-Alg
```

```agda
is-section-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (structure-𝕎-Alg {B = B} ∘ map-inv-structure-𝕎-Alg {B = B}) ~ id
is-section-map-inv-structure-𝕎-Alg (tree-𝕎 x α) = refl

is-retraction-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (map-inv-structure-𝕎-Alg {B = B} ∘ structure-𝕎-Alg {B = B}) ~ id
is-retraction-map-inv-structure-𝕎-Alg (pair x α) = refl

is-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (structure-𝕎-Alg {B = B})
is-equiv-structure-𝕎-Alg =
  is-equiv-is-invertible
    map-inv-structure-𝕎-Alg
    is-section-map-inv-structure-𝕎-Alg
    is-retraction-map-inv-structure-𝕎-Alg

equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor' A B (𝕎 A B) ≃ 𝕎 A B
equiv-structure-𝕎-Alg =
  pair structure-𝕎-Alg is-equiv-structure-𝕎-Alg

is-equiv-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (map-inv-structure-𝕎-Alg {B = B})
is-equiv-map-inv-structure-𝕎-Alg =
  is-equiv-is-invertible
    structure-𝕎-Alg
    is-retraction-map-inv-structure-𝕎-Alg
    is-section-map-inv-structure-𝕎-Alg

inv-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B ≃ type-polynomial-endofunctor' A B (𝕎 A B)
inv-equiv-structure-𝕎-Alg =
  pair map-inv-structure-𝕎-Alg is-equiv-map-inv-structure-𝕎-Alg
```

The fact that we have an equivalence

```text
W(A, B) ≃ Σ(x : A) (B(x) → W(A, B)),
```

suggests a way to characterize the identity type of `W(A,B)`.
Indeed, any equivalence is an embedding, and therefore we also have

```text
(x = y) ≃ (η(x) = η(y)).
```

The latter is an identity type in a `Σ`-type, which can be characterized as a `Σ`-type of identity types.
We therefore define the following observational equality relation on `W(A, B)`.

## Definition 20.2.2

Suppose `A` and each `B(x)` are in `𝒰`.
We define a binary relation

```text
Eq_W : W(A, B) → W(A, B) → 𝒰
```

recursively by

```text
Eq_W(tree(x, α), tree(y, β)) ≔ Σ(p : x = y) Π(z : B(x)) α(z) = β(tr_B(p, z))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  Eq-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β) =
    Σ (x ＝ y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z)))
```

## Theorem 20.2.3

The observational equality relation `Eq_W` on `W(A, B)` is reflexive, and the canonical map

```text
(x = y) → Eq_W(x, y)
```

is an equivalence for each `x, y : W(A, B)`.

### Proof
The element `refl-Eq_W(x) : Eq_W(x, x)` is defined recursively as

```text
refl-Eq_W(tree(x, α))≔ (refl, refl-htpy_α).
```

This proof of reflexivity induces the canonical map `(x = y) → Eq_W(x, y)`.
To show that it is an equivalence for each `x, y : W(A, B)`, we apply the fundamental theorem of identity types, by which it suffices to show that the type

```text
Σ(y : W(A, B)) Eq_W(x, y)
```

is contractible for each `x : W(A, B)`.
The center of contraction is the pair `(x, refl-Eq_W(x))`.
For the contraction, we have to construct a function

```text
h : Π(y : W(A, B)) Π(p : Eq_W(x, y)) (x, refl-Eq_W(x)) = (y, p).
```

By the induction principle of W-types, it suffices to define

```text
h(tree(y, β), (p, H))≔ (x, (refl, refl-htpy)) = (y, (p, H)).
```

Here we proceed by identification elimination on `p : x = y`, followed by homotopy induction on the homotopy `H : α ~ β`.
Thus, it suffices to construct an identification

```text
(x, (refl, refl-htpy)) = (x, (refl, refl-htpy)),
```

which we have by reflexivity. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-Eq-𝕎 : (w : 𝕎 A B) → Eq-𝕎 w w
  refl-Eq-𝕎 (tree-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

  center-total-Eq-𝕎 : (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
  center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎 A B) →
    Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ (𝕎 A B) (Eq-𝕎 (tree-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = pair (tree-𝕎 x β) (pair refl e)

  contraction-total-Eq-𝕎 :
    (w : 𝕎 A B) (t : Σ (𝕎 A B) (Eq-𝕎 w)) → center-total-Eq-𝕎 w ＝ t
  contraction-total-Eq-𝕎
    ( tree-𝕎 x α) (pair (tree-𝕎 .x β) (pair refl e)) =
    ap
      ( ( aux-total-Eq-𝕎 x α) ∘
        ( map-distributive-Π-Σ
          { A = B x}
          { B = λ y → 𝕎 A B}
          { C = λ y → Eq-𝕎 (α y)}))
      { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
      { y = λ y → pair (β y) (e y)}
      ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

  is-torsorial-Eq-𝕎 : (w : 𝕎 A B) → is-torsorial (Eq-𝕎 w)
  is-torsorial-Eq-𝕎 w =
    pair (center-total-Eq-𝕎 w) (contraction-total-Eq-𝕎 w)

  Eq-𝕎-eq : (v w : 𝕎 A B) → v ＝ w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = refl-Eq-𝕎 v

  is-equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v =
    fundamental-theorem-id
      ( is-torsorial-Eq-𝕎 v)
      ( Eq-𝕎-eq v)

  eq-Eq-𝕎 : (v w : 𝕎 A B) → Eq-𝕎 v w → v ＝ w
  eq-Eq-𝕎 v w = map-inv-is-equiv (is-equiv-Eq-𝕎-eq v w)

  equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → (v ＝ w) ≃ Eq-𝕎 v w
  equiv-Eq-𝕎-eq v w = pair (Eq-𝕎-eq v w) (is-equiv-Eq-𝕎-eq v w)
```

## Theorem 20.2.4

Consider a type family `B` over a type `A`, and let `k : 𝕋` be a truncation level.
If `A` is a `(k + 1)`-type, then so is `W(A, B)`.

### Proof
Suppose that `A` is a `(k + 1)`-type.
In order to show that `W(A, B)` is a `(k + 1)`-type, we have to show that its identity types are `k`-types.
The proof is by induction on `x, y : W(A, B)`.
For `x ≐ tree(a, α)` and `y ≐ tree(b, β)`, we have the equivalence

```text
(tree(a, α) = tree(b, β)) ≃ Σ(p : a = b) Π(z : B(a)) α(z) = β(tr_B(p, z))
```

Note that the type `a = b` is a `k`-type by the assumption that `A` is a `(k + 1)`-type.
Furthermore, the type `α(z) = β(tr_B(p, z))` is a `k`-type by the induction hypothesis.
Therefore it follows that the type on the right-hand side of the displayed equivalence is a `k`-type, and this completes the proof. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  is-trunc-𝕎 : (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (𝕎 A B)
  is-trunc-𝕎 k is-trunc-A (tree-𝕎 x α) (tree-𝕎 y β) =
    is-trunc-is-equiv k
      ( Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β))
      ( Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-equiv-Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-trunc-Σ
        ( is-trunc-A x y)
        ( λ p → is-trunc-Π k
          ( λ z →
            is-trunc-is-equiv' k
            ( α z ＝ β (tr B p z))
            ( Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-equiv-Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-trunc-𝕎 k is-trunc-A (α z) (β (tr B p z))))))

  is-set-𝕎 : is-set A → is-set (𝕎 A B)
  is-set-𝕎 = is-trunc-𝕎 neg-one-𝕋
```