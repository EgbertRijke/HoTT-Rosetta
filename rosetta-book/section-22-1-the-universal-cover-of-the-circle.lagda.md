# Section 22.1 The universal cover of the circle

```agda
module section-22-1-the-universal-cover-of-the-circle where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import section-17-6-the-binomial-types
open import section-19-4-homotopy-groups-of-types
open import section-21-1-the-induction-principle-of-the-circle
```

The type of small families over `S¹` is just the function type `S¹ → 𝒰`.
Therefore, we may use the universal property of the circle to construct type families over the circle.

By the universal property, `𝒰`-small type families over `S¹` are equivalently described as pairs `(X,p)` consisting of a type `X : 𝒰` and an identification `p : X = X`.
The univalence axiom implies that the map

```text
eq-equiv_{X,X} : (X ≃ X) → (X = X)
```

is an equivalence.
Therefore, type families over the circle are equivalently described as pairs `(X,e)`, consisting of a type `X` and an equivalence `e : X ≃ X`.
The type `Σ(X : 𝒰) X ≃ X` is also called the type of **descent data** for the circle.

```agda
Type-With-Endomorphism : (l : Level) → UU (lsuc l)
Type-With-Endomorphism l = Σ (UU l) endo

module _
  {l : Level} (X : Type-With-Endomorphism l)
  where

  type-Type-With-Endomorphism : UU l
  type-Type-With-Endomorphism = pr1 X

  endomorphism-Type-With-Endomorphism :
    type-Type-With-Endomorphism → type-Type-With-Endomorphism
  endomorphism-Type-With-Endomorphism = pr2 X

module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1) (Y : Type-With-Endomorphism l2)
  where

  hom-Type-With-Endomorphism : UU (l1 ⊔ l2)
  hom-Type-With-Endomorphism =
    Σ ( type-Type-With-Endomorphism X → type-Type-With-Endomorphism Y)
      ( λ f →
        coherence-square-maps
          ( f)
          ( endomorphism-Type-With-Endomorphism X)
          ( endomorphism-Type-With-Endomorphism Y)
          ( f))

  map-hom-Type-With-Endomorphism :
    hom-Type-With-Endomorphism →
    type-Type-With-Endomorphism X → type-Type-With-Endomorphism Y
  map-hom-Type-With-Endomorphism = pr1

  coherence-square-hom-Type-With-Endomorphism :
    (f : hom-Type-With-Endomorphism) →
    coherence-square-maps
      ( map-hom-Type-With-Endomorphism f)
      ( endomorphism-Type-With-Endomorphism X)
      ( endomorphism-Type-With-Endomorphism Y)
      ( map-hom-Type-With-Endomorphism f)
  coherence-square-hom-Type-With-Endomorphism = pr2

module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  is-equiv-hom-Type-With-Endomorphism :
    hom-Type-With-Endomorphism X Y → UU (l1 ⊔ l2)
  is-equiv-hom-Type-With-Endomorphism h =
    is-equiv (map-hom-Type-With-Endomorphism X Y h)

module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  equiv-Type-With-Endomorphism : UU (l1 ⊔ l2)
  equiv-Type-With-Endomorphism =
    Σ ( type-Type-With-Endomorphism X ≃ type-Type-With-Endomorphism Y)
      ( λ e →
        coherence-square-maps
          ( map-equiv e)
          ( endomorphism-Type-With-Endomorphism X)
          ( endomorphism-Type-With-Endomorphism Y)
          ( map-equiv e))

  equiv-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism →
    type-Type-With-Endomorphism X ≃ type-Type-With-Endomorphism Y
  equiv-equiv-Type-With-Endomorphism e = pr1 e

  map-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism →
    type-Type-With-Endomorphism X → type-Type-With-Endomorphism Y
  map-equiv-Type-With-Endomorphism e =
    map-equiv (equiv-equiv-Type-With-Endomorphism e)

  coherence-square-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism) →
    coherence-square-maps
      ( map-equiv-Type-With-Endomorphism e)
      ( endomorphism-Type-With-Endomorphism X)
      ( endomorphism-Type-With-Endomorphism Y)
      ( map-equiv-Type-With-Endomorphism e)
  coherence-square-equiv-Type-With-Endomorphism e = pr2 e

  hom-equiv-Type-With-Endomorphism :
    equiv-Type-With-Endomorphism → hom-Type-With-Endomorphism X Y
  pr1 (hom-equiv-Type-With-Endomorphism e) =
    map-equiv-Type-With-Endomorphism e
  pr2 (hom-equiv-Type-With-Endomorphism e) =
    coherence-square-equiv-Type-With-Endomorphism e

  is-equiv-equiv-Type-With-Endomorphism :
    (e : equiv-Type-With-Endomorphism) →
    is-equiv-hom-Type-With-Endomorphism X Y (hom-equiv-Type-With-Endomorphism e)
  is-equiv-equiv-Type-With-Endomorphism e =
    is-equiv-map-equiv (equiv-equiv-Type-With-Endomorphism e)

Type-With-Automorphism : (l : Level) → UU (lsuc l)
Type-With-Automorphism l = Σ (UU l) (Aut)

module _
  {l : Level} (A : Type-With-Automorphism l)
  where

  type-Type-With-Automorphism : UU l
  type-Type-With-Automorphism = pr1 A

  automorphism-Type-With-Automorphism : Aut type-Type-With-Automorphism
  automorphism-Type-With-Automorphism = pr2 A

  map-Type-With-Automorphism :
    type-Type-With-Automorphism → type-Type-With-Automorphism
  map-Type-With-Automorphism = map-equiv automorphism-Type-With-Automorphism

  type-with-endomorphism-Type-With-Automorphism : Type-With-Endomorphism l
  pr1 type-with-endomorphism-Type-With-Automorphism =
    type-Type-With-Automorphism
  pr2 type-with-endomorphism-Type-With-Automorphism =
    map-Type-With-Automorphism

module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1)
  (Y : Type-With-Automorphism l2)
  where

  equiv-Type-With-Automorphism : UU (l1 ⊔ l2)
  equiv-Type-With-Automorphism =
    equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  equiv-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism →
    type-Type-With-Automorphism X ≃ type-Type-With-Automorphism Y
  equiv-equiv-Type-With-Automorphism =
    equiv-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  map-equiv-Type-With-Automorphism :
    equiv-Type-With-Automorphism →
    type-Type-With-Automorphism X → type-Type-With-Automorphism Y
  map-equiv-Type-With-Automorphism =
    map-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  coherence-square-equiv-Type-With-Automorphism :
    (e : equiv-Type-With-Automorphism) →
    coherence-square-maps
      ( map-equiv-Type-With-Automorphism e)
      ( map-Type-With-Automorphism X)
      ( map-Type-With-Automorphism Y)
      ( map-equiv-Type-With-Automorphism e)
  coherence-square-equiv-Type-With-Automorphism =
    coherence-square-equiv-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

descent-data-circle :
  ( l1 : Level) → UU (lsuc l1)
descent-data-circle = Type-With-Automorphism

module _
  { l1 : Level} (P : descent-data-circle l1)
  where

  type-descent-data-circle : UU l1
  type-descent-data-circle = type-Type-With-Automorphism P

  aut-descent-data-circle : Aut type-descent-data-circle
  aut-descent-data-circle = automorphism-Type-With-Automorphism P

  map-descent-data-circle : type-descent-data-circle → type-descent-data-circle
  map-descent-data-circle = map-Type-With-Automorphism P
```

## Definition 22.1.1

Consider a type `X` and an equivalence `e : X ≃ X`.
We will construct a dependent type `D(X,e) : S¹ → 𝒰` equipped with an equivalence `x ↦ x_{D} : X ≃ D(X,e,base)` for which the square

```text
 [X] --≃-->[D(X,e,base)]
  |             |
e |             | tr_{D(X,e)}(loop)
  V             V
 [X] --≃-->[D(X,e,base)]
```

commutes.
We will write `d ↦ d_{X}` for the inverse of this equivalence, so that the relations

```text
(x_{D})_X = x (e(x)_{D}) = tr_{D(X,e)}(loop,x_{D})
(d_X)_{D} = d (tr_{D(X,e)}(d))_X = e(d_X)
```

hold.

### Construction

An easy path induction argument reveals that

```text
equiv-eq(ap_{P}(loop)) = tr_P(loop)
```

for each dependent type `P : S¹ → 𝒰`.
Therefore we see that the triangle

```text
                    [(S¹→ 𝒰)]
                   /          \
        gen_{S¹} /              \ desc_{S¹}
               V                  V
[Σ(X:𝒰) X=X]--tot(λ X. equiv-eq_{X,X})-->[Σ(X:𝒰) X ≃ X]
```

commutes, where the map `desc_{S¹}` is given by `P ↦ (P(base),tr_P(loop))` and the bottom map is an equivalence by the univalence axiom and Theorem 11.1.3.
Now it follows by the 3-for-2 property that `desc_{S¹}` is an equivalence, since `gen_{S¹}` is an equivalence by Theorem 21.2.3.
This means that for every type `X` and every `e : X ≃ X` there is a type family `D(X,e) : S¹ → 𝒰` equipped with an identification

```text
(D(X,e,base),tr_{D(X,e)}(loop)) = (X,e).
```

For convenience, we invert this identification.
Now we observe that the type of identifications in `Σ(X : 𝒰) X ≃ X` can be characterized by

```text
((X,e)=(X',e'))≃ Σ(α:X≃ X') e'∘ α~ α∘ e'.
```

This implies that we obtain an equivalence `x ↦ x_{D} : X ≃ D(X,e,base)` such that the square

```text
 [X] --x↦ x_{D}-->[D(X,e,base)]
  |                    |
e |                    | tr_{D(X,e)}(loop)
  V                    V
 [X] --x↦ x_{D}-->[D(X,e,base)]
```

commutes.

```agda
descent-data-family-circle :
  { l1 l2 : Level} {S : UU l1} (l : free-loop S) →
  ( S → UU l2) → descent-data-circle l2
pr1 (descent-data-family-circle l A) = A (base-free-loop l)
pr2 (descent-data-family-circle l A) = equiv-tr A (loop-free-loop l)

equiv-descent-data-circle :
  { l1 l2 : Level} → descent-data-circle l1 → descent-data-circle l2 →
  UU (l1 ⊔ l2)
equiv-descent-data-circle = equiv-Type-With-Automorphism

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( α : equiv-descent-data-circle P Q)
  where

  equiv-equiv-descent-data-circle :
    type-descent-data-circle P ≃ type-descent-data-circle Q
  equiv-equiv-descent-data-circle =
    equiv-equiv-Type-With-Automorphism P Q α

  map-equiv-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-equiv-descent-data-circle =
    map-equiv-Type-With-Automorphism P Q α

  coherence-square-equiv-descent-data-circle :
    coherence-square-maps
      ( map-equiv-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-equiv-descent-data-circle)
  coherence-square-equiv-descent-data-circle =
    coherence-square-equiv-Type-With-Automorphism P Q α

module _
  { l1 : Level} {S : UU l1} (l : free-loop S)
  where

  family-for-descent-data-circle :
    { l2 : Level} → descent-data-circle l2 → UU (l1 ⊔ lsuc l2)
  family-for-descent-data-circle {l2} P =
    Σ ( S → UU l2)
      ( λ A →
        equiv-descent-data-circle
          ( P)
          ( descent-data-family-circle l A))

  descent-data-circle-for-family :
    { l2 : Level} → (S → UU l2) → UU (lsuc l2)
  descent-data-circle-for-family {l2} A =
    Σ ( descent-data-circle l2)
      ( λ P →
        equiv-descent-data-circle
          ( P)
          ( descent-data-family-circle l A))

  family-with-descent-data-circle :
    ( l2 : Level) → UU (l1 ⊔ lsuc l2)
  family-with-descent-data-circle l2 =
    Σ ( S → UU l2) descent-data-circle-for-family

module _
  { l1 l2 : Level} {S : UU l1} {l : free-loop S}
  ( A : family-with-descent-data-circle l l2)
  where

  family-family-with-descent-data-circle : S → UU l2
  family-family-with-descent-data-circle = pr1 A

  descent-data-for-family-with-descent-data-circle :
    descent-data-circle-for-family l
      family-family-with-descent-data-circle
  descent-data-for-family-with-descent-data-circle = pr2 A

  descent-data-family-with-descent-data-circle : descent-data-circle l2
  descent-data-family-with-descent-data-circle =
    pr1 descent-data-for-family-with-descent-data-circle

  type-family-with-descent-data-circle : UU l2
  type-family-with-descent-data-circle =
    type-descent-data-circle descent-data-family-with-descent-data-circle

  aut-family-with-descent-data-circle : Aut type-family-with-descent-data-circle
  aut-family-with-descent-data-circle =
    aut-descent-data-circle descent-data-family-with-descent-data-circle

  map-aut-family-with-descent-data-circle :
    type-family-with-descent-data-circle → type-family-with-descent-data-circle
  map-aut-family-with-descent-data-circle =
    map-descent-data-circle descent-data-family-with-descent-data-circle

  eq-family-with-descent-data-circle :
    equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( descent-data-family-circle l family-family-with-descent-data-circle)
  eq-family-with-descent-data-circle =
    pr2 descent-data-for-family-with-descent-data-circle

  equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle ≃
    family-family-with-descent-data-circle (base-free-loop l)
  equiv-family-with-descent-data-circle =
    equiv-equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( descent-data-family-circle l family-family-with-descent-data-circle)
      ( eq-family-with-descent-data-circle)

  map-equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle →
    family-family-with-descent-data-circle (base-free-loop l)
  map-equiv-family-with-descent-data-circle =
    map-equiv equiv-family-with-descent-data-circle

  coherence-square-family-with-descent-data-circle :
    coherence-square-maps
      ( map-equiv-family-with-descent-data-circle)
      ( map-aut-family-with-descent-data-circle)
      ( tr family-family-with-descent-data-circle (loop-free-loop l))
      ( map-equiv-family-with-descent-data-circle)
  coherence-square-family-with-descent-data-circle =
    coherence-square-equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( descent-data-family-circle l family-family-with-descent-data-circle)
      ( eq-family-with-descent-data-circle)

  family-for-family-with-descent-data-circle :
    family-for-descent-data-circle l
      descent-data-family-with-descent-data-circle
  pr1 family-for-family-with-descent-data-circle =
    family-family-with-descent-data-circle
  pr2 family-for-family-with-descent-data-circle =
    eq-family-with-descent-data-circle
```

Recall from Example 9.2.5 that the successor function `succ-ℤ : ℤ → ℤ` is an equivalence.
Its inverse is the predecessor function defined in Exercise 4.1.

## Definition 22.1.2

The **universal cover** of the circle is defined via Definition 22.1.1 to be the unique dependent type `E_(S¹) ≔ D(ℤ,succ-ℤ ) : S¹ → 𝒰`. equipped with an equivalence `x ↦ x_E : ℤ → E_(S¹)(base)` and a homotopy witnessing that the square

```text
      [ℤ] --x ↦ x_E-->[E_(S¹)(base)]
       |                   |
succ-ℤ |                   | tr_{E_(S¹)}(loop)
       V                   V
      [ℤ] --x ↦ x_E-->[E_(S¹)(base)]
```

commutes.
We will occasionally write `y ↦ y_ℤ` for the inverse of `x ↦ x_{E}`.

The picture of the universal cover is that of a helix over the circle.
This picture emerges from the path liftings of `loop` in the total space.
The segments of the helix connecting `k` to `k+1` in the total space of the helix, are constructed in the following lemma.

## Lemma 22.1.3

For any `k : ℤ`, there is an identification

```text
segment-helix_k:(base,k_{E})=(base,succ-ℤ (k)_{E})
```

in the total space `Σ(t : S¹) E(t)`.

### Proof

_Proof._ By Theorem 9.3.4 it suffices to show that

```text
Π(k : ℤ) Σ(α : base = base) tr_{E}(α,k_{E}) = succ-ℤ (k)_{E}.
```

We just take `α ≔ loop`.
Then we have `tr_{E}(α,k_{E})= succ-ℤ (k)_{E}` by the commuting square provided in the definition of `E`. ◻
