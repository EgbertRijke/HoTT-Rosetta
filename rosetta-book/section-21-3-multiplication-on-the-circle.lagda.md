# Section 21.3 Multiplication on the circle

```agda
module section-21-3-multiplication-on-the-circle where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-12-3-sets
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-19-4-homotopy-groups-of-types
open import section-21-1-the-induction-principle-of-the-circle
open import section-21-2-the-dependent-universal-property-of-the-circle
```

One way the circle arises classically, is as the set of complex numbers at distance `1` from the origin.
It is an elementary fact that `|xy| = |x||y|` for any two complex numbers `x,y ∈ ℂ`, so it follows that when we multiply two complex numbers that both lie on the unit circle, then the result lies again on the unit circle.
This operation puts a group structure on the classical circle.

This suggests that it should also be possible to construct a multiplication on the higher inductive type `S¹`.
More precisely, we will equip `S¹` with an _H-space structure_, and in the exercises you will be asked to show that this multiplicative structure is associative, commutative, and has inverses.

## Definition 21.3.1

Consider a pointed type `A` with a base point `pt`.
An **H-space structure** on `(A,pt)` consists of a binary operation `μ : A → (A → A)` satisfying the following **coherent unit laws**:

```text
left-unit_μ(y) : μ(pt,y)= y
right-unit_μ(x) : μ(x,pt)= x
coh-unit_μ : left-unit_μ(pt) = right-unit_μ(pt).
```

```agda
module _
  {l : Level} {A : UU l} (μ : A → A → A) (e : A)
  where

coherent-unit-laws-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
coherent-unit-laws-mul-Pointed-Type A μ =
  coherent-unit-laws μ (point-Pointed-Type A)

coherent-unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
coherent-unital-mul-Pointed-Type A =
  Σ ( type-Pointed-Type A → type-Pointed-Type A → type-Pointed-Type A)
    ( coherent-unit-laws-mul-Pointed-Type A)

```

An **H-space** is a pointed type equipped with an H-space structure.

```agda
H-Space : (l : Level) → UU (lsuc l)
H-Space l =
  Σ (Pointed-Type l) coherent-unital-mul-Pointed-Type

make-H-Space :
  {l : Level} →
  (X : Pointed-Type l) → coherent-unital-mul-Pointed-Type X → H-Space l
make-H-Space X μ = (X , μ)

{-# INLINE make-H-Space #-}

module _
  {l : Level} (M : H-Space l)
  where

  pointed-type-H-Space : Pointed-Type l
  pointed-type-H-Space = pr1 M

  type-H-Space : UU l
  type-H-Space = type-Pointed-Type pointed-type-H-Space

  unit-H-Space : type-H-Space
  unit-H-Space = point-Pointed-Type pointed-type-H-Space

  coherent-unital-mul-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-H-Space
  coherent-unital-mul-H-Space = pr2 M

  mul-H-Space :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space = pr1 coherent-unital-mul-H-Space

  mul-H-Space' :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space' x y = mul-H-Space y x

  ap-mul-H-Space :
    {a b c d : type-H-Space} → a ＝ b → c ＝ d →
    mul-H-Space a c ＝ mul-H-Space b d
  ap-mul-H-Space p q = ap-binary mul-H-Space p q

  coherent-unit-laws-mul-H-Space :
    coherent-unit-laws mul-H-Space unit-H-Space
  coherent-unit-laws-mul-H-Space =
    pr2 coherent-unital-mul-H-Space

  left-unit-law-mul-H-Space :
    (x : type-H-Space) →
    mul-H-Space unit-H-Space x ＝ x
  left-unit-law-mul-H-Space =
    pr1 coherent-unit-laws-mul-H-Space

  right-unit-law-mul-H-Space :
    (x : type-H-Space) →
    mul-H-Space x unit-H-Space ＝ x
  right-unit-law-mul-H-Space =
    pr1 (pr2 coherent-unit-laws-mul-H-Space)

  coh-unit-laws-mul-H-Space :
    left-unit-law-mul-H-Space unit-H-Space ＝
    right-unit-law-mul-H-Space unit-H-Space
  coh-unit-laws-mul-H-Space =
    pr2 (pr2 coherent-unit-laws-mul-H-Space)

  unit-laws-mul-H-Space :
    unit-laws mul-H-Space unit-H-Space
  pr1 unit-laws-mul-H-Space = left-unit-law-mul-H-Space
  pr2 unit-laws-mul-H-Space = right-unit-law-mul-H-Space

  is-unital-mul-H-Space : is-unital mul-H-Space
  pr1 is-unital-mul-H-Space = unit-H-Space
  pr2 is-unital-mul-H-Space = unit-laws-mul-H-Space

  is-coherently-unital-mul-H-Space :
    is-coherently-unital mul-H-Space
  pr1 is-coherently-unital-mul-H-Space = unit-H-Space
  pr2 is-coherently-unital-mul-H-Space =
    coherent-unit-laws-mul-H-Space
```

## Remark 21.3.2

The data of an H-space structure is equivalently described by a family of base point preserving maps

```text
μ : Π(x:A) Σ(f : A → A) f(pt)=x
```

equipped with an identification `μ_pt = (id,refl)`.
The data `μ(a,pt) = a` corresponds to the right unit law for `μ`, whereas the data `μ_pt = (id,refl)` combines the left unit law and the coherence in one single identification.

Note that for any identification `α : x = y` in `A` and two base-point preserving functions `(f,p) : Σ(f : A → A) f(pt) = x` and `(g,q) : Σ(f : A → A) f(pt) = y`, we have

```text
τ : (Σ(H : f ~ g) p ∙ α = H(pt) ∙ q) → tr(α,(f,p)) = (g,q)
```

This function is easily constructed by identification elimination on `α`.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  ev-endo-Pointed-Type : endo-Pointed-Type (type-Pointed-Type A) →∗ A
  pr1 ev-endo-Pointed-Type = ev-point-Pointed-Type A
  pr2 ev-endo-Pointed-Type = refl

  pointed-section-ev-point-Pointed-Type : UU l
  pointed-section-ev-point-Pointed-Type =
    pointed-section ev-endo-Pointed-Type

  compute-pointed-section-ev-point-Pointed-Type :
    pointed-section-ev-point-Pointed-Type ≃ coherent-unital-mul-Pointed-Type A
  compute-pointed-section-ev-point-Pointed-Type =
    ( equiv-tot
      ( λ x →
        equiv-Σ
          ( λ α →
            Σ ( right-unit-law x (point-Pointed-Type A))
              ( coh-unit-laws x (point-Pointed-Type A) α))
          ( equiv-funext)
          ( λ _ → equiv-tot (λ _ → equiv-right-unwhisker-concat refl)))) ∘e
    ( associative-Σ)

module _
  {l : Level} (A : H-Space l)
  where

  ev-endo-H-Space :
    endo-Pointed-Type (type-H-Space A) →∗ pointed-type-H-Space A
  ev-endo-H-Space = ev-endo-Pointed-Type (pointed-type-H-Space A)

  pointed-section-ev-endo-H-Space : pointed-section ev-endo-H-Space
  pointed-section-ev-endo-H-Space =
    map-inv-equiv
      ( compute-pointed-section-ev-point-Pointed-Type (pointed-type-H-Space A))
      ( coherent-unital-mul-H-Space A)

  section-ev-endo-H-Space : section (map-pointed-map ev-endo-H-Space)
  section-ev-endo-H-Space =
    section-pointed-section ev-endo-H-Space pointed-section-ev-endo-H-Space
```

We will be using this in our construction of the H-space structure on the circle.

## Theorem 21.3.3

There is an H-space structure

```text
mul_(S¹) : S¹ → (S¹ → S¹)
left-unit_{S¹} : Π(y : S¹) mul_(S¹)(base,y) = y
right-unit_{S¹} : Π(x : S¹) mul_(S¹)(x,base) = x
coh-unit_{S¹} : left-unit_{S¹}(base) = right-unit_{S¹}(base).
```

on the circle.

### Proof

_Construction._ By Remark 21.3.2 it suffices to construct a dependent function

```text
μ : Π(x : S¹) Σ(f : S¹ → S¹) f(base) = x
```

such that `μ(base) = (id,refl)`.
This provides us with a useful shortcut, because the identification will follow from the computation rule of the induction principle of the circle.

Let `P` be the family of types given by `P(x) ≔ Σ(f : S¹ → S¹) f(base) = x`.
By the dependent universal property of the circle there is a unique

```text
μ : Π(x : S¹) Σ(f : S¹ → S¹) f(base)=x
```

equipped with an identification `α : μ(base) = (id,refl)` and an identification witnessing that the square

```text
[tr_P(loop,μ(base))]--ap_{tr_P(loop)}(α)-->[tr_P(loop,(id,refl))]
              |                                |
apd_{μ}(loop) |                                | τ(H,r)
              V                                V
          [μ(base)]  -----α---------->  [(id,refl)]
```

commutes.
In this square, `τ` is the function from Remark 21.3.2, and the homotopy `H : id ~ id` equipped with an identification `r:loop = H(base) ∙ refl` remain to be defined.

We use the dependent universal property of the circle with respect to the family `E_{id,id}` given by

```text
E_{id,id}(x) ≔ (x=x),
```

to define `H` as the unique homotopy equipped with an identification

```text
α : H(base) = loop
```

and an identification `β` witnessing that the square

```text
[tr_{E_{id,id}}(loop,H(base))]--ap_{tr_{E_{id,id}}(loop)}(α)-->[tr_{E_{id,id}}(loop,loop)]
              |                                                         |
apd_{H}(loop) |                                                         | γ
              V                                                         V
          [H(base)]      -----------------α--------------->           [loop]
```

commutes.
Now it remains to define the path `γ:tr_{E_{id,id}}(loop,loop)=loop` in the above square.
To proceed, we first observe that a simple path induction argument yields a function

```text
(p ∙ r=q ∙ p) → (tr_{E_{id,id}}(p,q)=r),
```

for any `p : base = x`, `q : base = base` and `r : x = x`.
In particular, we have a function

```text
(loop ∙ loop=loop ∙ loop)→(tr_{E_{id,id}}(loop,loop) = loop).
```

Now we apply this function to `refl` to obtain the desired identification

```text
γ : tr_{E_{id,id}}(loop,loop) = loop.
```

 ◻

```agda
loop-htpy-𝕊¹ : (x : 𝕊¹) → x ＝ x
loop-htpy-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))

compute-base-loop-htpy-𝕊¹ : loop-htpy-𝕊¹ base-𝕊¹ ＝ loop-𝕊¹
compute-base-loop-htpy-𝕊¹ =
  base-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))

Mul-Π-𝕊¹ : 𝕊¹ → UU lzero
Mul-Π-𝕊¹ x = 𝕊¹-Pointed-Type →∗ (𝕊¹ , x)

dependent-identification-Mul-Π-𝕊¹ :
  {x : 𝕊¹} (p : base-𝕊¹ ＝ x) (q : Mul-Π-𝕊¹ base-𝕊¹) (r : Mul-Π-𝕊¹ x) →
  (H : pr1 q ~ pr1 r) →
  pr2 q ∙ p ＝ H base-𝕊¹ ∙ pr2 r →
  tr Mul-Π-𝕊¹ p q ＝ r
dependent-identification-Mul-Π-𝕊¹ refl q r H u =
  eq-pointed-htpy q r (H , inv right-unit ∙ u)

eq-id-id-𝕊¹-Pointed-Type :
  tr Mul-Π-𝕊¹ loop-𝕊¹ id-pointed-map ＝ id-pointed-map
eq-id-id-𝕊¹-Pointed-Type =
  dependent-identification-Mul-Π-𝕊¹ loop-𝕊¹
    ( id-pointed-map)
    ( id-pointed-map)
    ( loop-htpy-𝕊¹)
    ( inv compute-base-loop-htpy-𝕊¹ ∙ inv right-unit)

mul-Π-𝕊¹ : Π-𝕊¹ (Mul-Π-𝕊¹) (id-pointed-map) (eq-id-id-𝕊¹-Pointed-Type)
mul-Π-𝕊¹ =
  apply-dependent-universal-property-𝕊¹
    ( Mul-Π-𝕊¹)
    ( id-pointed-map)
    ( eq-id-id-𝕊¹-Pointed-Type)

mul-𝕊¹ : 𝕊¹ → 𝕊¹ → 𝕊¹
mul-𝕊¹ x = pr1 (pr1 mul-Π-𝕊¹ x)

left-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ base-𝕊¹ x ＝ x
left-unit-law-mul-𝕊¹ = htpy-eq (ap pr1 (pr1 (pr2 mul-Π-𝕊¹)))

right-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ x base-𝕊¹ ＝ x
right-unit-law-mul-𝕊¹ x = pr2 (pr1 mul-Π-𝕊¹ x)

coh-unit-laws-𝕊¹ : coherent-unit-laws mul-𝕊¹ base-𝕊¹
coh-unit-laws-𝕊¹ =
    coherent-unit-laws-unit-laws mul-𝕊¹
        (left-unit-law-mul-𝕊¹ , right-unit-law-mul-𝕊¹)
```

## Remark 21.3.4

For some of the exercises below it may be useful to know that the binary operation `mul_(S¹)` is the unique map `S¹ → (S¹ → S¹)` equipped with an identification

```text
base-mul_(S¹) : mul_(S¹)(base) = id
```

and an identification `loop-mul_(S¹)` witnessing that the square

```text
         [mul_(S¹)(base)]--base-mul_(S¹)--> [id]
                    |                         |
ap_{mul_(S¹)}(loop) |                         | eq-htpy(H)
                    V                         V
         [mul_(S¹)(base)]--base-mul_(S¹)--> [id]
```

commutes, where the homotopy `H : id ~ id` is the one constructed in Theorem 21.3.3.
