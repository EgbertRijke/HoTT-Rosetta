# Section 22.4 The fundamental group of the circle

```agda
module section-22-4-the-fundamental-group-of-the-circle where

open import universe-levels
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-19-4-homotopy-groups-of-types
open import section-21-1-the-induction-principle-of-the-circle
open import section-21-2-the-dependent-universal-property-of-the-circle
open import section-22-1-the-universal-cover-of-the-circle
open import section-22-3-the-dependent-universal-property-of-the-integers
```

We have two goals remaining in this book.
The first goal is to prove that the universal cover of the circle is an identity system at `base : S¹`, in the sense of Definition 11.2.1.
Since the universal cover is a family of sets over the circle, this implies that the circle is a `1`-type.

## Theorem 22.4.1

The universal cover of the circle is an identity system at `base : S¹`.

### Proof

_Proof._ By Exercise 13.9 it suffices to show that the map

```text
f ↦ f(0_{E}) : (Π(t : S¹) E_(S¹)(t) → A(t)) → A(base)
```

is an equivalence for every type family `A` over the circle.
Note that we have a commuting triangle

```text
                                 [(Π(t:S¹) E_(S¹)(t)→ A(t))]
                                 /                         \
                               /                            \ f ↦ f(0_{E})
                             V                                V
[Σ(h:ℤ→ A(base)) h∘succ-ℤ~ tr_A(loop)∘ h]--{(h,H)↦ h(0)}-->[A(base)]
```

in which the left map is the equivalence obtained in Corollary 22.2.4 and the bottom map is an equivalence by Corollary 22.3.6. ◻

```agda
center-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  Σ X (universal-cover-circle l dup-circle)
pr1 (center-total-universal-cover-circle l dup-circle) = base-free-loop l
pr2 (center-total-universal-cover-circle l dup-circle) =
  map-equiv ( compute-fiber-universal-cover-circle l dup-circle) zero-ℤ

dependent-identification-loop-contraction-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  dependent-identification
    ( contraction-total-space
      ( center-total-universal-cover-circle l dup-circle))
    ( pr2 l)
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-universal-cover-circle l dup-circle))
      ( h))
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-universal-cover-circle l dup-circle))
      ( h))
dependent-identification-loop-contraction-total-universal-cover-circle
  l dup-circle h p =
  map-dependent-identification-contraction-total-space'
    ( center-total-universal-cover-circle l dup-circle)
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-tr-universal-cover-circle l dup-circle)
    ( h)
    ( h)
    ( p)

contraction-total-universal-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  ( t : Σ X (universal-cover-circle l dup-circle)) →
  center-total-universal-cover-circle l dup-circle ＝ t
contraction-total-universal-cover-circle-data
  {l1} l dup-circle h p (pair x y) =
  map-inv-is-equiv
    ( dup-circle
      ( contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)))
    ( pair
      ( map-inv-equiv
        ( equiv-contraction-total-space
          ( center-total-universal-cover-circle l dup-circle)
          ( base-free-loop l)
          ( compute-fiber-universal-cover-circle l dup-circle))
        ( h))
      ( dependent-identification-loop-contraction-total-universal-cover-circle
        l dup-circle h p))
    x y

is-torsorial-universal-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  is-torsorial (universal-cover-circle l dup-circle)
pr1 (is-torsorial-universal-cover-circle-data l dup-circle h p) =
  center-total-universal-cover-circle l dup-circle
pr2 (is-torsorial-universal-cover-circle-data l dup-circle h p) =
  contraction-total-universal-cover-circle-data l dup-circle h p

path-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l)
  ( k : ℤ) →
  Id
    { A = Σ X (universal-cover-circle l dup-circle)}
    ( pair
      ( base-free-loop l)
      ( map-equiv (compute-fiber-universal-cover-circle l dup-circle) k))
    ( pair
      ( base-free-loop l)
      ( map-equiv
        ( compute-fiber-universal-cover-circle l dup-circle)
        ( succ-ℤ k)))
path-total-universal-cover-circle l dup-circle k =
  segment-Σ
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-tr-universal-cover-circle l dup-circle)
    k

CONTRACTION-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  UU l1
CONTRACTION-universal-cover-circle l dup-circle =
  ELIM-ℤ
    ( λ k →
      Id
        ( center-total-universal-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-universal-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-universal-cover-circle l dup-circle)
      ( path-total-universal-cover-circle l dup-circle k))

Contraction-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  CONTRACTION-universal-cover-circle l dup-circle
Contraction-universal-cover-circle l dup-circle =
  Elim-ℤ
    ( λ k →
      Id
        ( center-total-universal-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-universal-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-universal-cover-circle l dup-circle)
      ( path-total-universal-cover-circle l dup-circle k))

abstract
  is-torsorial-universal-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l) →
    is-torsorial (universal-cover-circle l dup-circle)
  is-torsorial-universal-cover-circle l dup-circle =
    is-torsorial-universal-cover-circle-data l dup-circle
      ( pr1 (Contraction-universal-cover-circle l dup-circle))
      ( inv-htpy
        ( pr2 (pr2 (Contraction-universal-cover-circle l dup-circle))))

point-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  universal-cover-circle l dup-circle (base-free-loop l)
point-universal-cover-circle l dup-circle =
  map-equiv (compute-fiber-universal-cover-circle l dup-circle) zero-ℤ

universal-cover-circle-eq :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( x : X) → base-free-loop l ＝ x → universal-cover-circle l dup-circle x
universal-cover-circle-eq l dup-circle .(base-free-loop l) refl =
  point-universal-cover-circle l dup-circle

abstract
  is-equiv-universal-cover-circle-eq :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l) →
    ( x : X) → is-equiv (universal-cover-circle-eq l dup-circle x)
  is-equiv-universal-cover-circle-eq l dup-circle =
    fundamental-theorem-id
      ( is-torsorial-universal-cover-circle l dup-circle)
      ( universal-cover-circle-eq l dup-circle)

equiv-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( x : X) →
  ( base-free-loop l ＝ x) ≃ (universal-cover-circle l dup-circle x)
equiv-universal-cover-circle l dup-circle x =
  pair
    ( universal-cover-circle-eq l dup-circle x)
    ( is-equiv-universal-cover-circle-eq l dup-circle x)

compute-loop-space-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  type-Ω (X , base-free-loop l) ≃ ℤ
compute-loop-space-circle l dup-circle =
  ( inv-equiv (compute-fiber-universal-cover-circle l dup-circle)) ∘e
  ( equiv-universal-cover-circle l dup-circle (base-free-loop l))
```

## Corollary 22.4.2

The circle is a `1`-type and not a `0`-type.

### Proof

_Proof._ To see that the circle is a `1`-type we have to show that `s = t` is a `0`-type for every `s,t : S¹`.
By Exercise 21.2 it suffices to show that the loop space of the circle is a `0`-type.
This is indeed the case, because `ℤ` is a `0`-type, and we have an equivalence `(base = base) ≃ ℤ`.

Furthermore, since `ℤ` is a `0`-type and not a `(-1)`-type, it follows that the circle is a `1`-type and not a `0`-type. ◻

Our second goal is to construct a group isomorphism

```text
π_1(S¹) ≅ ℤ.
```

However, Theorem 22.4.1 doesn’t immediately show that the fundamental group of the circle is `ℤ`.
It only gives us an equivalence

```text
Ω(S¹) ≃ ℤ.
```

In order to compute the fundamental group of the circle we augment the fundamental theorem of identity types with the following proposition.

## Proposition 22.4.3

Consider a type `A` equipped with a point `a : A`, and consider an identity system `B` on `A` at `a` equipped with `b : B(a)`.
Furthermore, suppose that there is a binary operation

```text
μ : B(a) → (B(x) → B(x))
```

for every `x : A`, equipped with a homotopy `μ(_,b) ~ id`.
Then we have

```text
f(p ∙ q) = μ(f(p),f(q))
```

for the unique family of maps

```text
f : Π(x : A) (a = x) → B(x)
```

such that `f(refl) = b`, and for every `p : a = a` and `q : a = x`.

### Proof

BENCHMARK PROBLEM

_Proof._ Consider a family of maps `f : (a = x) → B(x)` indexed by `x : A` such that `f(refl) = b`, and let `p : a = a` and `q : a = x`.
By induction on `q` it suffices to show that

```text
f(p) = μ(f(p),f(refl))
```

This follows, since `f(refl) = b` and `μ(f(p),b) = f(p)`. ◻

We are now ready to prove that the fundamental group of the circle is `ℤ`.
Recall from Definition 22.1.2 that we write `y ↦ y_ℤ` for the inverse of the equivalence

```text
x ↦ x_{E} : ℤ ≃ E_(S¹)(base).
```

## Theorem 22.4.4

There is a group isomorphism

```text
π_1(S¹) ≅ ℤ.
```

### Proof

BENCHMARK PROBLEM

_Proof._ First we observe that, since the circle is a `1`-type, we have an isomorphism of groups `π_1(S¹) ≅ Ω(S¹)`.
In order to show that the group `Ω(S¹)` is isomorphic to `ℤ`, we prove that the family of equivalences

```text
α : Π(t : S¹) (base = t) → E_(S¹)(t)
```

given by `α(refl) ≔ 0_{E}` satisfies

```text
α(p ∙ q)_ℤ = α(p)_ℤ + α(q)_ℤ
```

for every `p,q : Ω(S¹)`.

To see that the claim holds, note that by Proposition 22.4.3 it suffices to construct a binary operation

```text
μ : E_(S¹)(base) → (E_(S¹)(x) → E_(S¹)(x))
```

equipped with a homotopy `μ(_,0_{E}) ~ id`, such that

```text
μ(k_{E},l_{E}) = (k+l)_{E}
```

holds for every `k,l : ℤ`.
Equivalently, it suffices to construct for each `k : ℤ` a function

```text
μ(k_{E}) : E_(S¹)(x) → E_(S¹)(x)
```

indexed by `x : S¹` equipped with an identification `μ(k_{E},l_{E}) = (k+l)_{E}` for each `k,l : ℤ`.
Since we have

```text
k+(l+1) = (k+l)+1
```

for all `k,l : ℤ`, such a function is obtained at once from Corollary 22.2.4. ◻

In order to prove that the fundamental group of the circle is `ℤ`, we first had to use the univalence axiom to construct the universal cover of the circle.
This proof was originally discovered by Mike Shulman in 2011, and later published in \[citation: `LicataShulman`\].
Its importance of this proof to the field of homotopy type theory is hard to overestimate.
The proof led to the discovery of the _encode-decode method_, which we presented in this book as the fundamental theorem of identity types, and it was the start of the field that is now sometimes called _synthetic homotopy theory_, where the induction principle for identity types and the univalence axiom are used along with methods from algebraic topology in order to compute algebraic invariants of types.
