# Section 11.1 Families of equivalences

```agda
module section-11-1-families-of-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-10-3-contractible-equivalences
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
```

## Definition 11.1.1

Consider a family of maps

```text
  f : Π(x : A) B(x) → C(x).
```

We define the map

```text
  tot(f) : Σ(x : A) B(x) → Σ(x : A) C(x)
```

by `λ (x,y). (x,f(x,y))`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  tot : Σ A B → Σ A C
  tot (x , y) = (x , f x y)

tot-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (x , y) = eq-pair-eq-fiber (H x y)

tot-id :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  tot (λ x → id) ~ id {A = Σ A B}
tot-id B p = refl

preserves-comp-tot :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {B' : A → UU l3} {B'' : A → UU l4}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → g x ∘ f x) ~ tot g ∘ tot f
preserves-comp-tot f g p = refl
```

## Lemma 11.1.2

For any family of maps `f : Π(x : A) B(x) → C(x)` and any `t : Σ(x : A) C(x)`, there is an equivalence

```text
  fib(tot(f),t) ≃ fib(f(pr1(t)), pr2(t)).
```

### Proof

We first define

```text
  φ : Π(t:Σ(x:A) C(x)) fib(tot(f), t)→fib(f(pr1(t)), pr2(t))
```

by pattern matching by

```text
  φ((x,f(x,y)),((x,y),refl)) ≔ (y,refl).
```

For the proof that `φ(t)` is an equivalence, for each `t : Σ(x : A) C(x)`, we construct a map

```text
  ψ(t) : fib(f(pr1(t)),pr2(t)) → fib(tot(f),t)
```

equipped with homotopies `G(t):φ(t)∘ψ(t)~id` and `H(t):ψ(t)∘φ(t)~id`.
Each of these definitions is given by pattern matching, as follows:

```text
      ψ((x,f(x,y)),(y,refl)) ≔ ((x,y),refl)
      G((x,f(x,y)),(y,refl)) ≔ refl
  H((x,f(x,y)),((x,y),refl)) ≔ refl. ◻
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  map-compute-fiber-tot :
    (t : Σ A C) → fiber (tot f) t → fiber (f (pr1 t)) (pr2 t)
  map-compute-fiber-tot .(tot f (x , y)) ((x , y) , refl) = (y , refl)

  map-inv-compute-fiber-tot :
    (t : Σ A C) → fiber (f (pr1 t)) (pr2 t) → fiber (tot f) t
  map-inv-compute-fiber-tot (a , .(f a y)) (y , refl) = ((a , y) , refl)

  is-section-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-compute-fiber-tot t ∘ map-inv-compute-fiber-tot t) ~ id
  is-section-map-inv-compute-fiber-tot (x , .(f x y)) (y , refl) = refl

  is-retraction-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-inv-compute-fiber-tot t ∘ map-compute-fiber-tot t) ~ id
  is-retraction-map-inv-compute-fiber-tot ._ ((x , y) , refl) = refl

  abstract
    is-equiv-map-compute-fiber-tot :
      (t : Σ A C) → is-equiv (map-compute-fiber-tot t)
    is-equiv-map-compute-fiber-tot t =
      is-equiv-is-invertible
        ( map-inv-compute-fiber-tot t)
        ( is-section-map-inv-compute-fiber-tot t)
        ( is-retraction-map-inv-compute-fiber-tot t)

  compute-fiber-tot : (t : Σ A C) → fiber (tot f) t ≃ fiber (f (pr1 t)) (pr2 t)
  pr1 (compute-fiber-tot t) = map-compute-fiber-tot t
  pr2 (compute-fiber-tot t) = is-equiv-map-compute-fiber-tot t

  abstract
    is-equiv-map-inv-compute-fiber-tot :
      (t : Σ A C) → is-equiv (map-inv-compute-fiber-tot t)
    is-equiv-map-inv-compute-fiber-tot t =
      is-equiv-is-invertible
        ( map-compute-fiber-tot t)
        ( is-retraction-map-inv-compute-fiber-tot t)
        ( is-section-map-inv-compute-fiber-tot t)

  inv-compute-fiber-tot :
    (t : Σ A C) → fiber (f (pr1 t)) (pr2 t) ≃ fiber (tot f) t
  pr1 (inv-compute-fiber-tot t) = map-inv-compute-fiber-tot t
  pr2 (inv-compute-fiber-tot t) = is-equiv-map-inv-compute-fiber-tot t
```

## Theorem 11.1.3

Let `f : Π(x : A) B(x) → C(x)` be a family of maps.
The following are equivalent:

1. For each `x : A`, the map `f(x)` is an equivalence.
   In this case we say that `f` is a **family of equivalences**.

2. The map `tot(f) : Σ(x : A) B(x) → Σ(x : A) C(x)` is an equivalence.

### Proof

By Theorems 10.3.5 and 10.4.6 it suffices to show that `f(x)` is a contractible map for each `x : A`, if and only if `tot(f)` is a contractible map.
Thus, we will show that `fib(f(x),c)` is contractible if and only if `fib(tot(f),x,c)` is contractible, for each `x : A` and `c : C(x)`.
However, by Lemma 11.1.2 these types are equivalent, so the result follows by Exercise 10.3. ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-fiberwise-equiv : (f : (x : A) → B x → C x) → UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv f = (x : A) → is-equiv (f x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-equiv-tot-is-fiberwise-equiv : is-fiberwise-equiv f → is-equiv (tot f)
    is-equiv-tot-is-fiberwise-equiv H =
      is-equiv-is-contr-map
        ( λ t →
          is-contr-is-equiv
            ( fiber (f (pr1 t)) (pr2 t))
            ( map-compute-fiber-tot f t)
            ( is-equiv-map-compute-fiber-tot f t)
            ( is-contr-map-is-equiv (H (pr1 t)) (pr2 t)))

  abstract
    is-fiberwise-equiv-is-equiv-tot : is-equiv (tot f) → is-fiberwise-equiv f
    is-fiberwise-equiv-is-equiv-tot is-equiv-tot-f x =
      is-equiv-is-contr-map
        ( λ z →
          is-contr-is-equiv'
            ( fiber (tot f) (x , z))
            ( map-compute-fiber-tot f (x , z))
            ( is-equiv-map-compute-fiber-tot f (x , z))
            ( is-contr-map-is-equiv is-equiv-tot-f (x , z)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  equiv-tot : ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
  pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
  pr2 (equiv-tot e) =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))
```

Now consider the situation where we have a map `f : A → B`, and a family `C` over `B`.
Then we have the map

```text
  λ (x,z). (f(x),z) : Σ(x : A) C(f(x)) → Σ(y : B) C(y).
```

We claim that this map is an equivalence when `f` is an equivalence.
The technique to prove this claim is the same as the technique we used in Theorem 11.1.3: first we note that the fibers are equivalent to the fibers of `f`, and then we use the fact that a map is an equivalence if and only if its fibers are contractible to finish the proof.

The converse of the following lemma does not hold.
Why not?

## Lemma 11.1.4

Consider a map `f : A → B`, and let `C` be a type family over `B`.
If `f` is an equivalence, then the map

```text
  σ_f(C) ≔ λ (x,z). (f(x),z) : Σ(x : A) C(f(x)) → Σ(y : B) C(y)
```

is an equivalence.

### Proof

We claim that for each `t : Σ(y : B) C(y)` there is an equivalence

```text
  fib(σ_f(C),t) ≃ fib(f,pr1(t)).
```

We obtain such an equivalence by constructing the following functions and homotopies:

```text
                      φ(t) : fib(σ_f(C),t) → fib(f,pr1(t))
  φ((f(x),z),((x,z),refl)) ≔ (x,refl)

                      ψ(t) : fib(f,pr1(t)) → fib(σ_f(C),t)
      ψ((f(x),z),(x,refl)) ≔ ((x,z),refl)

                      G(t) : φ(t) ∘ ψ(t) ~ id
      G((f(x),z),(x,refl)) ≔ refl

                      H(t) : ψ(t) ∘ φ(t) ~ id
  H((f(x),z),((x,z),refl)) ≔ refl.
```

Now the claim follows, since we see that `φ` is a contractible map if and only if `f` is a contractible map. ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  map-Σ-map-base : Σ A (λ x → C (f x)) → Σ B C
  map-Σ-map-base (x , y) = (f x , y)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  fiber-map-Σ-map-base-fiber :
    (t : Σ B C) → fiber f (pr1 t) → fiber (map-Σ-map-base f C) t
  fiber-map-Σ-map-base-fiber (.(f x) , z) (x , refl) = ((x , z) , refl)

  fiber-fiber-map-Σ-map-base :
    (t : Σ B C) → fiber (map-Σ-map-base f C) t → fiber f (pr1 t)
  fiber-fiber-map-Σ-map-base ._ ((x , z) , refl) = (x , refl)

  is-section-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    fiber-map-Σ-map-base-fiber t ∘ fiber-fiber-map-Σ-map-base t ~ id
  is-section-fiber-fiber-map-Σ-map-base .(f x , z) ((x , z) , refl) = refl

  is-retraction-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    (fiber-fiber-map-Σ-map-base t ∘ fiber-map-Σ-map-base-fiber t) ~ id
  is-retraction-fiber-fiber-map-Σ-map-base (.(f x) , z) (x , refl) = refl

  abstract
    is-equiv-fiber-map-Σ-map-base-fiber :
      (t : Σ B C) → is-equiv (fiber-map-Σ-map-base-fiber t)
    is-equiv-fiber-map-Σ-map-base-fiber t =
      is-equiv-is-invertible
        ( fiber-fiber-map-Σ-map-base t)
        ( is-section-fiber-fiber-map-Σ-map-base t)
        ( is-retraction-fiber-fiber-map-Σ-map-base t)

  compute-fiber-map-Σ-map-base :
    (t : Σ B C) → fiber f (pr1 t) ≃ fiber (map-Σ-map-base f C) t
  pr1 (compute-fiber-map-Σ-map-base t) =
    fiber-map-Σ-map-base-fiber t
  pr2 (compute-fiber-map-Σ-map-base t) =
    is-equiv-fiber-map-Σ-map-base-fiber t

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  abstract
    is-contr-map-map-Σ-map-base :
      is-contr-map f → is-contr-map (map-Σ-map-base f C)
    is-contr-map-map-Σ-map-base is-contr-f (y , z) =
      is-contr-equiv'
        ( fiber f y)
        ( compute-fiber-map-Σ-map-base f C (y , z))
        ( is-contr-f y)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  abstract
    is-equiv-map-Σ-map-base : is-equiv f → is-equiv (map-Σ-map-base f C)
    is-equiv-map-Σ-map-base is-equiv-f =
      is-equiv-is-contr-map
        ( is-contr-map-map-Σ-map-base f C (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ map-equiv e) ≃ Σ B C
equiv-Σ-equiv-base C (f , is-equiv-f) =
  ( map-Σ-map-base f C , is-equiv-map-Σ-map-base f C is-equiv-f)
```

Now we use Lemma 11.1.4 to obtain a generalization of Theorem 11.1.3.

## Definition 11.1.5

Consider a map `f : A → B` and a family of maps

```text
  g : Π(x : A) C(x) → D(f(x)),
```

where `C` is a type family over `A`, and `D` is a type family over `B`.
In this situation we also say that `g` is a **family of maps over `f`**.
Then we define

```text
  tot_f(g) : Σ(x : A) C(x) → Σ(y : B) D(y)
```

by `tot_f(g)(x,z) ≔ (f(x),g(x,z))`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  map-Σ : (f : A → B) (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
  map-Σ f g (x , y) = (f x , g x y)
```

## Theorem 11.1.6

Suppose that `g` is a family of maps over `f` as in Definition 11.1.5, and suppose that `f` is an equivalence.
Then the following are equivalent:

1. The family of maps `g` over `f` is a family of equivalences.

2. The map `tot_f(g)` is an equivalence.

### Proof

Note that we have a commuting triangle

```text
                tot_f(g)
  Σ(x:A) C(x) -----------> Σ(y:B) D(y)
             \            /
       tot(g) \          / λ (x,z). (f(x),z)
               \        /
                ∨      ∨
             Σ(x:A) D(f(x))
```

By the assumption that `f` is an equivalence, it follows that the map

```text
  Σ(x : A) D(f(x)) → Σ(y : B) D(y)
```

is an equivalence.
Therefore it follows that `tot_f(g)` is an equivalence if and only if `tot(g)` is an equivalence.
Now the claim follows, since `tot(g)` is an equivalence if and only if `g` if a family of equivalences. ◻

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  triangle-map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) →
    map-Σ D f g ~ map-Σ-map-base f D ∘ tot g
  triangle-map-Σ f g t = refl

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  abstract
    is-equiv-map-Σ :
      {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-equiv f → is-fiberwise-equiv g → is-equiv (map-Σ D f g)
    is-equiv-map-Σ {f} {g} is-equiv-f is-fiberwise-equiv-g =
      is-equiv-left-map-triangle
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
        ( is-equiv-map-Σ-map-base f D is-equiv-f)

  equiv-Σ :
    (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) → Σ A C ≃ Σ B D
  pr1 (equiv-Σ e g) =
    map-Σ D (map-equiv e) (λ x → map-equiv (g x))
  pr2 (equiv-Σ e g) =
    is-equiv-map-Σ
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x))

  abstract
    is-fiberwise-equiv-is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-equiv (map-Σ D f g) → is-fiberwise-equiv g
    is-fiberwise-equiv-is-equiv-map-Σ f g H K =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-map-triangle
          ( map-Σ D f g)
          ( map-Σ-map-base f D)
          ( tot g)
          ( triangle-map-Σ D f g)
          ( is-equiv-map-Σ-map-base f D H)
          ( K))
```
