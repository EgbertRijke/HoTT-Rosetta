# Section 10.4 Equivalences are contractible maps

```agda
module section-10-4-equivalences-are-contractible-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-2-inverse-concatenation-maps
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
```

In Theorem 10.4.6 we will show the converse to Theorem 10.3.5, i.e., we will show that any equivalence is a contractible map.
We will do this in two steps.

First we introduce a new notion of *coherently invertible map*, for which we can easily show that such maps have contractible fibers.
Then we show that any equivalence is a coherently invertible map.

Recall that an invertible map is a map `f : A → B` equipped with `g : B → A` and homotopies

```text
  G : f ∘ g ~ id    and    H : g ∘ f ~ id.
```

Then we observe that both `G · f` and `f · H` are homotopies of the same type

```text
  f ∘ g ∘ f ~ f.
```

A coherently invertible map is an invertible map for which there is a further homotopy `G · f ~ f · H`.

## Definition 10.4.1

Consider a map `f : A → B`.
We say that `f` is **coherently invertible** if it comes equipped with

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id
  K : G · f ~ f · H.
```

We will write `is-coh-invertible(f)` for the type of quadruples `(g, G, H, K)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : f ∘ g ~ id) (H : g ∘ f ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible f g G H = G ·r f ~ f ·l H

  is-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-coherently-invertible f =
    Σ ( B → A)
      ( λ g →
        Σ ( f ∘ g ~ id)
          ( λ G →
            Σ ( g ∘ f ~ id)
              ( λ H → coherence-is-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f)
  where

  map-inv-is-coherently-invertible : B → A
  map-inv-is-coherently-invertible = pr1 H

  is-section-map-inv-is-coherently-invertible :
    is-section f map-inv-is-coherently-invertible
  is-section-map-inv-is-coherently-invertible = pr1 (pr2 H)

  is-retraction-map-inv-is-coherently-invertible :
    is-retraction f map-inv-is-coherently-invertible
  is-retraction-map-inv-is-coherently-invertible = pr1 (pr2 (pr2 H))

  coh-is-coherently-invertible :
    coherence-is-coherently-invertible f
      ( map-inv-is-coherently-invertible)
      ( is-section-map-inv-is-coherently-invertible)
      ( is-retraction-map-inv-is-coherently-invertible)
  coh-is-coherently-invertible = pr2 (pr2 (pr2 H))

  is-invertible-is-coherently-invertible : is-invertible f
  pr1 is-invertible-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr1 (pr2 is-invertible-is-coherently-invertible) =
    is-section-map-inv-is-coherently-invertible
  pr2 (pr2 is-invertible-is-coherently-invertible) =
    is-retraction-map-inv-is-coherently-invertible

  section-is-coherently-invertible : section f
  pr1 section-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 section-is-coherently-invertible =
    is-section-map-inv-is-coherently-invertible

  retraction-is-coherently-invertible : retraction f
  pr1 retraction-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 retraction-is-coherently-invertible =
    is-retraction-map-inv-is-coherently-invertible

coherently-invertible-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
coherently-invertible-map A B = Σ (A → B) (is-coherently-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : coherently-invertible-map A B)
  where

  map-coherently-invertible-map : A → B
  map-coherently-invertible-map = pr1 e

  is-coherently-invertible-map-coherently-invertible-map :
    is-coherently-invertible map-coherently-invertible-map
  is-coherently-invertible-map-coherently-invertible-map = pr2 e

  map-inv-coherently-invertible-map : B → A
  map-inv-coherently-invertible-map =
    map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-section-map-inv-coherently-invertible-map :
    map-coherently-invertible-map ∘ map-inv-coherently-invertible-map ~ id
  is-section-map-inv-coherently-invertible-map =
    is-section-map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-retraction-map-inv-coherently-invertible-map :
    map-inv-coherently-invertible-map ∘ map-coherently-invertible-map ~ id
  is-retraction-map-inv-coherently-invertible-map =
    is-retraction-map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  coh-coherently-invertible-map :
    coherence-is-coherently-invertible
      ( map-coherently-invertible-map)
      ( map-inv-coherently-invertible-map)
      ( is-section-map-inv-coherently-invertible-map)
      ( is-retraction-map-inv-coherently-invertible-map)
  coh-coherently-invertible-map =
    coh-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  section-coherently-invertible-map :
    section map-coherently-invertible-map
  section-coherently-invertible-map =
    section-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  retraction-coherently-invertible-map :
    retraction map-coherently-invertible-map
  retraction-coherently-invertible-map =
    retraction-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-invertible-coherently-invertible-map :
    is-invertible map-coherently-invertible-map
  is-invertible-coherently-invertible-map =
    is-invertible-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  invertible-map-coherently-invertible-map : invertible-map A B
  pr1 invertible-map-coherently-invertible-map =
    map-coherently-invertible-map
  pr2 invertible-map-coherently-invertible-map =
    is-invertible-coherently-invertible-map
```

Although we will encounter the notion of coherently invertible map on some further occasions, the following proposition is our main motivation for considering it.

## Proposition 10.4.2

Any coherently invertible map has contractible fibers.

### Proof

Consider a map `f : A → B` equipped with

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id
  K : G · f ~ f · H,
```

and let `y : B`.
Our goal is to show that `fib(f,y)` is contractible.
For the center of contraction we take `(g(y),G(y))`.
In order to construct a contraction, it suffices to construct a dependent function of type

```text
  Π(x : A) Π(p : f(x) = y) Eq-fib_f((g(y),G(y)),(x,p)).
```

By path induction on `p:f(x)=y` it suffices to construct a dependent function of type

```text
  Π(x : A) Eq-fib_f((g(f(x)),G(f(x))),(x,refl)).
```

By definition of `Eq-fib_f`, we have to construct for each `x : A` an identification `α : g(f(x)) = x` equipped with a further identification

```text
  G(f(x)) = ap_{f}(α) ∙ refl.
```

Such a dependent function is constructed as `λ x. (H(x),K'(x))`, where the homotopy `H : g ∘ f ~ id` is given by assumption, and the homotopy

```text
  K' : Π(x : A) G(f(x)) = ap_{f}(H(x)) ∙ refl
```

is defined as

```text
  K' ≔ K ∙ right-unit-htpy(f · H)⁻¹. ◻
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    center-fiber-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fiber f y
    pr1 (center-fiber-is-coherently-invertible H y) =
      map-inv-is-coherently-invertible H y
    pr2 (center-fiber-is-coherently-invertible H y) =
      is-section-map-inv-is-coherently-invertible H y

    contraction-fiber-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fiber f y) →
      (center-fiber-is-coherently-invertible H y) ＝ t
    contraction-fiber-is-coherently-invertible H y (x , refl) =
      eq-Eq-fiber f y
        ( is-retraction-map-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible :
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fiber-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fiber-is-coherently-invertible H y
```

Our next goal is to show that for any map `f : A → B` equipped with

```text
  g : B → A,    G : f ∘ g ~ id,    and    H : g ∘ f ~ id,
```

we can improve the homotopy `G` to a new homotopy `G' : f ∘ g ~ id` for which there is a further homotopy

```text
  f · H ~ G' · f.
```

Note that this situation is analogous to the situation in the proof of Theorem 10.2.3, where we improved the contraction `C` so that it satisfied `C(c) = refl`.
The extra coherence `f · H ~ G' · f` is then used in the proof that the fibers of an equivalence are contractible.

## Definition 10.4.3

Let `f, g : A → B` be functions, and consider `H : f ~ g` and `p : x = y` in `A`.
We define the identification

```text
  nat-htpy(H,p) : ap_{f}(p) ∙ H(y) = H(x) ∙ ap_{g}(p)
```

witnessing that the square

```text
              H(x)
        f(x) ====== g(x)
          ∥           ∥
  ap_f(p) ∥           ∥ ap_g(p)
          ∥           ∥
        f(y) ====== g(y)
              H(y)
```

commutes.
This square is also called the **naturality square** of the homotopy `H` at `p`.

### Construction

By path induction on `p` it suffices to construct an identification

```text
  ap_{f}(refl) ∙ H(x) = H(x) ∙ ap_{g}(refl)
```

since `ap_{f}(refl) ≐ refl` and `ap_{g}(refl) ≐ refl`, and since `refl ∙ H(x) ≐ H(x)`, we see that the path `right-unit(H(x))⁻¹` is of the asserted type.

```agda
nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  H x ∙ ap g p ＝ ap f p ∙ H y
nat-htpy H refl = right-unit
```

## Definition 10.4.4

Consider `f : A → A` and `H : f ~ id`.
We construct an identification `H(f(x)) = ap_{f}(H(x))`, for any `x : A`.

### Construction

By the naturality of homotopies with respect to identifications the square

```text
                   H(f(x))
            ff(x) ========= f(x)
             ∥                ∥
  ap_f(H(x)) ∥                ∥ H(x)
             ∥                ∥
            f(x) ============ x
                     H(x)
```

commutes.
This gives the desired identification `H(f(x)) = ap_{f}(H(x))`.

```agda
nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → H x ∙ p ＝ ap f p ∙ H y
nat-htpy-id H refl = right-unit
```

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : H ·r f ~ f ·l H
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-coh-htpy-id : f ·l H ~ H ·r f
  inv-coh-htpy-id = inv-htpy coh-htpy-id
```

## Lemma 10.4.5

Let `f : A → B` be a map equipped with an inverse, i.e., consider

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id.
```

Then there is a homotopy `G' : f ∘ g ~ id` equipped with a further homotopy

```text
  K : f · H ~ G' · f.
```

Thus we obtain a map `has-inverse(f) → is-coh-invertible(f)`.

### Proof

For each `y : B`, we construct the identification `G'(y)` as the concatenation

```text
         G(fg(y))⁻¹           ap_f(H(g(y)))         G(y)
  fg(y) ============ fgfg(y) =============== fg(y) ====== y.
```

In order to construct a homotopy `f · H ~ G' · f`, it suffices to show that the square

```text
                       G(fgf(x))
             fgfgf(x) =========== fgf(x)
                 ∥                  ∥ 
  ap_f(H(gf(x))) ∥                  ∥ ap_f(H(x))
                 ∥                  ∥
              fgf(x) ============= f(x)
                        G(f(x))
```

commutes for every `x : A`.
Recall from Definition 10.4.4 that we have `H(gf(x)) = ap_{gf}(H(x))`.
Using this identification, we see that it suffices to show that the square

```text
                       (G · f)(gf(x))
             fgfgf(x) ================ fgf(x)
                 ∥                        ∥
  ap_{fgf}(H(x)) ∥                        ∥ ap_f(H(x))
                 ∥                        ∥
              fgf(x) =================== f(x)
                         (G · f)(x)
```

commutes.
Now we observe that this is just a naturality square the homotopy `G · f : fgf ~ f`, which commutes by Definition 10.4.3. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  is-retraction-map-inv-is-coherently-invertible-is-invertible :
    map-inv-is-invertible H ∘ f ~ id
  is-retraction-map-inv-is-coherently-invertible-is-invertible =
    is-retraction-map-inv-is-invertible H

  abstract
    is-section-map-inv-is-coherently-invertible-is-invertible :
      f ∘ map-inv-is-invertible H ~ id
    is-section-map-inv-is-coherently-invertible-is-invertible =
      ( ( inv-htpy (is-section-map-inv-is-invertible H)) ·r
        ( f ∘ map-inv-is-invertible H)) ∙h
      ( ( ( f) ·l
          ( is-retraction-map-inv-is-invertible H) ·r
          ( map-inv-is-invertible H)) ∙h
        ( is-section-map-inv-is-invertible H))

  abstract
    inv-coh-is-coherently-invertible-is-invertible :
      f ·l is-retraction-map-inv-is-coherently-invertible-is-invertible ~
      is-section-map-inv-is-coherently-invertible-is-invertible ·r f
    inv-coh-is-coherently-invertible-is-invertible =
      left-transpose-htpy-concat
        ( ( is-section-map-inv-is-invertible H) ·r
          ( f ∘ map-inv-is-invertible H ∘ f))
        ( f ·l is-retraction-map-inv-is-invertible H)
        ( ( ( f) ·l
            ( is-retraction-map-inv-is-invertible H) ·r
            ( map-inv-is-invertible H ∘ f)) ∙h
          ( is-section-map-inv-is-invertible H ·r f))
        ( ( ( nat-htpy (is-section-map-inv-is-invertible H ·r f)) ·r
            ( is-retraction-map-inv-is-invertible H)) ∙h
          ( right-whisker-concat-htpy
            ( ( inv-preserves-comp-left-whisker-comp
                ( f)
                ( map-inv-is-invertible H ∘ f)
                ( is-retraction-map-inv-is-invertible H)) ∙h
              ( left-whisker-comp²
                ( f)
                ( inv-coh-htpy-id (is-retraction-map-inv-is-invertible H))))
            ( is-section-map-inv-is-invertible H ·r f)))

  abstract
    coh-is-coherently-invertible-is-invertible :
      coherence-is-coherently-invertible
        ( f)
        ( map-inv-is-invertible H)
        ( is-section-map-inv-is-coherently-invertible-is-invertible)
        ( is-retraction-map-inv-is-coherently-invertible-is-invertible)
    coh-is-coherently-invertible-is-invertible =
      inv-htpy inv-coh-is-coherently-invertible-is-invertible

  is-coherently-invertible-is-invertible : is-coherently-invertible f
  is-coherently-invertible-is-invertible =
    ( map-inv-is-invertible H ,
      is-section-map-inv-is-coherently-invertible-is-invertible ,
      is-retraction-map-inv-is-coherently-invertible-is-invertible ,
      coh-is-coherently-invertible-is-invertible)
```

Now we put the pieces together to conclude that any equivalence has contractible fibers.

## Theorem 10.4.6

Any equivalence is a contractible map.

### Proof

We have seen in Proposition 10.4.2 that any coherently invertible map is a contractible map.
Moreover, any equivalence has the structure of an invertible map by Proposition 9.2.7, and any invertible map is coherently invertible by Lemma 10.4.5. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv =
      is-contr-map-is-coherently-invertible ∘ (is-coherently-invertible-is-invertible ∘ is-invertible-is-equiv)
```

The following corollary is very similar to Theorem 10.1.4, which asserts that the type `Σ(x : A) a = x` is contractible.
However, we haven’t yet established that the equivalence `(a = x) ≃ (x = a)` induces an equivalence on total spaces.
However, using the fact that equivalences are contractible maps we can give a direct proof.

## Corollary 10.4.7

Let `A` be a type, and let `a : A`.
Then the type

```text
  Σ(x : A) x = a
```

is contractible.

### Proof

By Example 9.2.3, the identity function is an equivalence.
Therefore, the fibers of the identity function are contractible by Theorem 10.4.6.
Note that `Σ(x : A) x = a` is exactly the fiber of `id` at `a : A`. ◻

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-torsorial-Id' : (a : A) → is-torsorial (λ x → x ＝ a)
    pr1 (pr1 (is-torsorial-Id' a)) = a
    pr2 (pr1 (is-torsorial-Id' a)) = refl
    pr2 (is-torsorial-Id' a) (.a , refl) = refl
```

## Supplementary definitions

### The predicate of being a transpose coherently invertible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-transpose-coherently-invertible :
    (f : A → B) (g : B → A) (G : f ∘ g ~ id) (H : g ∘ f ~ id) → UU (l1 ⊔ l2)
  coherence-is-transpose-coherently-invertible f g G H = H ·r g ~ g ·l G

  is-transpose-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-transpose-coherently-invertible f =
    Σ ( B → A)
      ( λ g →
        Σ ( f ∘ g ~ id)
          ( λ G →
            Σ ( g ∘ f ~ id)
              ( λ H → coherence-is-transpose-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-transpose-coherently-invertible f)
  where

  map-inv-is-transpose-coherently-invertible : B → A
  map-inv-is-transpose-coherently-invertible = pr1 H

  is-section-map-inv-is-transpose-coherently-invertible :
    f ∘ map-inv-is-transpose-coherently-invertible ~ id
  is-section-map-inv-is-transpose-coherently-invertible = pr1 (pr2 H)

  is-retraction-map-inv-is-transpose-coherently-invertible :
    map-inv-is-transpose-coherently-invertible ∘ f ~ id
  is-retraction-map-inv-is-transpose-coherently-invertible = pr1 (pr2 (pr2 H))

  coh-is-transpose-coherently-invertible :
    coherence-is-transpose-coherently-invertible f
      ( map-inv-is-transpose-coherently-invertible)
      ( is-section-map-inv-is-transpose-coherently-invertible)
      ( is-retraction-map-inv-is-transpose-coherently-invertible)
  coh-is-transpose-coherently-invertible = pr2 (pr2 (pr2 H))

  is-invertible-is-transpose-coherently-invertible : is-invertible f
  pr1 is-invertible-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr1 (pr2 is-invertible-is-transpose-coherently-invertible) =
    is-section-map-inv-is-transpose-coherently-invertible
  pr2 (pr2 is-invertible-is-transpose-coherently-invertible) =
    is-retraction-map-inv-is-transpose-coherently-invertible

  section-is-transpose-coherently-invertible : section f
  pr1 section-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr2 section-is-transpose-coherently-invertible =
    is-section-map-inv-is-transpose-coherently-invertible

  retraction-is-transpose-coherently-invertible : retraction f
  pr1 retraction-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr2 retraction-is-transpose-coherently-invertible =
    is-retraction-map-inv-is-transpose-coherently-invertible

transpose-coherently-invertible-map :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
transpose-coherently-invertible-map A B =
  Σ (A → B) (is-transpose-coherently-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (e : transpose-coherently-invertible-map A B)
  where

  map-transpose-coherently-invertible-map : A → B
  map-transpose-coherently-invertible-map = pr1 e

  is-transpose-coherently-invertible-map-transpose-coherently-invertible-map :
    is-transpose-coherently-invertible map-transpose-coherently-invertible-map
  is-transpose-coherently-invertible-map-transpose-coherently-invertible-map =
    pr2 e

  map-inv-transpose-coherently-invertible-map : B → A
  map-inv-transpose-coherently-invertible-map =
    map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-section-map-inv-transpose-coherently-invertible-map :
    ( map-transpose-coherently-invertible-map ∘
      map-inv-transpose-coherently-invertible-map) ~
    ( id)
  is-section-map-inv-transpose-coherently-invertible-map =
    is-section-map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-retraction-map-inv-transpose-coherently-invertible-map :
    ( map-inv-transpose-coherently-invertible-map ∘
      map-transpose-coherently-invertible-map) ~
    ( id)
  is-retraction-map-inv-transpose-coherently-invertible-map =
    is-retraction-map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  coh-transpose-coherently-invertible-map :
    coherence-is-transpose-coherently-invertible
      ( map-transpose-coherently-invertible-map)
      ( map-inv-transpose-coherently-invertible-map)
      ( is-section-map-inv-transpose-coherently-invertible-map)
      ( is-retraction-map-inv-transpose-coherently-invertible-map)
  coh-transpose-coherently-invertible-map =
    coh-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  section-transpose-coherently-invertible-map :
    section map-transpose-coherently-invertible-map
  section-transpose-coherently-invertible-map =
    section-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  retraction-transpose-coherently-invertible-map :
    retraction map-transpose-coherently-invertible-map
  retraction-transpose-coherently-invertible-map =
    retraction-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-invertible-transpose-coherently-invertible-map :
    is-invertible map-transpose-coherently-invertible-map
  is-invertible-transpose-coherently-invertible-map =
    is-invertible-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  invertible-map-transpose-coherently-invertible-map : invertible-map A B
  pr1 invertible-map-transpose-coherently-invertible-map =
    map-transpose-coherently-invertible-map
  pr2 invertible-map-transpose-coherently-invertible-map =
    is-invertible-transpose-coherently-invertible-map
```

### The inverse of a coherently invertible map is transpose coherently invertible and vice versa

The inverse of a coherently invertible map is transpose coherently invertible.
Conversely, the inverse of a transpose coherently invertible map is coherently
invertible. Since these are defined by simply moving data around, they are
strict inverses to one another.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transpose-coherently-invertible-map-inv-is-coherently-invertible :
    {f : A → B} (H : is-coherently-invertible f) →
    is-transpose-coherently-invertible (map-inv-is-coherently-invertible H)
  is-transpose-coherently-invertible-map-inv-is-coherently-invertible {f} H =
    ( f ,
      is-retraction-map-inv-is-coherently-invertible H ,
      is-section-map-inv-is-coherently-invertible H ,
      coh-is-coherently-invertible H)

  is-coherently-invertible-map-inv-is-transpose-coherently-invertible :
    {f : A → B} (H : is-transpose-coherently-invertible f) →
    is-coherently-invertible (map-inv-is-transpose-coherently-invertible H)
  is-coherently-invertible-map-inv-is-transpose-coherently-invertible {f} H =
    ( f ,
      is-retraction-map-inv-is-transpose-coherently-invertible H ,
      is-section-map-inv-is-transpose-coherently-invertible H ,
      coh-is-transpose-coherently-invertible H)

  transpose-coherently-invertible-map-inv-coherently-invertible-map :
    coherently-invertible-map A B → transpose-coherently-invertible-map B A
  transpose-coherently-invertible-map-inv-coherently-invertible-map e =
    ( map-inv-coherently-invertible-map e ,
      is-transpose-coherently-invertible-map-inv-is-coherently-invertible
        ( is-coherently-invertible-map-coherently-invertible-map e))

  coherently-invertible-map-inv-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A B → coherently-invertible-map B A
  coherently-invertible-map-inv-transpose-coherently-invertible-map e =
    ( map-inv-transpose-coherently-invertible-map e ,
      is-coherently-invertible-map-inv-is-transpose-coherently-invertible
        ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map
          ( e)))
```

### Invertible maps are transpose coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  is-transpose-coherently-invertible-is-invertible :
    is-transpose-coherently-invertible f
  is-transpose-coherently-invertible-is-invertible =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertible
      ( is-coherently-invertible-is-invertible
        ( is-invertible-map-inv-is-invertible H))
```

### Coherently invertible maps are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-coherently-invertible :
    is-coherently-invertible f → is-equiv f
  is-equiv-is-coherently-invertible H =
    is-equiv-is-invertible' (is-invertible-is-coherently-invertible H)

  is-equiv-is-transpose-coherently-invertible :
    is-transpose-coherently-invertible f → is-equiv f
  is-equiv-is-transpose-coherently-invertible H =
    is-equiv-is-invertible'
      ( is-invertible-is-transpose-coherently-invertible H)
```

The following maps are not simple constructions and should not be computed with.
Therefore, we mark them as `abstract`.

```agda
  abstract
    is-coherently-invertible-is-equiv :
      is-equiv f → is-coherently-invertible f
    is-coherently-invertible-is-equiv =
      is-coherently-invertible-is-invertible ∘ is-invertible-is-equiv

  abstract
    is-transpose-coherently-invertible-is-equiv :
      is-equiv f → is-transpose-coherently-invertible f
    is-transpose-coherently-invertible-is-equiv =
      is-transpose-coherently-invertible-is-invertible ∘ is-invertible-is-equiv
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  map-inv-is-equiv : B → A
  map-inv-is-equiv = pr1 (is-invertible-is-equiv H)

  is-section-map-inv-is-equiv : is-section f map-inv-is-equiv
  is-section-map-inv-is-equiv =
    is-section-map-inv-is-coherently-invertible-is-invertible
      ( is-invertible-is-equiv H)

  is-retraction-map-inv-is-equiv : is-retraction f map-inv-is-equiv
  is-retraction-map-inv-is-equiv =
    is-retraction-map-inv-is-coherently-invertible-is-invertible
      ( is-invertible-is-equiv H)

  coherence-map-inv-is-equiv :
    coherence-is-coherently-invertible f
      ( map-inv-is-equiv)
      ( is-section-map-inv-is-equiv)
      ( is-retraction-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coh-is-coherently-invertible-is-invertible (is-invertible-is-equiv H)

  is-equiv-map-inv-is-equiv : is-equiv map-inv-is-equiv
  is-equiv-map-inv-is-equiv =
    is-equiv-is-invertible f
      ( is-retraction-map-inv-is-equiv)
      ( is-section-map-inv-is-equiv)
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  is-section-map-inv-equiv : is-section (map-equiv e) map-inv-equiv
  is-section-map-inv-equiv = is-section-map-inv-is-equiv (is-equiv-map-equiv e)

  is-retraction-map-inv-equiv : is-retraction (map-equiv e) map-inv-equiv
  is-retraction-map-inv-equiv =
    is-retraction-map-inv-is-equiv (is-equiv-map-equiv e)

  coherence-map-inv-equiv :
    coherence-is-coherently-invertible
      ( map-equiv e)
      ( map-inv-equiv)
      ( is-section-map-inv-equiv)
      ( is-retraction-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv
  is-equiv-map-inv-equiv = is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

  inv-equiv : B ≃ A
  pr1 inv-equiv = map-inv-equiv
  pr2 inv-equiv = is-equiv-map-inv-equiv

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  retract-equiv : A ≃ B → A retract-of B
  retract-equiv e =
    ( map-equiv e , map-inv-equiv e , is-retraction-map-inv-equiv e)

  retract-inv-equiv : B ≃ A → A retract-of B
  retract-inv-equiv e =
    ( map-inv-equiv e , map-equiv e , is-section-map-inv-equiv e)
```
