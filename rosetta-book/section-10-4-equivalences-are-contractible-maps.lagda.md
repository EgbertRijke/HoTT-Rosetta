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

<!-- rosetta-item: section-10.4 -->

In Theorem 10.4.6 we will show the converse to Theorem 10.3.5, i.e., we will show that any equivalence is a contractible map.
We will do this in two steps.

First we introduce a new notion of *coherently invertible map*, for which we can easily show that such maps have contractible fibers.
Then we show that any equivalence is a coherently invertible map.

Recall that an invertible map is a map `f:A→ B` equipped with `g:B→ A` and homotopies
```text
G : f∘ g ~ id and H:g∘ f~ id.
```
Then we observe that both `G · f` and `f · H` are homotopies of the same type
```text
f∘ g∘ f ~ f.
```
A coherently invertible map is an invertible map for which there is a further homotopy `G · f~ f· H`.

## Definition 10.4.1

<!-- rosetta-item: definition-10.4.1 -->

Consider a map `f:A→ B`.
We say that `f` is **coherently invertible** if it comes equipped with
```text
g : B → A
G : f ∘ g ~ id
H : g ∘ f ~ id
K : G · f ~ f · H.
```
We will write `is-coh-invertible(f)` for the type of quadruples `(g,G,H,K)`.

<!-- rosetta-agda-block: definition-10.4.1-coherently-invertible -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : f ∘ g ~ id) (H : g ∘ f ~ id) → Type (l1 ⊔ l2)
  coherence-is-coherently-invertible f g G H = G ·r f ~ f ·l H

  is-coherently-invertible : (A → B) → Type (l1 ⊔ l2)
  is-coherently-invertible f =
    Σ ( B → A)
      ( λ g →
        Σ ( f ∘ g ~ id)
          ( λ G →
            Σ ( g ∘ f ~ id)
              ( λ H → coherence-is-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
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
```
<!-- rosetta-item-end: definition-10.4.1 -->

Although we will encounter the notion of coherently invertible map on some further occasions, the following proposition is our main motivation for considering it.

## Proposition 10.4.2

<!-- rosetta-item: proposition-10.4.2; latex-label: lem:contr-inv -->

Any coherently invertible map has contractible fibers.

### Proof

<!-- rosetta-item: subheading-10.4-proof -->

*Proof.* Consider a map `f:A→ B` equipped with
```text
g : B → A
G : f ∘ g ~ id
H : g ∘ f ~ id
K : G · f ~ f · H,
```
and let `y:B`.
Our goal is to show that `fib(f, y)` is contractible.
For the center of contraction we take `(g(y),G(y))`.
In order to construct a contraction, it suffices to construct a dependent function of type
```text
Π(x:A) Π(p:f(x)=y) Eq-fib_f((g(y),G(y)),(x,p)).
```
By path induction on `p:f(x)=y` it suffices to construct a dependent function of type
```text
Π(x:A) Eq-fib_f((g(f(x)),G(f(x))),(x,refl)).
```
By definition of `Eq-fib_f`, we have to construct for each `x:A` an identification `α:g(f(x))=x` equipped with a further identification
```text
G(f(x))=ap_{f}(α) ∙ refl.
```
Such a dependent function is constructed as `λ x. (H(x),K'(x))`, where the homotopy `H:g∘ f~ id` is given by assumption, and the homotopy
```text
K' : Π(x:A) G(f(x))=ap_{f}(H(x)) ∙ refl
```
is defined as
```text
K'≔ K ∙ right-unit-htpy(f· H)^{-1}.
```
 ◻

<!-- rosetta-agda-block: proposition-10.4.2-coherently-invertible-contractible -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
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
<!-- rosetta-item-end: proposition-10.4.2 -->

Our next goal is to show that for any map `f:A→ B` equipped with
```text
g:B→ A, G:f∘ g ~ id, and H:g∘ f~ id,
```
we can improve the homotopy `G` to a new homotopy `G':f∘ g~ id` for which there is a further homotopy
```text
f· H~ G'· f.
```
Note that this situation is analogous to the situation in the proof of Theorem 10.2.3, where we improved the contraction `C` so that it satisfied `C(c)=refl`.
The extra coherence `f· H~ G'· f` is then used in the proof that the fibers of an equivalence are contractible.

## Definition 10.4.3

<!-- rosetta-item: definition-10.4.3; latex-label: defn:htpy_nat -->

Let `f,g:A→ B` be functions, and consider `H:f~ g` and `p:x=y` in `A`.
We define the identification
```text
nat-htpy(H,p) ≔ ap_{f}(p) ∙ H(y)=H(x) ∙ ap_{g}(p)
```
witnessing that the square
<!-- rosetta-diagram: a2f4fce2f636; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[f(x)]---->[g(x)]
  |          |
[f(y)]---->[g(y)]

Arrows:
- f(x) --H(x)--> g(x)
- f(x) --ap_{f}(p)--> f(y)
- g(x) --ap_{g}(p)--> g(y)
- f(y) --H(y)--> g(y)
```
commutes.
This square is also called the **naturality square** of the homotopy `H` at `p`.

### Construction

<!-- rosetta-item: subheading-10.4-construction -->

By path induction on `p` it suffices to construct an identification
```text
ap_{f}(refl) ∙ H(x)=H(x) ∙ ap_{g}(refl)
```
since `ap_{f}(refl)≐ refl` and `ap_{g}(refl)≐refl`, and since `refl ∙ H(x)≐ H(x)`, we see that the path `right-unit(H(x))^{-1}` is of the asserted type.

<!-- rosetta-agda-block: definition-10.4.3-naturality -->

```agda
nat-htpy :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  H x ∙ ap g p ＝ ap f p ∙ H y
nat-htpy H refl = right-unit
```
<!-- rosetta-item-end: definition-10.4.3 -->

## Definition 10.4.4

<!-- rosetta-item: definition-10.4.4; latex-label: defn:retraction_swap -->

Consider `f:A→ A` and `H: f~ id[A]`.
We construct an identification `H(f(x))=ap_{f}(H(x))`, for any `x:A`.

### Construction

<!-- rosetta-item: subheading-10.4-construction-2 -->

By the naturality of homotopies with respect to identifications the square
<!-- rosetta-diagram: e9ca675c5778; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[ff(x)]---->[f(x)]
   |          |
 [f(x)]----> [x]

Arrows:
- ff(x) --ap_{f}(H(x))--> f(x)
- ff(x) --H(f(x))--> f(x)
- f(x) --H(x)--> x
- f(x) --H(x)--> x
```
commutes.
This gives the desired identification `H(f(x))=ap_{f}(H(x))`.

<!-- rosetta-agda-block: definition-10.4.4-retraction-swap -->

```agda
nat-htpy-id :
  {l : Level} {A : Type l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → H x ∙ p ＝ ap f p ∙ H y
nat-htpy-id H refl = right-unit
```
<!-- rosetta-item-end: definition-10.4.4 -->

## Lemma 10.4.5

<!-- rosetta-item: lemma-10.4.5; latex-label: lem:coherently-invertible -->

Let `f:A→ B` be a map equipped with an inverse, i.e., consider
```text
g : B → A
G : f ∘ g ~ id
H : g ∘ f ~ id.
```
Then there is a homotopy `G':f∘ g~ id` equipped with a further homotopy
```text
K : f· H ~ G'· f.
```
Thus we obtain a map `has-inverse(f)→is-coh-invertible(f)`.

### Proof

<!-- rosetta-item: subheading-10.4-proof-2 -->

*Proof.* For each `y:B`, we construct the identification `G'(y)` as the concatenation
<!-- rosetta-diagram: b0f70c6cf179; review: pending -->

*Linear diagram (automatic draft).*

```text
[fg(y)]---->[[2.5em] fgfg(y)]---->[[2.5em] fg(y)]----> [y]

Arrows:
- fg(y) --{G(fg(y))}^{-1}--> [2.5em] fgfg(y)
- [2.5em] fgfg(y) --ap_{f}(H(g(y)))--> [2.5em] fg(y)
- [2.5em] fg(y) --G(y)--> y
```
In order to construct a homotopy `f· H ~ G'· f`, it suffices to show that the square
<!-- rosetta-diagram: d894f03c5f8d; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[fgfgf(x)]---->[fgf(x)]
    |             |
 [fgf(x)] ----> [f(x)]

Arrows:
- fgfgf(x) --{G(fgf(x))}--> fgf(x)
- fgfgf(x) --ap_{f}(H(gf(x)))--> fgf(x)
- fgf(x) --ap_{f}(H(x))--> f(x)
- fgf(x) --G(f(x))--> f(x)
```
commutes for every `x:A`.
Recall from Definition 10.4.4 that we have `H(gf(x))=ap_{gf}(H(x))`.
Using this identification, we see that it suffices to show that the square
<!-- rosetta-diagram: d5e947466295; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[fgfgf(x)]---->[fgf(x)]
    |             |
 [fgf(x)] ----> [f(x)]

Arrows:
- fgfgf(x) --(G· f)(gf(x))--> fgf(x)
- fgfgf(x) --ap_{fgf}(H(x))--> fgf(x)
- fgf(x) --ap_{f}(H(x))--> f(x)
- fgf(x) --(G· f)(x)--> f(x)
```
commutes.
Now we observe that this is just a naturality square the homotopy `G· f:fgf~ f`, which commutes by Definition 10.4.3. ◻

<!-- rosetta-agda-block: lemma-10.4.5-concatenation-injective-helper -->

```agda
module _
  {l1 : Level} {A : Type l1}
  where

  is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ q ＝ p ∙ r → q ＝ r
  is-injective-concat refl s = s

  is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → p ∙ r ＝ q ∙ r → p ＝ q
  is-injective-concat' refl s = inv right-unit ∙ s ∙ right-unit
```

<!-- rosetta-agda-block: lemma-10.4.5-identification-whisker-helper -->

```agda
module _
  {l : Level} {A : Type l}
  where

  right-whisker-concat : {x y z : A} {p q : x ＝ y} → p ＝ q → (r : y ＝ z) → p ∙ r ＝ q ∙ r
  right-whisker-concat α q = ap (_∙ q) α
```

<!-- rosetta-agda-block: lemma-10.4.5-transpose-homotopy-helper -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h) (M : H ∙h K ~ L)
  where

  left-transpose-htpy-concat : K ~ inv-htpy H ∙h L
  left-transpose-htpy-concat x =
    left-transpose-eq-concat (H x) (K x) (L x) (M x)

  inv-htpy-left-transpose-htpy-concat : inv-htpy H ∙h L ~ K
  inv-htpy-left-transpose-htpy-concat = inv-htpy left-transpose-htpy-concat
```

<!-- rosetta-agda-block: lemma-10.4.5-whisker-concatenation-helper -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  right-whisker-concat-htpy :
    {f g h : (x : A) → B x} {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J
  right-whisker-concat-htpy K J x = right-whisker-concat (K x) (J x)
```

<!-- rosetta-agda-block: lemma-10.4.5-composition-whisker-helper -->

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Type l1} {B : A → Type l2} {C : A → Type l3} {D : A → Type l4}
  where

  inv-preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    (k ∘ h) ·l H ~ k ·l (h ·l H)
  inv-preserves-comp-left-whisker-comp k h H x = ap-comp k h (H x)

  preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    k ·l (h ·l H) ~ (k ∘ h) ·l H
  preserves-comp-left-whisker-comp k h H =
    inv-htpy (inv-preserves-comp-left-whisker-comp k h H)
```

<!-- rosetta-agda-block: lemma-10.4.5-higher-whisker-helper -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3}
  {f g : (x : A) → B x}
  where

  left-whisker-comp² :
    (h : {x : A} → B x → C x) {H H' : f ~ g} (α : H ~ H') → h ·l H ~ h ·l H'
  left-whisker-comp² h α = ap h ·l α
```

<!-- rosetta-agda-block: lemma-10.4.5-identity-coherence-helper -->

```agda
module _
  {l : Level} {A : Type l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : H ·r f ~ f ·l H
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-coh-htpy-id : f ·l H ~ H ·r f
  inv-coh-htpy-id = inv-htpy coh-htpy-id
```

<!-- rosetta-agda-block: lemma-10.4.5-invertible-coherently-invertible -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (H : is-invertible f)
  where

  is-retraction-map-inv-is-coherently-invertible-is-invertible :
    pr1 H ∘ f ~ id
  is-retraction-map-inv-is-coherently-invertible-is-invertible =
    pr2 (pr2 H)

  abstract
    is-section-map-inv-is-coherently-invertible-is-invertible :
      f ∘ pr1 H ~ id
    is-section-map-inv-is-coherently-invertible-is-invertible =
      ( ( inv-htpy (pr1 (pr2 H))) ·r
        ( f ∘ pr1 H)) ∙h
      ( ( ( f) ·l
          ( pr2 (pr2 H)) ·r
          ( pr1 H)) ∙h
        ( pr1 (pr2 H)))

  abstract
    inv-coh-is-coherently-invertible-is-invertible :
      f ·l is-retraction-map-inv-is-coherently-invertible-is-invertible ~
      is-section-map-inv-is-coherently-invertible-is-invertible ·r f
    inv-coh-is-coherently-invertible-is-invertible =
      left-transpose-htpy-concat
        ( ( pr1 (pr2 H)) ·r
          ( f ∘ pr1 H ∘ f))
        ( f ·l pr2 (pr2 H))
        ( ( ( f) ·l
            ( pr2 (pr2 H)) ·r
            ( pr1 H ∘ f)) ∙h
          ( pr1 (pr2 H) ·r f))
        ( ( ( nat-htpy (pr1 (pr2 H) ·r f)) ·r
            ( pr2 (pr2 H))) ∙h
          ( right-whisker-concat-htpy
            ( ( inv-preserves-comp-left-whisker-comp
                ( f)
                ( pr1 H ∘ f)
                ( pr2 (pr2 H))) ∙h
              ( left-whisker-comp²
                ( f)
                ( inv-coh-htpy-id (pr2 (pr2 H)))))
            ( pr1 (pr2 H) ·r f)))

  abstract
    coh-is-coherently-invertible-is-invertible :
      coherence-is-coherently-invertible
        ( f)
        ( pr1 H)
        ( is-section-map-inv-is-coherently-invertible-is-invertible)
        ( is-retraction-map-inv-is-coherently-invertible-is-invertible)
    coh-is-coherently-invertible-is-invertible =
      inv-htpy inv-coh-is-coherently-invertible-is-invertible

  is-coherently-invertible-is-invertible : is-coherently-invertible f
  is-coherently-invertible-is-invertible =
    ( pr1 H ,
      is-section-map-inv-is-coherently-invertible-is-invertible ,
      is-retraction-map-inv-is-coherently-invertible-is-invertible ,
      coh-is-coherently-invertible-is-invertible)
```
<!-- rosetta-item-end: lemma-10.4.5 -->

Now we put the pieces together to conclude that any equivalence has contractible fibers.

## Theorem 10.4.6

<!-- rosetta-item: theorem-10.4.6; latex-label: thm:contr_equiv -->

Any equivalence is a contractible map.

### Proof

<!-- rosetta-item: subheading-10.4-proof-3 -->

*Proof.* We have seen in Proposition 10.4.2 that any coherently invertible map is a contractible map.
Moreover, any equivalence has the structure of an invertible map by Proposition 9.2.7, and any invertible map is coherently invertible by Lemma 10.4.5. ◻

<!-- rosetta-agda-block: theorem-10.4.6-equivalence-contractible-map -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv =
      is-contr-map-is-coherently-invertible ∘ (is-coherently-invertible-is-invertible ∘ is-invertible-is-equiv)
```
<!-- rosetta-item-end: theorem-10.4.6 -->

The following corollary is very similar to Theorem 10.1.4, which asserts that the type `Σ(x:A) a=x` is contractible.
However, we haven’t yet established that the equivalence `(a=x)≃ (x=a)` induces an equivalence on total spaces.
However, using the fact that equivalences are contractible maps we can give a direct proof.

## Corollary 10.4.7

<!-- rosetta-item: corollary-10.4.7; latex-label: cor:contr_path -->

Let `A` be a type, and let `a:A`.
Then the type
```text
Σ(x:A) x=a
```
is contractible.

### Proof

<!-- rosetta-item: subheading-10.4-proof-4 -->

*Proof.* By Example 9.2.3, the identity function is an equivalence.
Therefore, the fibers of the identity function are contractible by Theorem 10.4.6.
Note that `Σ(x:A) x=a` is exactly the fiber of `id[A]` at `a:A`. ◻

<!-- rosetta-agda-block: corollary-10.4.7-reverse-total-path -->

```agda
module _
  {l : Level} {A : Type l}
  where

  abstract
    is-contr-Id' : (a : A) → is-contr (Σ A (λ x → x ＝ a))
    pr1 (pr1 (is-contr-Id' a)) = a
    pr2 (pr1 (is-contr-Id' a)) = refl
    pr2 (is-contr-Id' a) (.a , refl) = refl
```
<!-- rosetta-item-end: corollary-10.4.7 -->
