# Section 13.2 Identity systems on Π-types

```agda
module section-13-2-identity-systems-on-pi-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
```

Recall from Section 11.6 that the *structure identity principle* is a way to obtain an identity system on a `Σ`-type.
Identity systems were defined in Definition 11.2.1.
In this section we will describe how to obtain identity systems on a `Π`-type.
We will first show that `Π`-types distribute over `Σ`-types.
This theorem is sometimes called the *type theoretic principle of choice* because it can be seen as the Curry-Howard interpretation of the axiom of choice.

## Theorem 13.2.1

Consider a family of types `C(x,y)` indexed by `x : A` and `y : B(x)`.
Then the map

```text
  choice : (Π(x : A) Σ(y : B(x)) C(x,y)) → (Σ(f : Π(x : A) B(x)) Π(x : A) C(x,f(x)))
```

given by

```text
  choice(h) ≔ ( λ x. pr1(h(x)), λ x. pr2(h(x))).
```

is an equivalence.

### Proof

We define the map

```text
  choice⁻¹ : (Σ(f : Π(x : A) B(x)) Π(x : A) C(x,f(x))) → Π(x : A) Σ(y : B(x)) C(x,y)
```

by `choice⁻¹(f,g) ≔ λ x. (f(x),g(x))`.
Then we have to construct homotopies

```text
  choice ∘ choice⁻¹ ~ id,    and    choice⁻¹ ∘ choice ~ id.
```

For the first homotopy it suffices to construct an identification

```text
  choice(choice⁻¹(f,g)) = (f,g)
```

for any `f : Π(x : A) B(x)` and any `g : Π(x : A) C(x,f(x))`.
We compute the left-hand side as follows:

```text
  choice(choice⁻¹(f,g)) ≐ choice(λ x. (f(x),g(x))) ≐ (λ x. f(x), λ x. g(x)).
```

By the `η`-rule for `Π`-types we have the judgmental equalities `f ≐ λ x. f(x)` and `g ≐ λ x. g(x)`.
Therefore we have the identification

```text
  refl : choice(choice⁻¹(f,g)) = (f,g).
```

This completes the construction of the first homotopy.

For the second homotopy we have to construct an identification

```text
  choice⁻¹(choice(h)) = h
```

for any `h : Π(x : A) Σ(y : B(x)) C(x,y)`.
We compute the left-hand side as follows:

```text
  choice⁻¹(choice(h))
  ≐ choice⁻¹(λ x. pr1(h(x)), λ x. pr2(h(x)))
  ≐ λ x. (pr1(h(x)),pr2(h(x)))
```

However, it is *not* the case that `(pr1(h(x)), pr2(h(x))) ≐ h(x)` for any `h : Π(x : A) Σ(y : B(x)) C(x,y)`.
Nevertheless, we have the identification

```text
  eq-pair(refl,refl) : (pr1(h(x)), pr2(h(x))) = h(x).
```

Therefore we obtain the required homotopy by function extensionality:

```text
  λ h. eq-htpy(λ x. eq-pair(refl,refl)) : choice⁻¹ ∘ choice ~ id. ◻
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3)
  where

  Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  Π-total-fam = (x : A) → Σ (B x) (C x)

  universally-structured-Π : UU (l1 ⊔ l2 ⊔ l3)
  universally-structured-Π = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

  implicit-Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  implicit-Π-total-fam = {x : A} → Σ (B x) (C x)

  universally-structured-implicit-Π : UU (l1 ⊔ l2 ⊔ l3)
  universally-structured-implicit-Π =
    Σ ({x : A} → B x) (λ f → {x : A} → C x (f {x}))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  map-distributive-Π-Σ : Π-total-fam C → universally-structured-Π C
  pr1 (map-distributive-Π-Σ φ) x = pr1 (φ x)
  pr2 (map-distributive-Π-Σ φ) x = pr2 (φ x)

  map-inv-distributive-Π-Σ : universally-structured-Π C → Π-total-fam C
  pr1 (map-inv-distributive-Π-Σ ψ x) = (pr1 ψ) x
  pr2 (map-inv-distributive-Π-Σ ψ x) = (pr2 ψ) x

  is-section-map-inv-distributive-Π-Σ :
    map-distributive-Π-Σ ∘ map-inv-distributive-Π-Σ ~ id
  is-section-map-inv-distributive-Π-Σ (ψ , ψ') = refl

  is-retraction-map-inv-distributive-Π-Σ :
    map-inv-distributive-Π-Σ ∘ map-distributive-Π-Σ ~ id
  is-retraction-map-inv-distributive-Π-Σ φ = refl

  abstract
    is-equiv-map-distributive-Π-Σ : is-equiv (map-distributive-Π-Σ)
    is-equiv-map-distributive-Π-Σ =
      is-equiv-is-invertible
        ( map-inv-distributive-Π-Σ)
        ( is-section-map-inv-distributive-Π-Σ)
        ( is-retraction-map-inv-distributive-Π-Σ)

  distributive-Π-Σ : Π-total-fam C ≃ universally-structured-Π C
  pr1 distributive-Π-Σ = map-distributive-Π-Σ
  pr2 distributive-Π-Σ = is-equiv-map-distributive-Π-Σ

  abstract
    is-equiv-map-inv-distributive-Π-Σ : is-equiv (map-inv-distributive-Π-Σ)
    is-equiv-map-inv-distributive-Π-Σ =
      is-equiv-is-invertible
        ( map-distributive-Π-Σ)
        ( is-retraction-map-inv-distributive-Π-Σ)
        ( is-section-map-inv-distributive-Π-Σ)

  inv-distributive-Π-Σ : universally-structured-Π C ≃ Π-total-fam C
  pr1 inv-distributive-Π-Σ = map-inv-distributive-Π-Σ
  pr2 inv-distributive-Π-Σ = is-equiv-map-inv-distributive-Π-Σ

  map-distributive-implicit-Π-Σ :
    implicit-Π-total-fam C → universally-structured-implicit-Π C
  pr1 (map-distributive-implicit-Π-Σ φ) {x} = pr1 (φ {x})
  pr2 (map-distributive-implicit-Π-Σ φ) {x} = pr2 (φ {x})

  map-inv-distributive-implicit-Π-Σ :
    universally-structured-implicit-Π C → implicit-Π-total-fam C
  pr1 (map-inv-distributive-implicit-Π-Σ ψ {x}) = pr1 ψ
  pr2 (map-inv-distributive-implicit-Π-Σ ψ {x}) = pr2 ψ

  is-section-map-inv-distributive-implicit-Π-Σ :
    ( ( map-distributive-implicit-Π-Σ) ∘
      ( map-inv-distributive-implicit-Π-Σ)) ~ id
  is-section-map-inv-distributive-implicit-Π-Σ (ψ , ψ') = refl

  is-retraction-map-inv-distributive-implicit-Π-Σ :
    ( ( map-inv-distributive-implicit-Π-Σ) ∘
      ( map-distributive-implicit-Π-Σ)) ~ id
  is-retraction-map-inv-distributive-implicit-Π-Σ φ = refl

  abstract
    is-equiv-map-distributive-implicit-Π-Σ :
      is-equiv (map-distributive-implicit-Π-Σ)
    is-equiv-map-distributive-implicit-Π-Σ =
      is-equiv-is-invertible
        ( map-inv-distributive-implicit-Π-Σ)
        ( is-section-map-inv-distributive-implicit-Π-Σ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σ)

  distributive-implicit-Π-Σ :
    implicit-Π-total-fam C ≃ universally-structured-implicit-Π C
  pr1 distributive-implicit-Π-Σ = map-distributive-implicit-Π-Σ
  pr2 distributive-implicit-Π-Σ = is-equiv-map-distributive-implicit-Π-Σ

  abstract
    is-equiv-map-inv-distributive-implicit-Π-Σ :
      is-equiv (map-inv-distributive-implicit-Π-Σ)
    is-equiv-map-inv-distributive-implicit-Π-Σ =
      is-equiv-is-invertible
        ( map-distributive-implicit-Π-Σ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σ)
        ( is-section-map-inv-distributive-implicit-Π-Σ)

  inv-distributive-implicit-Π-Σ :
    (universally-structured-implicit-Π C) ≃ (implicit-Π-total-fam C)
  pr1 inv-distributive-implicit-Π-Σ = map-inv-distributive-implicit-Π-Σ
  pr2 inv-distributive-implicit-Π-Σ = is-equiv-map-inv-distributive-implicit-Π-Σ
```

The fact that `Π`-types distribute over `Σ`-types has many useful consequences.
The most straightforward consequence is the following.

## Corollary 13.2.2

For any two types `A` and `B`, and any type family `C` over `B`, we have an equivalence

```text
  (A → Σ(y : B) C(y)) ≃ (Σ(f : A → B) Π(x : A) C(f(x))).
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  where

  mapping-into-Σ : (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
  mapping-into-Σ = map-distributive-Π-Σ {B = λ _ → B}

  abstract
    is-equiv-mapping-into-Σ : is-equiv mapping-into-Σ
    is-equiv-mapping-into-Σ = is-equiv-map-distributive-Π-Σ

  equiv-mapping-into-Σ :
    (A → Σ B C) ≃ Σ (A → B) (λ f → (x : A) → C (f x))
  pr1 equiv-mapping-into-Σ = mapping-into-Σ
  pr2 equiv-mapping-into-Σ = is-equiv-mapping-into-Σ
```

Another direct consequence of the distributivity of `Π`-types over `Σ`-types is the fact that

```text
  Π(b : B) fib(f, b) ≃ Σ(g : B → A) f ∘ g ~ id.
```

### Products of fibers and sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-split-surjective : (A → B) → UU (l1 ⊔ l2)
  is-split-surjective f = (b : B) → fiber f b

  split-surjection : UU (l1 ⊔ l2)
  split-surjection = Σ (A → B) is-split-surjective

  map-split-surjection : split-surjection → (A → B)
  map-split-surjection = pr1

  is-split-surjective-split-surjection :
    (f : split-surjection) → is-split-surjective (map-split-surjection f)
  is-split-surjective-split-surjection = pr2

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  section-is-split-surjective : is-split-surjective f → section f
  pr1 (section-is-split-surjective s) = pr1 ∘ s
  pr2 (section-is-split-surjective s) = pr2 ∘ s

  is-split-surjective-section : section f → is-split-surjective f
  pr1 (is-split-surjective-section s b) = pr1 s b
  pr2 (is-split-surjective-section s b) = pr2 s b

  equiv-section-is-split-surjective : is-split-surjective f ≃ section f
  equiv-section-is-split-surjective = distributive-Π-Σ

  equiv-is-split-surjective-section : section f ≃ is-split-surjective f
  equiv-is-split-surjective-section = inv-distributive-Π-Σ
```

In the following corollary we use the distributivity of `Π`-types over `Σ`-types to show that dependent functions are sections of projection maps.

## Corollary 13.2.3

Consider a type family `B` over `A`, and consider the projection map

```text
  pr1 : (Σ(x : A) B(x)) → A.
```

Then we have an equivalence

```text
  sec(pr1) ≃ Π(x : A) B(x).
```

### Proof

Theorem 13.2.1 gives the first equivalence in the following calculation:

```text
  Σ(h : A → Σ(x : A) B(x)) pr1 ∘ h ~ id
  ≃ Σ((f,g) : Σ(f : A → A) Π(x : A) B(f(x))) f ~ id
  ≃ Σ((f,H) : Σ(f : A → A) f ~ id) Π(x : A) B(f(x))
  ≃ Π(x : A) B(x)
```

In the second equivalence we used Exercise 9.5 to swap the family `f ↦ Π(x : A) B(f(x))` with the family `f ↦ f ~ id`, and in the third equivalence we used the fact that

```text
  Σ(f : A → A) f ~ id
```

is contractible, with center of contraction `(id,refl-htpy)`.
One way to see that it is contractible is by Exercise 13.1.
A direct way to see this, is by another application of Theorem 13.2.1.
This gives an equivalence

```text
  (Σ(f : A → A) f ~ id) ≃ (Π(x : A) Σ(y : A) y = x),
```

and the right-hand side is a product of contractible types. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-section-pr1 : section (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-section-pr1 =
    ( left-unit-law-Σ-is-contr
      ( is-contr-equiv
        ( Π-total-fam (λ x y → y ＝ x))
        ( inv-distributive-Π-Σ)
        ( is-contr-Π is-torsorial-Id'))
      ( id , refl-htpy)) ∘e
    ( equiv-right-swap-Σ) ∘e
    ( equiv-Σ-equiv-base ( λ s → pr1 s ~ id) ( distributive-Π-Σ))
```

In the final application of distributivity of `Π`-types over `Σ`-types we obtain a general way of constructing identity systems of `Π`-types.

## Theorem 13.2.4

Consider a family `B` of types over `A`, and for each `b : B(a)` consider an identity system `E(b)` at `b`.
Furthermore, consider a dependent function `f : Π(x : A) B(x)`.
Then the family of types

```text
  Π(x : A) E(f(x),g(x))
```

indexed by `g : Π(x : A) B(x)` is an identity system at `f`.

### Proof

*Proof.* By Theorem 11.2.2 it suffices to show that the type

```text
  Σ(g : Π(x : A) B(x)) Π(x : A) E(f(x),g(x))
```

is contractible.
By Theorem 13.2.1 it follows that this type is equivalent to the type

```text
  Π(x : A) Σ(y : B(x)) E(f(x),y).
```

This is a product of contractible types because each `E(f(x))` is an identity system at `f(x) : B(x)`.
This product is therefore contractible by the weak function extensionality principle. ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (is-torsorial-C : (x : A) → is-torsorial (C x))
  where

  is-torsorial-Eq-Π : is-torsorial (λ g → (x : A) → C x (g x))
  is-torsorial-Eq-Π =
    is-contr-equiv'
      ( (x : A) → Σ (B x) (C x))
      ( distributive-Π-Σ)
      ( is-contr-Π is-torsorial-C)

  is-torsorial-Eq-implicit-Π : is-torsorial (λ g → {x : A} → C x (g {x}))
  is-torsorial-Eq-implicit-Π =
    is-contr-equiv
      ( Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
      ( equiv-Σ
        ( λ g → (x : A) → C x (g x))
        ( equiv-explicit-implicit-Π)
        ( λ _ → equiv-explicit-implicit-Π))
      ( is-torsorial-Eq-Π)

  is-torsorial-Eq-implicit-Π' : is-torsorial (λ g → (x : A) → C x (g {x}))
  is-torsorial-Eq-implicit-Π' =
    is-contr-equiv
      ( Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
      ( equiv-Σ-equiv-base
        ( λ g → (x : A) → C x (g x))
        ( equiv-explicit-implicit-Π))
      ( is-torsorial-Eq-Π)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x)
  (Eq-B : (x : A) → B x → UU l3)
  where

  map-extensionality-Π :
    ( (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
    ( g : (x : A) → B x) → f ＝ g → ((x : A) → Eq-B x (g x))
  map-extensionality-Π e .f refl x = map-equiv (e x (f x)) refl

  abstract
    is-equiv-map-extensionality-Π :
      (e : (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
      (g : (x : A) → B x) → is-equiv (map-extensionality-Π e g)
    is-equiv-map-extensionality-Π e =
      fundamental-theorem-id
        ( is-torsorial-Eq-Π
          ( λ x →
            fundamental-theorem-id'
              ( λ y → map-equiv (e x y))
              ( λ y → is-equiv-map-equiv (e x y))))
        ( map-extensionality-Π e)

  extensionality-Π :
    ( (x : A) (y : B x) → (f x ＝ y) ≃ Eq-B x y) →
    ( g : (x : A) → B x) → (f ＝ g) ≃ ((x : A) → Eq-B x (g x))
  pr1 (extensionality-Π e g) = map-extensionality-Π e g
  pr2 (extensionality-Π e g) = is-equiv-map-extensionality-Π e g
```

Note: Agda-unimath does not contain the proof that Eq-Π is an identity system, even though it is a straightforward corollary of what we have formalized so far.
