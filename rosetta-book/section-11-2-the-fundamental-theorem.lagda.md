# Section 11.2 The fundamental theorem

```agda
module section-11-2-the-fundamental-theorem where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-2-singleton-induction
open import section-11-1-families-of-equivalences
open import exercise-10-3-contractible-equivalences
```

<!-- rosetta-item: section-11.2 -->

The fundamental theorem of identity types (Theorem 11.2.2) is a general theorem that can be used to characterize the identity type of a given type.
It describes necessary and sufficient conditions on a type family `B` over a type `A` equipped with a point `a:A` to obtain an equivalence `(a=x)≃ B(x)` for each `x:A`.

One of those conditions is that the family `B` satisfies an induction principle that is similar to the identification elimination principle.
Such families are called *identity systems*, which we will introduce now.

## Definition 11.2.1

<!-- rosetta-item: definition-11.2.1; latex-label: defn:identity-system -->

Let `A` be a type equipped with a term `a:A`.
A **(unary) identity system** on `A` at `a` consists of a type family `B` over `A` equipped with `b:B(a)`, such that for any family of types `P(x,y)` indexed by `x:A` and `y:B(x)`, the function
```text
h↦ h(a,b):(Π(x:A) Π(y:B(x)) P(x,y))→ P(a,b)
```
has a section.

<!-- rosetta-agda-block: definition-11.2.1-evaluation -->

```agda
ev-refl-identity-system :
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {a : A} (b : B a)
  {P : (x : A) (y : B x) → Type l3} →
  ((x : A) (y : B x) → P x y) → P a b
ev-refl-identity-system {a = a} b f = f a b
```

<!-- rosetta-agda-block: definition-11.2.1-identity-system-level -->

```agda
module _
  {l1 l2 : Level} (l : Level) {A : Type l1} (B : A → Type l2) (a : A) (b : B a)
  where

  is-identity-system-Level : Type (l1 ⊔ l2 ⊔ lsuc l)
  is-identity-system-Level =
    (P : (x : A) (y : B x) → Type l) → section (ev-refl-identity-system b {P})
```

<!-- rosetta-agda-block: definition-11.2.1-identity-system -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) (a : A) (b : B a)
  where

  is-identity-system : Typeω
  is-identity-system = {l : Level} → is-identity-system-Level l B a b
```
<!-- rosetta-item-end: definition-11.2.1 -->

In other words, if `B` is an identity system on `A` at `a` and `P` is a family of types indexed by `x:A` and `y:B(x)`, then there is for each `p:P(a,b)` a dependent function
```text
f:Π(x:A) Π(y:B(x)) P(x,y)
```
such that `f(a,b)=p`.
This is of course a variant of identification elimination, where the computation rule is given by an identification rather than as a judgmental equality.

We will state the fundamental theorem of identity types in a way that makes it maximally applicable.
The fundamental theorem starts off with assuming a type `A` equipped with a base point `a:A`, and a type family `B` over `A` equipped with a point `b:B(a)`.
Furthermore it assumes an arbitrary family of maps
```text
f:Π(x:A) (a=x)→ B(x)
```
equipped with an identification `f(a,refl)=b`.
The theorem asserts conditions that are equivalent to `f` being a family of equivalences.

In the setup of the fundamental theorem of identity types we can always construct the family of maps
```text
f≔path-ind_a(b):Π(x:A) (a=x)→ B(x)
```
for which the judgmental equality `f(a,refl)≐ b` holds.
So you may wonder why we choose to formulate the fundamental theorem of identity types using a general family of maps `f`.
The reason is that it is somewhat common to apply the fundamental theorem of identity types in order to conclude that `f` is a family of equivalences, even when `f` is not by definition the canonical family of maps, and we want to be free to do so.

The most important implication in the fundamental theorem is that (ii) implies (i).
Occasionally we will also use the third equivalent statement.

## Theorem 11.2.2

<!-- rosetta-item: theorem-11.2.2; latex-label: thm:id_fundamental -->

Let `A` be a type with `a:A`, and let `B` be a type family over `A` equipped with a point `b:B(a)`.
Furthermore, consider a family of maps
```text
f:Π(x:A) (a=x)→ B(x)
```
equipped with an identification `f(a,refl)=b`.
Then the following are equivalent:

1.  The family of maps `f` is a family of equivalences.

2.  The total space
```text
Σ(x:A) B(x)
```
    is contractible.

3.  The family `B` equipped with `b:B(a)` is an identity system.

In particular, we see that for any `b:B(a)`, the canonical family of maps
```text
path-ind_a(b):Π(x:A) (a=x)→ B(x)
```
is a family of equivalences if and only if `Σ(x:A) B(x)` is contractible.

### Proof

<!-- rosetta-item: subheading-11.2-proof -->

*Proof.* First we show that (i) and (ii) are equivalent.
By Theorem 11.1.3 it follows that the family of maps `f` is a family of equivalences if and only if it induces an equivalence
```text
(Σ(x:A) a=x) ≃ (Σ(x:A) B(x))
```
on total spaces.
We have that `Σ(x:A) a=x` is contractible, so it follows by Exercise 10.3 that `tot(f)` is an equivalence if and only if `Σ(x:A) B(x)` is contractible.

Now we show that (ii) and (iii) are equivalent.
Note that we have the following commuting triangle
<!-- rosetta-diagram: 5c2d1dec28fc; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[Π(t:Σ(x:A) B(x)) P(t)]                  [Π(x:A) Π(y:B(x)) P(x,y)]

                            [P(a,b)]

Arrows:
- Π(t:Σ(x:A) B(x)) P(t) --ev-pair--> Π(x:A) Π(y:B(x)) P(x,y)
- Π(t:Σ(x:A) B(x)) P(t) --{ev-pt(a,b)}--> P(a,b)
- Π(x:A) Π(y:B(x)) P(x,y) --{λ h. h(a,b)}--> P(a,b)
```
In this diagram the top map has a section.
Therefore it follows by Exercise 9.4 that the left map has a section if and only if the right map has a section.
Recall from Definition 10.2.1 that the type `Σ(x:A) B(x)` satisfies singleton induction if and only if the left map in the triangle has a section for each `P`.
Therefore we conclude our proof with Theorem 10.2.3, which shows that the type `Σ(x:A) B(x)` satisfies singleton induction if and only if it is contractible. ◻

<!-- rosetta-agda-block: theorem-11.2.2-fundamental-theorem -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {a : A}
  where

  abstract
    fundamental-theorem-id :
      is-contr (Σ A B) → (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id is-torsorial-B f =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot f) (is-contr-Id a) is-torsorial-B)

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f → is-contr (Σ A B)
    fundamental-theorem-id' f is-fiberwise-equiv-f =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot f)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
        ( is-contr-Id a)
```

<!-- rosetta-agda-block: theorem-11.2.2-identity-system-from-contractibility -->

```agda
is-identity-system-is-contr :
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (a : A) (b : B a) →
  is-contr (Σ A B) → is-identity-system B a b
pr1 (is-identity-system-is-contr a b H P) p =
  ev-pair (ind-singleton (a , b) H (λ t → P (pr1 t) (pr2 t)) p)
pr2 (is-identity-system-is-contr a b H P) =
  compute-ind-singleton (a , b) H (λ t → P (pr1 t) (pr2 t))
```

<!-- rosetta-agda-block: theorem-11.2.2-contractibility-from-identity-system -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (a : A) (b : B a)
  where

  abstract
    is-torsorial-is-identity-system :
      is-identity-system B a b → is-contr (Σ A B)
    pr1 (is-torsorial-is-identity-system H) = (a , b)
    pr2 (is-torsorial-is-identity-system H) (x , y) =
      pr1 (H (λ x' y' → (a , b) ＝ (x' , y'))) refl x y

  abstract
    fundamental-theorem-id-is-identity-system :
      is-identity-system B a b →
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id-is-identity-system H =
      fundamental-theorem-id (is-torsorial-is-identity-system H)
```

<!-- rosetta-agda-block: theorem-11.2.2-canonical-family -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (a : A) (b : B a)
  where

  abstract
    fundamental-theorem-id-J :
      is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J is-torsorial-B =
      fundamental-theorem-id is-torsorial-B (ind-Id a (λ x p → B x) b)

  abstract
    fundamental-theorem-id-J' :
      is-fiberwise-equiv (ind-Id a (λ x p → B x) b) → is-contr (Σ A B)
    fundamental-theorem-id-J' H =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot (ind-Id a (λ x p → B x) b))
        ( is-equiv-tot-is-fiberwise-equiv H)
        ( is-contr-Id a)
```
<!-- rosetta-item-end: theorem-11.2.2 -->
