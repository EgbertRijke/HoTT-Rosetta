# Section 12.2 Subtypes

```agda
module section-12-2-subtypes where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import exercise-10-3-contractible-equivalences
open import exercise-10-7-fibers-of-projections
```

<!-- rosetta-item: section-12.2 -->

In set theory, a set `y` is said to be a subset of a set `x`, if any element of `y` is an element of `x`, i.e., if the condition
```text
∀_z (z∈ y)→ (z∈ x)
```
holds.
We have already noted that type theory is different from set theory in that terms in type theory come equipped with a *unique* type.
Moreover, in set theory the proposition `x∈ y` is well-formed for any two sets `x` and `y`, whereas in type theory we can only judge that `a:A` by applying the rules of inference of type theory in such a manner that we arrive at the conclusion that `a:A`.
Because of these differences we must find a different way to talk about subtypes.

Note that in set theory there is a correspondence between the subsets of a set `x`, and the *predicates* on `x`.
A predicate on `x` is just a proposition `P(z)` that varies over the elements `z∈ x`.
Indeed, if `y` is a subset of `x`, then the corresponding predicate is the proposition `z∈ y`.
Conversely, if `P` is a predicate on `x`, then we obtain the subset
```text
{z∈ x| P(z)}
```
of `x`.
This observation suggests that in type theory we should define a subtype of a type `A` to be a family of propositions over `A`.

## Definition 12.2.1

<!-- rosetta-item: definition-12.2.1 -->

A type family `B` over `A` is said to be a **subtype** of `A` if for each `x:A` the type `B(x)` is a proposition.
When `B` is a subtype of `A`, we also say that `B(x)` is a **property** of `x:A`.

<!-- rosetta-agda-block: definition-12.2.1-subtypes -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2)
  where

  is-subtype : Type (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : Type (l1 ⊔ l2)
  is-property = is-subtype

subtype : {l1 : Level} (l : Level) (A : Type l1) → Type (l1 ⊔ lsuc l)
subtype l A = A → Prop l

module _
  {l1 l2 : Level} {A : Type l1} (P : subtype l2 A)
  where

  is-in-subtype : A → Type l2
  is-in-subtype x = type-Prop (P x)

  is-prop-is-in-subtype : (x : A) → is-prop (is-in-subtype x)
  is-prop-is-in-subtype x = is-prop-type-Prop (P x)

  type-subtype : Type (l1 ⊔ l2)
  type-subtype = Σ A is-in-subtype

  inclusion-subtype : type-subtype → A
  inclusion-subtype = pr1

  ap-inclusion-subtype :
    (x y : type-subtype) →
    x ＝ y → (inclusion-subtype x ＝ inclusion-subtype y)
  ap-inclusion-subtype x y p = ap inclusion-subtype p
```
<!-- rosetta-item-end: definition-12.2.1 -->

One reason why subtypes are important and useful, is that for any
```text
(x,p),(y,q):Σ(x:A) P(x)
```
in a subtype of `A`, we have `(x,p)=(y,q)` if and only if `x=y`.
In other words, two terms of a subtype of `A` are equal if and only if they are equal as terms of `A`.
This fact is properly expressed using embeddings: we claim that the projection map
```text
pr 1 : (Σ(x:A) P(x))→ A
```
is an embedding, for any subtype `P` of `A`.
This claim can be strengthened slightly.
We will prove the following two closely related facts:

1.  A map `f:A→ B` is an embedding if and only if its fibers are propositions.

2.  A family of types `B` over `A` is a subtype of `A` if and only if the projection map
```text
(Σ(x:A) B(x))→ A
```
    is an embedding.

The first fact is analogous to the fact that a map is an equivalence if and only if its fibers are contractible, which we saw in Theorems 10.4.6 and 10.3.5.
To prove the above claims, we will need that propositions are closed under equivalences.

## Lemma 12.2.2

<!-- rosetta-item: lemma-12.2.2; latex-label: lem:prop_equiv -->

Let `A` and `B` be types, and let `e:A ≃ B`.
Then we have
```text
is-prop(A)↔is-prop(B).
```

### Proof

<!-- rosetta-item: subheading-12.2-proof -->

*Proof.* We will show that `is-prop(B)` implies `is-prop(A)`.
This suffices, because the converse follows from the fact that `e^{-1}:B→ A` is also an equivalence.

Since `e` is assumed to be an equivalence, it follows by Theorem 11.4.2 that
```text
ap{e} : (x=y)→ (e(x)=e(y))
```
is an equivalence for any `x,y:A`.
If `B` is a proposition, then in particular the type `e(x)=e(y)` is contractible for any `x,y:A`, so the claim follows from Theorem 10.4.6. ◻

<!-- rosetta-agda-block: lemma-12.2.2-propositions-under-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H =
      is-prop-is-proof-irrelevant
        ( λ a → is-contr-is-equiv B f E (is-proof-irrelevant-is-prop H (f a)))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (f , is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-section-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (f , is-equiv-f) = is-prop-is-equiv' is-equiv-f
```
<!-- rosetta-item-end: lemma-12.2.2 -->

## Theorem 12.2.3

<!-- rosetta-item: theorem-12.2.3; latex-label: thm:embedding -->

Consider a map `f:A→ B`.
The following are equivalent:

1.  The map `f` is an embedding.

2.  The fiber `fib(f, b)` is a proposition for each `b:B`.

### Proof

<!-- rosetta-item: subheading-12.2-proof-2 -->

*Proof.* By the fundamental theorem of identity types, it follows that `f` is an embedding if and only if
```text
Σ(x:A) f(x)=f(y)
```
is contractible for each `y:A`.
In other words, `f` is an embedding if and only if `fib(f, f(y))` is contractible for each `y:A`.
Note that we obtain equivalences
```text
fib(f, f(y))≃ fib(f, b)
```
for any `b:B` and `p:f(y)=b`, by transporting along `p`.
Therefore it follows by Lemma 12.2.2 that `fib(f, f(y))` is contractible for each `y:A` if and only if `fib(f, b)` is contractible for each `y:A`, and each `b:B` such that `p:f(y)=b`.
The latter condition holds if and only if we have
```text
fib(f, b)→is-contr(fib(f, b))
```
for any `b:B`, which is by Proposition 12.1.3 equivalent to the condition that each `fib(f, b)` is a proposition. ◻

<!-- rosetta-agda-block: theorem-12.2.3-propositional-map-predicate -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-prop-map : (A → B) → Type (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fiber f b)
```

<!-- rosetta-agda-block: theorem-12.2.3-embeddings-propositional-fibers -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id
        ( is-contr-equiv'
          ( fiber f (f x))
          ( equiv-fiber f (f x))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (x , refl)))
        ( λ _ → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fiber f y) → is-contr (fiber f y)
      α (x , refl) =
        is-contr-equiv
          ( fiber' f (f x))
          ( equiv-fiber f (f x))
          ( fundamental-theorem-id' (λ _ → ap f) (is-emb-f x))
```
<!-- rosetta-item-end: theorem-12.2.3 -->

## Corollary 12.2.4

<!-- rosetta-item: corollary-12.2.4; latex-label: cor:pr1-embedding -->

Consider a family `B` of types over `A`.
The following are equivalent:

1.  The map `pr 1 : (Σ(x:A) B(x))→ A` is an embedding.

2.  The type `B(x)` is a proposition for each `x:A`.

### Proof

<!-- rosetta-item: subheading-12.2-proof-3 -->

*Proof.* This corollary follows at once from Exercise 10.7, where we showed that
```text
fib(pr 1, x)≃ B(x).
```
 ◻

<!-- rosetta-agda-block: corollary-12.2.4-propositional-inclusion-fibers -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : subtype l2 A)
  where

  abstract
    is-prop-map-inclusion-subtype : is-prop-map (inclusion-subtype B)
    is-prop-map-inclusion-subtype =
      ( λ x →
        is-prop-equiv
          ( equiv-fiber-pr1 (is-in-subtype B) x)
          ( is-prop-is-in-subtype B x))
```

<!-- rosetta-agda-block: corollary-12.2.4-subtype-embedding -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : subtype l2 A)
  where

  abstract
    is-emb-inclusion-subtype : is-emb (inclusion-subtype B)
    is-emb-inclusion-subtype =
      is-emb-is-prop-map
        ( is-prop-map-inclusion-subtype B)

  emb-subtype : type-subtype B ↪ A
  pr1 emb-subtype = inclusion-subtype B
  pr2 emb-subtype = is-emb-inclusion-subtype

  equiv-ap-inclusion-subtype :
    {s t : type-subtype B} →
    (s ＝ t) ≃ (inclusion-subtype B s ＝ inclusion-subtype B t)
  pr1 (equiv-ap-inclusion-subtype {s} {t}) = ap-inclusion-subtype B s t
  pr2 (equiv-ap-inclusion-subtype {s} {t}) = is-emb-inclusion-subtype s t
```

<!-- rosetta-agda-block: corollary-12.2.4-subtype-from-embedding -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fiber-pr1 B x) (is-prop-map-is-emb H x)
```

<!-- rosetta-agda-block: corollary-12.2.4-embedding-from-subtype -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  is-emb-pr1-is-subtype : is-subtype B → is-emb (pr1 {B = B})
  is-emb-pr1-is-subtype H =
    is-emb-inclusion-subtype (λ x → (B x , H x))
```
<!-- rosetta-item-end: corollary-12.2.4 -->
