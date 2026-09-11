# Section 11.4 Embeddings

```agda
module section-11-4-embeddings where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-2-the-fundamental-theorem
```

<!-- rosetta-item: section-11.4 -->

In our second application of the fundamental theorem we show that equivalences are embeddings.
The notion of embedding is the homotopical analogue of the set theoretic notion of injective map.

## Definition 11.4.1

<!-- rosetta-item: definition-11.4.1 -->

An **embedding** is a map `f:A→ B` that satisfies the property that
```text
ap{f}:(x = y)→(f(x) = f(y))
```
is an equivalence, for every `x,y:A`.
We write `is-emb(f)` for the type of witnesses that `f` is an embedding, and we define
```text
A↪ B≔ Σ(f:A→ B) is-emb(f).
```

<!-- rosetta-agda-block: definition-11.4.1-embedding-predicate -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-emb : (A → B) → Type (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

  equiv-ap-is-emb :
    {f : A → B} (e : is-emb f) {x y : A} → (x ＝ y) ≃ (f x ＝ f y)
  pr1 (equiv-ap-is-emb {f} e) = ap f
  pr2 (equiv-ap-is-emb {f} e {x} {y}) = e x y
```

<!-- rosetta-agda-block: definition-11.4.1-embeddings -->

```agda
infix 5 _↪_
_↪_ :
  {l1 l2 : Level} → Type l1 → Type l2 → Type (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  map-emb : A ↪ B → A → B
  map-emb = pr1

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb = pr2

  equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (x ＝ y) ≃ (map-emb e x ＝ map-emb e y)
  equiv-ap-emb e = equiv-ap-is-emb (is-emb-map-emb e)
```
<!-- rosetta-item-end: definition-11.4.1 -->

Another way of phrasing the following statement is that equivalent types have equivalent identity types.

## Theorem 11.4.2

<!-- rosetta-item: theorem-11.4.2; latex-label: cor:emb_equiv -->

Any equivalence is an embedding.

### Proof

<!-- rosetta-item: subheading-11.4-proof -->

*Proof.* Let `e:A ≃ B` be an equivalence, and let `x:A`.
Our goal is to show that
```text
ap{e} : (x = y)→ (e(x) = e(y))
```
is an equivalence for every `y:A`.
By Theorem 11.2.2 it suffices to show that
```text
Σ(y:A) e(x)=e(y)
```
is contractible.
Now observe that there is an equivalence

```text
Σ(y:A) e(x)=e(y) ≃ Σ(y:A) e(y)=e(x)
≐ fib(e, e(x))
```

by Theorem 11.1.3, since for each `y:A` the map
```text
inv : (e(x)=e(y))→ (e(y)= e(x))
```
is an equivalence by Exercise 9.1.
The fiber `fib(e, e(x))` is contractible by Theorem 10.4.6, so it follows by Exercise 10.3 that the type `Σ(y:A) e(x)=e(y)` is indeed contractible. ◻

<!-- rosetta-agda-block: theorem-11.4.2-equivalences-are-embeddings -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B}
  where

  is-emb-is-contr-fibers-values' :
    ((a : A) → is-contr (fiber' f (f a))) → is-emb f
  is-emb-is-contr-fibers-values' c a =
    fundamental-theorem-id (c a) (λ x → ap f {a} {x})

  is-emb-is-equiv : is-equiv f → is-emb f
  is-emb-is-equiv H =
    is-emb-is-contr-fibers-values'
      ( λ a →
        is-contr-equiv'
          ( fiber f (f a))
          ( equiv-fiber f (f a))
          ( is-contr-map-is-equiv H (f a)))
```

<!-- rosetta-agda-block: theorem-11.4.2-embedding-of-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-emb-equiv : (e : A ≃ B) → is-emb (map-equiv e)
  is-emb-equiv e = is-emb-is-equiv (is-equiv-map-equiv e)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-equiv e
```
<!-- rosetta-item-end: theorem-11.4.2 -->
