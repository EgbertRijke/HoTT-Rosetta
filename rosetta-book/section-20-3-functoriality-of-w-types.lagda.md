# Section 20.3 Functoriality of W-types

```agda
module section-20-3-functoriality-of-w-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-2-bi-invertible-maps
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-20-1-the-type-of-well-founded-trees
open import section-20-2-observational-equality-of-w-types

open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import exercise-12-6-truncated-sigma-types
open import exercise-13-12-dependent-products-of-truncated-maps
```

## Definition 20.3.1

Consider a type family `B` over `A`, and a type family `B'` over `A'`.
Furthermore, consider a map `f : A' → A` and a family of equivalences

```text
e_x : B'(x) ≃ B(f(x))
```

indexed by `x : A'`.
Then we define the map `W(f, e) : W(A', B') → W(A, B)` of W-types inductively by

```text
W(f, e)(tree(x, α)) ≔ tree(f(x), W(f, g) ∘ α ∘ e_x⁻¹).
```

```agda
map-𝕎' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (g : (x : A) → D (f x) → B x) →
  𝕎 A B → 𝕎 C D
map-𝕎' D f g (tree-𝕎 a α) = tree-𝕎 (f a) (λ d → map-𝕎' D f g (α (g a d)))

map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 A B → 𝕎 C D
map-𝕎 D f e = map-𝕎' D f (λ x → map-inv-equiv (e x))
```

## Lemma 20.3.2

For any morphism `W(f,e) : W(A', B') → W(A, B)` of W-types and any `tree(x, α) : W(A, B)`, there is an equivalence

```text
fib(W(f, e), tree(x, α)) ≃ fib(f, x) × Π(b : B(x)) fib(W(f, e), α(b)).
```

### Proof
First, note that by the characterization in Theorem 20.2.3 of the identity type of `W(A, B)`, there is an equivalence between the fiber `fib(W(f, e), tree(x, α))` and the type

```text
Σ(x' : A') Σ(α' : B'(x') → W(A', B')) Σ(p : f(x') = x)
Σ(x' : A') Π(b : B(f(x'))) W(f, e)(α'(e_{x'}⁻¹(b))) = α(tr_{B}(p, b)).
```

By rearranging the `Σ`-type, we see that this type is equivalent to the type

```text
Σ((x', p) : fib(f, x)) Σ(α' : B'(x') → W(A', B'))
Σ(x' : A') Π(b : B(f(x'))) W(f, e)(α'(e_{x'}⁻¹(b))) = α(tr_{B}(p, b)).
```

Therefore, it suffices to show for each `(x', p) : fib(f, x)`, that the type

```text
Σ(α' : B'(x') → W(A', B')) Π(b : B(f(x'))) W(f, e)(α'(e_{x'}⁻¹(b))) = α(tr_{B}(p,b ))
```

is equivalent to the type `Π(b : B(x)) fib(W(f, e), α(b))`.
Since we have an identification `p : f(x') = x` and an equivalence `e_{x'} : B'(x') ≃ B(f(x'))`, it follows that the type above is equivalent to the type

```text
Σ(α' : B(x) → W(A', B')) Π(b : B(x)) W(f, e)(α'(b)) = α(b).
```

By distributivity of `Π` over `Σ`, i.e., by Theorem 13.2.1, this type is equivalent to the type

```text
Π(b : B(x)) Σ(w : W(A', B')) W(f, e)(w) = α(b),
```

completing the proof. ◻

```agda
fiber-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
fiber-map-𝕎 D f e (tree-𝕎 c γ) =
  (fiber f c) × ((d : D c) → fiber (map-𝕎 D f e) (γ d))

abstract
  equiv-fiber-map-𝕎 :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
    (D : C → UU l4) (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
    (y : 𝕎 C D) → fiber (map-𝕎 D f e) y ≃ fiber-map-𝕎 D f e y
  equiv-fiber-map-𝕎 {A = A} {B} {C} D f e (tree-𝕎 c γ) =
    ( ( ( inv-associative-Σ) ∘e
        ( equiv-tot
          ( λ a →
            ( ( equiv-tot
                ( λ p →
                  ( ( equiv-Π
                      ( λ (d : D c) → fiber (map-𝕎 D f e) (γ d))
                      ( (equiv-tr D p) ∘e (e a))
                      ( λ b → id-equiv)) ∘e
                    ( inv-distributive-Π-Σ)) ∘e
                  ( equiv-tot
                    ( λ α →
                      equiv-Π
                        ( λ (b : B a) →
                          map-𝕎 D f e (α b) ＝ γ (tr D p (map-equiv (e a) b)))
                        ( inv-equiv (e a))
                        ( λ d →
                          ( equiv-concat'
                            ( map-𝕎 D f e
                              ( α (map-inv-equiv (e a) d)))
                            ( ap
                              ( γ ∘ (tr D p))
                              ( inv (is-section-map-inv-equiv (e a) d)))) ∘e
                          ( inv-equiv
                            ( equiv-Eq-𝕎-eq
                              ( map-𝕎 D f e
                                ( α (map-inv-equiv (e a) d)))
                              ( γ (tr D p d))))))))) ∘e
              ( equiv-left-swap-Σ)) ∘e
            ( equiv-tot
              ( λ α →
                equiv-Eq-𝕎-eq
                  ( tree-𝕎
                    ( f a)
                    ( ( map-𝕎 D f e) ∘
                      ( α ∘ map-inv-equiv (e a)))) (tree-𝕎 c γ)))))) ∘e
      ( associative-Σ)) ∘e
    ( equiv-Σ
      ( λ t → map-𝕎 D f e (structure-𝕎-Alg t) ＝ tree-𝕎 c γ)
      ( inv-equiv-structure-𝕎-Alg)
      ( λ x →
        equiv-concat
          ( ap (map-𝕎 D f e) (is-section-map-inv-structure-𝕎-Alg x))
          ( tree-𝕎 c γ)))
```

## Theorem 20.3.3

Consider a morphism `W(f, e) : W(A, B) → W(A', B')` of W-types.
If the map `f : A → A'` is `k`-truncated, then so is the map `W(f, e)`.
In particular, if `f` is an equivalence or an embedding, then so is `W(f, e)`.

### Proof
Suppose that the map `f` is `k`-truncated.
We will prove recursively that the fibers of the morphism `W(f, e)` on W-types is `k`-truncated.
We saw in Lemma 20.3.2 that there is an equivalence

```text
fib(W(f, e), tree(x, α)) ≃ fib(f, x) × Π(b : B(x)) fib(W(f, e), α(b)).
```

The type `fib(f, x)` is `k`-truncated by assumption, and each of the types

```text
fib(W(f, e), α(b))
```

is `k`-truncated by the inductive hypothesis, so the claim follows. ◻

```agda
is-trunc-map-map-𝕎 :
  {l1 l2 l3 l4 : Level} (k : 𝕋)
  {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-trunc-map k f → is-trunc-map k (map-𝕎 D f e)
is-trunc-map-map-𝕎 k D f e H (tree-𝕎 c γ) =
  is-trunc-equiv k
    ( fiber-map-𝕎 D f e (tree-𝕎 c γ))
    ( equiv-fiber-map-𝕎 D f e (tree-𝕎 c γ))
    ( is-trunc-Σ
      ( H c)
      ( λ t → is-trunc-Π k (λ d → is-trunc-map-map-𝕎 k D f e H (γ d))))
```

```agda
is-equiv-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-equiv f → is-equiv (map-𝕎 D f e)
is-equiv-map-𝕎 D f e H =
  is-equiv-is-contr-map
    ( is-trunc-map-map-𝕎 neg-two-𝕋 D f e (is-contr-map-is-equiv H))

equiv-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ≃ C) (e : (x : A) → B x ≃ D (map-equiv f x)) →
  𝕎 A B ≃ 𝕎 C D
equiv-𝕎 D f e =
  pair
    ( map-𝕎 D (map-equiv f) e)
    ( is-equiv-map-𝕎 D (map-equiv f) e (is-equiv-map-equiv f))
```

```agda
is-emb-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-emb f → is-emb (map-𝕎 D f e)
is-emb-map-𝕎 D f e H =
  is-emb-is-prop-map
    (is-trunc-map-map-𝕎 neg-one-𝕋 D f e (is-prop-map-is-emb H))

emb-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ↪ C) (e : (x : A) → B x ≃ D (map-emb f x)) → 𝕎 A B ↪ 𝕎 C D
emb-𝕎 D f e =
  pair
    ( map-𝕎 D (map-emb f) e)
    ( is-emb-map-𝕎 D (map-emb f) e (is-emb-map-emb f))
```