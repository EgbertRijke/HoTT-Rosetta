# Section 20.4 The elementhood relation on W-types

```agda
module section-20-4-the-elementhood-relation-on-w-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-10-3-contractible-maps
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-20-1-the-type-of-well-founded-trees
```

The elements of a W-type `W(A, B)` are constructed out of families of elements of `W(A, B)` indexed by a type `B(x)` for some `x : A`.
More precisely, for each `tree(x, α) : W(A, B)` we have a family of elements

```text
α(y) : W(A, B)
```
indexed by `y : B(x)`.
Thus, we could say that `α(y)` is in `tree(x, α)`, for each `y : B(x)`.
More abstractly, we can define an elementhood relation on `W(A, B)`.

## Definition 20.4.1

Given a W-type `W(A, B)` and a universe `𝒰` containing both `A` and each type in the family `B`, we define a type-valued relation

```text
 ∈ : W(A, B) → W(A, B) → 𝒰
```

by `(x ∈ tree(a, α)) ≔ Σ(y : B(a)) α(y) = x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _∈-𝕎_ _∉-𝕎_

  _∈-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∈-𝕎 y = fiber (component-𝕎 y) x

  _∉-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∉-𝕎 y = is-empty (x ∈-𝕎 y)
```

Using the elementhood relation on `W(A, B)`, we can reformulate the induction principle to, perhaps, a more recognizable form:

## Theorem 20.4.2

For any family `P` of types over `W(A, B)`, there is a function

```text
i : (Π(x : W(A, B)) (Π(y : W(A, B)) (y ∈ x) → P(y)) → P(x)) → (Π(x : X) P(x))
```

that comes equipped with an identification

```text
i(h, x) = h(x, λ y. λ e. i(h, y))
```

for every `h : Π(x : W(A, B)) (Π(y : W(A, B)) (y ∈ x) → P(y)) → P(x)`, and every `x : W(A, B)`.

### Proof
For any type family `P` over `W(A, B)`, we first define a new type family `□ P` over `W(A, B)` given by
```text
□ P(x) ≔ Π(y : W(A, B)) (y ∈ x) → P(y).
```
The family `□ P(x)` comes equipped with a map

```text
η : (Π(x : W(A, B)) P(x)) → (Π(x : W(A,B)) □ P(x))
```

given by `η(f, x, y, e) ≔ f(y)`.
Conversely, there is a map

```text
ε(h) : (Π(y : W(A, B)) □ P(y)) → (Π(x : W(A, B)) P(x))
```

for every `h : Π(y : W(A, B)) □ P(y) → P(y)`, given by `ε(h, g, x) ≔ h(x, g(x))`.
Note that the induction principle can now be stated as

```text
i : (Π(y : W(A, B)) □ P(y) → P(y)) → (Π(x : W(A, B)) P(x)),
```

and the computation rule states that

```text
i(h, x) = h(x, η(i(h), x)).
```

Before we prove the induction principle, we prove the intermediate claim that there is a function

```text
i' : (Π(y : W(A, B)) □ P(y) → P(y)) → (Π(x : W(A, B)) □ P(x))
```

equipped with an identification

```text
j'(h, x, y, e) : i'(h, x, y, e) = h(y, i'(h, y))
```

for every `h : Π(y : W(A, B)) □ P(y) → P(y)` and every `x, y : W(A, B)` equipped with `e : y ∈ x`.
Both `i'` and `j'` are defined by pattern matching:

```text
i'(h, tree(a, f), f(b), (b, refl)) := h(f(b), i'(h, f(b)))
j'(h, tree(a, f), f(b), (b, refl)) := refl.
```

Now we define `i(h):=ε(h,i'(h))`.
Note that we have the judgmental equalities

```text
i(h,x) ≐ ε(h, i'(h), x)
       ≐ h(x, i'(h, x)),
```

and

```text
h(x, λ y. λ e. i(h,y)) ≐ h(x, λ y. λ e. ε(h, i'(h), y))
                       ≐ h(x, λ y. λ e. h(y, i'(h, y))).
```
The computation rule is therefore satisfied by the identification

```text
                ap_{h(x)}(eq-htpy(λ y. eq-htpy(j'(h, x, y))))
h(x, i'(h, x)) =============================================== h(x, λ y. λ e. h(y, i'(h, y))) 
```

◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  □-∈-𝕎 : (𝕎 A B → UU l3) → (𝕎 A B → UU (l1 ⊔ l2 ⊔ l3))
  □-∈-𝕎 P x = (y : 𝕎 A B) → (y ∈-𝕎 x) → P y
  
  η-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) → ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-∈-𝕎 P x)
  η-□-∈-𝕎 P f x y e = f y

  ε-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    ((x : 𝕎 A B) → □-∈-𝕎 P x) → (x : 𝕎 A B) → P x
  ε-□-∈-𝕎 P h f x = h x (f x)

  ind-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → □-∈-𝕎 P x
  ind-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) =
    h (α b) (ind-□-∈-𝕎 P h (α b))

  compute-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x y : 𝕎 A B) (e : y ∈-𝕎 x) →
    ind-□-∈-𝕎 P h x y e ＝ h y (ind-□-∈-𝕎 P h y)
  compute-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) = refl

  ind-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → P x
  ind-∈-𝕎 P h = ε-□-∈-𝕎 P h (ind-□-∈-𝕎 P h)

  compute-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → ind-∈-𝕎 P h x ＝ h x (λ y e → ind-∈-𝕎 P h y)
  compute-∈-𝕎 P h x =
    ap (h x) (eq-htpy (eq-htpy ∘ compute-□-∈-𝕎 P h x))
```