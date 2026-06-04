# Coproducts

```agda
module section-4-4-coproducts where

open import universe-levels

open import section-4-3-the-empty-type
```

## Definition 4.4.1

Let `A` and `B` be types. We define the \define{coproduct} to be a type that comes equipped with

```text
  inl : A → A + B
  inr : B → A + B,
```

satisfying the induction principle that for any family of types `P(x)` indexed by `x : A + B`, there is a term

```text
  ind-coprod : (Π{x : A} P(inl(x))) → ((Π{y : B} P(inr(y))) → Π{z : A + B} P(z))
```

for which the computation rules

```text
  ind-coprod(f,g,inl(x)) ≐ f(x)
  ind-coprod(f,g,inr(y)) ≐ g(y)
```

hold. Alternatively, a definition of a dependent function `h : Π{x : A + B} P(x)` by induction using `f : Π{x : A} P(inl(x))` and `g : Π{y : B} P(inr(y))` can be presented by pattern matching as

```text
  h(inl(x)) ≔ f(x)
  h(inr(y)) ≔ g(y).
```

Sometimes we write `[f,g]` for the function `ind-coprod(f,g)`. The coproduct of two types is sometimes also called the \define{disjoint sum}.

```agda
infixr 10 _+_

data _+_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2)
  where
  inl : A → A + B
  inr : B → A + B

ind-coproduct :
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : A + B → Type l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : A + B) → C t
ind-coproduct C f g (inl x) = f x
ind-coproduct C f g (inr x) = g x

rec-coproduct :
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} →
  (A → C) → (B → C) → (A + B) → C
rec-coproduct {C = C} = ind-coproduct (λ _ → C)
```

By the induction principle of coproducts we obtain a function

```text
  ind-coprod : (A → X) → ((B → X) → (A + B → X))
```

for any type `X`. Note that this special case of the induction principle of coproducts is very similar to the elimination rule of disjunction in first order logic: if `P`, `P'`, and `Q` are propositions, then we have

```text
  (P → Q) → ((P' → Q)→ (P ∨ P' → Q)).
```

Indeed, we can think of \emph{propositions as types} and of terms as their constructive proofs. Under this interpretation of type theory the coproduct is indeed the disjunction.

### Remark 4.4.2

A simple application of the induction principle for coproducts gives us a map

```text
  f + g : A + B → A' + B'
```

for every `f : A → A'` and `g : B → B'`. Indeed, the map `f + g` is defined by

```text
    (f + g)(inl(x)) ≔ inl(f(x))
    (f + g)(inr(y)) ≔ inr(g(y)).
```

```agda
map-coproduct :
  {l1 l2 l3 l4 : Level}
  {A : Type l1} {B : Type l2} {A' : Type l3} {B' : Type l4}
  (f : A → A') (g : B → B') → A + B → A' + B'
map-coproduct f g (inl x) = inl (f x)
map-coproduct f g (inr y) = inr (g y)
```

### Proposition 4.4.3

  Consider two types `A` and `B`, and suppose that `B` is empty. Then there is a function

```text
    (A + B) → A.
```

### Remark 4.4.4

  In other words, there is a function

```text
    is-empty(B) → ((A + B) → A),
```

for any two types `A` and `B`. Similarly, there is a function

```text
    is-empty(A) → ((A + B) → B),
```

for any two types `A` and `B`.

### Proof of Proposition 4.4.3

  We will construct the function `(A + B) → A` with the induction principle of the coproduct `A + B`. Therefore, we must construct two functions:

```text
    f : A → A
    g : B → A.
```

The function `f` is simply defined to be the identity function `\idfunc : A → A`. Recall that we have assumed that `B` is empty, so we have a function `b̃ : B → ∅`. Furthermore, we always have the function `\exfalso : ∅ → A`. Therefore, we can define `g≔ \exfalso\circ b̃` to complete the proof.

```agda
map-left-unit-law-coproduct :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} →
  is-empty A → A + B → B
map-left-unit-law-coproduct H (inl x) = ex-falso (H x)
map-left-unit-law-coproduct H (inr y) = y

map-right-unit-law-coproduct :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} →
  is-empty B → A + B → A
map-right-unit-law-coproduct H (inl x) = x
map-right-unit-law-coproduct H (inr x) = ex-falso (H x)
```
