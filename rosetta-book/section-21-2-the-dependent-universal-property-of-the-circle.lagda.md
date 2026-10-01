# Section 21.2 The (dependent) universal property of the circle

```agda
module section-21-2-the-dependent-universal-property-of-the-circle where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-21-1-the-induction-principle-of-the-circle
```

We will now use the induction principle of the circle to derive the _dependent universal property_ and the _universal property_ of the circle.
The universal property of the circle states that, for any type `X` the canonical map

```text
(S¹ → X) → (Σ(x:X) x = x)
```

given by `f ↦ (f(base),ap_{f}(loop))` is an equivalence.
The type `Σ(x : X) x = x` is also called the type of **free loops** in `X`.
In other words, the universal property of the circle states that a map `S¹ → X` is the same thing as a free loop in `X`.

The _dependent universal property_ of the circle similarly states that for any type family `P` over the circle, the canonical map

```text
dgen_{S¹}:(Π(x : S¹) P(x)) → (Σ(y : P(base)) tr_P(loop,y) = y)
```

given by `f ↦ (f(base),apd_{f}(loop))` is an equivalence.

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  dependent-universal-property-circle : UUω
  dependent-universal-property-circle =
    {l2 : Level} (P : X → UU l2) → is-equiv (ev-free-loop-Π α P)
```

Note that the induction principle already states that this map has a section.
The dependent universal property therefore improves on this by stating that this map also has a retraction.

## Theorem 21.2.1

For any type family `P` over the circle, the map

```text
dgen_{S¹}: (Π(x:S¹) P(x)) → (Σ(y:P(base)) tr_P(loop,y) = y)
```

given by `f ↦ (f(base),apd_{f}(loop))` is an equivalence.

### Proof

_Proof._ By the induction principle of the circle we know that the map has a section, i.e., we have

```text
ind-S¹ : (Σ(y:P(base)) tr_P(loop,y)=y) → (Π(x:S¹) P(x))
comp_S¹ : dgen_{S¹}∘ind-S¹~id
```

Therefore it remains to construct a homotopy

```text
ind-S¹ ∘ dgen_{S¹} ~ id.
```

Thus, for any `f : Π (x : S¹) P(x)` our task is to construct an identification

```text
ind-S¹(dgen_{S¹}(f)) = f.
```

By function extensionality it suffices to construct a homotopy

```text
Π(x:S¹) ind-S¹(dgen_{S¹}(f))(x) = f(x).
```

We proceed by the induction principle of the circle using the family of types `E_{g,f}(x) ≔ g(x) = f(x)` indexed by `x : S¹`, where `g` is the function

```text
g ≔ ind-S¹(dgen_{S¹}(f)).
```

Thus, it suffices to construct

```text
α : g(base) = f(base)
β : tr_{E_{g,f}}(loop,α) = α.
```

An argument by path induction on `p` yields that

```text
(apd_{g}(p) ∙ r = ap_{tr_P(p)}(q) ∙ apd_{f}(p)) → (tr_{E_{g,f}}(p,q) = r),
```

for any `f,g : Π(x : X) P(x)` and any `p : x = x'`, `q : g(x) = f(x)` and `r : g(x') = f(x')`.
Therefore it suffices to construct an identification `α : g(base) = f(base)` equipped with an identification `β` witnessing that the square

```text
     [tr_P(loop,g(base))]--ap_{tr_P(loop)}(α)-->[tr_P(loop,f(base))]
              |                                     |
apd_{g}(loop) |                                     | apd_{f}(loop)
              v                                     v
         [g(base)]     --------α------------->  [f(base)]
```

commutes.
Notice that we get exactly such a pair `(α,β)` from the computation rule of the circle, by Remark 21.1.3. ◻

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  free-dependent-loop-htpy :
    {l2 : Level} {P : X → UU l2} {f g : (x : X) → P x} →
    ( Eq-free-dependent-loop α P
      ( ev-free-loop-Π α P f)
      ( ev-free-loop-Π α P g)) →
    ( free-dependent-loop α (λ x → f x ＝ g x))
  pr1 (free-dependent-loop-htpy {l2} {P} {f} {g} (p , q)) = p
  pr2 (free-dependent-loop-htpy {l2} {P} {f} {g} (p , q)) =
    map-compute-dependent-identification-eq-value f g (loop-free-loop α) p p q

  is-retraction-ind-circle :
    ( ind-circle : induction-principle-circle α)
    { l2 : Level} (P : X → UU l2) →
    ( ( function-induction-principle-circle α ind-circle P) ∘
      ( ev-free-loop-Π α P)) ~
    ( id)
  is-retraction-ind-circle ind-circle P f =
    eq-htpy
      ( function-induction-principle-circle α ind-circle
        ( eq-value
          ( function-induction-principle-circle α ind-circle P
            ( ev-free-loop-Π α P f))
          ( f))
        ( free-dependent-loop-htpy
          ( Eq-free-dependent-loop-eq α P _ _
            ( compute-induction-principle-circle α ind-circle P
              ( ev-free-loop-Π α P f)))))

  abstract
    dependent-universal-property-induction-principle-circle :
      induction-principle-circle α →
      dependent-universal-property-circle α
    dependent-universal-property-induction-principle-circle ind-circle P =
      is-equiv-is-invertible
        ( function-induction-principle-circle α ind-circle P)
        ( compute-induction-principle-circle α ind-circle P)
        ( is-retraction-ind-circle ind-circle P)

```

As a corollary we obtain the following uniqueness principle for dependent functions defined by the induction principle of the circle.

## Corollary 21.2.2

Consider a type family `P` over the circle, and let

```text
y : P(base)
p : tr_{P}(loop,y) = y.
```

Then the type of functions `f : Π(x : S¹) P(x)` equipped with an identification

```text
α: f(base) = y
```

and an identification `β` witnessing that the square

```text
   [tr_P(loop,f(base))]--ap_{tr_P(loop)}(α)-->[tr_P(loop,y)]
              |                                       |
apd_{f}(loop) |                                       | p
              v                                       v
          [f(base)]      ------α--------------->     [y]
```

commutes, is contractible.

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  uniqueness-dependent-universal-property-circle :
    dependent-universal-property-circle α →
    {l2 : Level} {P : X → UU l2} (k : free-dependent-loop α P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ h → Eq-free-dependent-loop α P (ev-free-loop-Π α P h) k))
  uniqueness-dependent-universal-property-circle dup-circle {l2} {P} k =
    is-contr-is-equiv'
      ( fiber (ev-free-loop-Π α P) k)
      ( tot (λ h → Eq-free-dependent-loop-eq α P (ev-free-loop-Π α P h) k))
      ( is-equiv-tot-is-fiberwise-equiv
        (λ h → is-equiv-Eq-free-dependent-loop-eq α P (ev-free-loop-Π α P h) k))
      ( is-contr-map-is-equiv (dup-circle P) k)
```

Now we use the dependent universal property to derive the ordinary universal property of the circle.
It would be tempting to say that it is a direct corollary, but we need to address the transport that occurs in the dependent universal property.

## Theorem 21.2.3

For each type `X`, the **action on generators**

```text
gen_{S¹} : (S¹ → X) → Σ(x:X) x = x
```

given by `f ↦ (f(base),ap_{f}(loop))` is an equivalence.

### Proof

_Proof._ We prove the claim by constructing a commuting triangle

```text
                   [(S¹→ X)]
                  /          \
   gen_{S¹}      /             \  dgen_{S¹}
                V               V
     [(Σ(x:X) x=x)]  ---≃--->  [(Σ(x:X) tr_{const_X}(loop,x)=x)]
```

in which the bottom map is an equivalence.
Indeed, once we have such a triangle, we use the fact from Theorem 21.2.1 that `dgen_{S¹}` is an equivalence to conclude that `gen_{S¹}` is an equivalence.

To construct the bottom map, we first observe that for any constant type family `const_B` over a type `A`, any `p:a=a'` in `A`, and any `b:B`, there is an identification

```text
tr-const_B(p,b) : tr_{const_B}(p,b)=b.
```

This identification is easily constructed by path induction on `p`.
Now we construct the bottom map as the induced map on total spaces of the family of maps

```text
l ↦ tr-const_X(loop,x) ∙ l,
```

indexed by `x : X`.
Since concatenating by a path is an equivalence, it follows by Theorem 11.1.3 that the induced map on total spaces is indeed an equivalence.

To show that the triangle commutes, it suffices to construct for any `f:S¹→ X` an identification witnessing that the triangle

_Triangle-shaped diagram (automatic draft)._

```text
[tr_{const_X}(loop,f(base))] --{tr-const_X(loop,f(base))}--> [f(base)]
              \                                         /
 apd_{f}(loop) \                                      /  ap_{f}(loop
                V                                   V
                              [f(base)]
```

commutes.
This again follows from general considerations: for any `f:A→ B` and any `p:a=a'` in `A`, the triangle

```text
[tr_{const_B}(p,f(a))] --tr-const_B(p,f(a))--> [f(a)]
                  \                              /
        apd_{f}(p) \                           /  ap_{f}(p)
                    V                         V
                              [f(a')]
```

commutes by path induction on `p`. ◻

## Corollary 21.2.4

For any loop `l : x = x` in a type `X`, the type of maps `f : S¹ → X` equipped with an identification

```text
α : f(base) = x
```

and an identification `β` witnessing that the square

```text
          [f(base)]--α--> [x]
              |            |
 ap_{f}(loop) |            | l
              v            v
          [f(base)]--α--> [x]
```

commutes, is contractible.
