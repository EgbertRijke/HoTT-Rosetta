# Section 21.1 The induction principle of the circle

```agda
module section-21-1-the-induction-principle-of-the-circle where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
```

The _circle_ is specified as a higher inductive type `S¹` that comes equipped with

```text
base : S¹
loop : base = base.
```

Just like for ordinary inductive types, the induction principle for higher inductive types provides us with a way of constructing sections of dependent types.
However, we need to take the _path constructor_ `loop` into account in the induction principle.

The induction principle of the circle tells us how to define a section

```text
f : Π(x : S¹) P(x)
```

of an arbitrary type family `P` over `S¹`.
To see what the induction principle of the circle should be, we start with an arbitrary section `f : Π(x : S¹) P(x)` and see how it acts on the constructors of `S¹`.
By applying `f` to the base point of the circle, we obtain an element `f(base) : P(base)`.
Moreover, using the dependent action on paths of `f` of Definition 5.4.2 we also obtain an identification

```text
apd_{f}(loop) : tr_P(loop,f(base)) = f(base)
```

in the type `P(base)`.
In other words, we obtain a _dependent action on generators_ for every section of a family of types.

## Definition 21.1.1

Let `P` be a type family over the circle.
The **dependent action on generators** is the map

```text
dgen_{S¹} : (Π(x : S¹) P(x))→(Σ(u:P(base)) tr_P(loop,u) = u)
```

given by `dgen_{S¹}(f)≔(f(base),apd_{f}(loop))`.

The induction principle of the circle states that in order to construct a section `f : Π (x : S¹) P(x)`, it suffices to provide an element `u : P(base)` and an identification

```text
tr_P(loop,u)=u.
```

More precisely, the induction principle of the circle is formulated as follows:

```agda
free-loop : {l1 : Level} (X : UU l1) → UU l1
free-loop X = Σ X (λ x → x ＝ x)

module _
  {l1 : Level} {X : UU l1}
  where

  base-free-loop : free-loop X → X
  base-free-loop = pr1

  loop-free-loop : (α : free-loop X) → base-free-loop α ＝ base-free-loop α
  loop-free-loop = pr2
```

## Definition 21.1.2

The **circle** is a type `S¹` that comes equipped with

```text
base : S¹
loop : base = base,
```

```agda
postulate
  𝕊¹ : UU lzero

postulate
  base-𝕊¹ : 𝕊¹

postulate
  loop-𝕊¹ : base-𝕊¹ ＝ base-𝕊¹

free-loop-𝕊¹ : free-loop 𝕊¹
free-loop-𝕊¹ = base-𝕊¹ , loop-𝕊¹

𝕊¹-Pointed-Type : Pointed-Type lzero
𝕊¹-Pointed-Type = 𝕊¹ , base-𝕊¹
```

and satisfies the **induction principle of the circle**, which provides for each type family `P` over `S¹` a map

```text
ind-S¹ : (Σ (u:P(base)) tr_P(loop,u) = u) → (Π (x : S¹) P(x)),
```

```agda
postulate
  ind-𝕊¹ : induction-principle-circle free-loop-𝕊¹
```

and a homotopy witnessing that `ind-S¹` is a section of `dgen_{S¹}`

```text
comp_S¹ : dgen_{S¹} ∘ ind-S¹ ~ id
```

for the computation rules.

## Remark 21.1.3

The type of identifications `(u,p)=(u',p')` in the type

```text
Σ(u : P(base)) tr_P(loop,u) = u
```

is equivalent to the type of pairs `(α,β)` consisting of an identification `α : u = u'`, and an identification `β` witnessing that the square

```text
[tr_P(loop,u)]--ap_{tr_P(loop)}(α)-->[tr_P(loop,u')]
      |                                  |
     p|                                  | p'
      v                                  v
     [u]      --------α------------->  [u']
```

commutes.
Therefore it follows from the induction principle of the circle that for any `(u,p) : Σ (u:P(base)) tr_P(loop,u)=u`, there is a dependent function `f:Π (x : S¹) P(x)` equipped with an identification

```text
α : f(base)=u,
```

and an identification `β` witnessing that the square

```text
  [tr_P(loop,f(base))]--ap_{tr_P(loop)}(α)-->[tr_P(loop,u)]
          |                                     |
apd_f loop|                                     | p'
          v                                     v
       [f(base)]      --------α------------>  [u']
```

commutes.
