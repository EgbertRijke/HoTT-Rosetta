# Section 21.1 The induction principle of the circle

```agda
module section-21-1-the-induction-principle-of-the-circle where
```

<!-- rosetta-item: section-21.1 -->

The *circle* is specified as a higher inductive type `S^1` that comes equipped with
```text
base : S^1
loop : base = base.
```
Just like for ordinary inductive types, the induction principle for higher inductive types provides us with a way of constructing sections of dependent types.
However, we need to take the *path constructor* `loop` into account in the induction principle.

The induction principle of the circle tells us how to define a section
```text
f:Π(x:S^1) P(x)
```
of an arbitrary type family `P` over `S^1`.
To see what the induction principle of the circle should be, we start with an arbitrary section `f:Π(x:S^1) P(x)` and see how it acts on the constructors of `S^1`.
By applying `f` to the base point of the circle, we obtain an element `f(base):P(base)`.
Moreover, using the dependent action on paths of `f` of Definition 5.4.2 we also obtain an identification
```text
apd_{f}(loop) : tr_P(loop,f(base)) = f(base)
```
in the type `P(base)`.
In other words, we obtain a *dependent action on generators* for every section of a family of types.

## Definition 21.1.1

<!-- rosetta-item: definition-21.1.1; latex-label: eq:dgen_circle -->

Let `P` be a type family over the circle.
The **dependent action on generators** is the map
```text
dgen_{S^1}:(Π(x:S^1) P(x))→(Σ(u:P(base)) tr_P(loop,u) = u)
```
given by `dgen_{S^1}(f)≔(f(base),apd_{f}(loop))`.

<!-- rosetta-item-end: definition-21.1.1 -->

The induction principle of the circle states that in order to construct a section `f:Π(x:S^1) P(x)`, it suffices to provide an element `u:P(base)` and an identification
```text
tr_P(loop,u)=u.
```
More precisely, the induction principle of the circle is formulated as follows:

## Definition 21.1.2

<!-- rosetta-item: definition-21.1.2 -->

The **circle** is a type `S^1` that comes equipped with
```text
base : S^1
loop : base = base,
```
and satisfies the **induction principle of the circle**, which provides for each type family `P` over `S^1` a map
```text
ind-S^1:(Σ(u:P(base)) tr_P(loop,u) = u)→ (Π(x:S^1) P(x)),
```
and a homotopy witnessing that `ind-S^1` is a section of `dgen_{S^1}`
```text
comp_S^1:dgen_{S^1}∘ ind-S^1~ id
```
for the computation rules.

<!-- rosetta-item-end: definition-21.1.2 -->

## Remark 21.1.3

<!-- rosetta-item: remark-21.1.3; latex-label: rmk:circle-induction -->

The type of identifications `(u,p)=(u',p')` in the type
```text
Σ(u:P(base)) tr_P(loop,u)=u
```
is equivalent to the type of pairs `(α,β)` consisting of an identification `α:u=u'`, and an identification `β` witnessing that the square
<!-- rosetta-diagram: 500a745466d2; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_P(loop,u)]---->[tr_P(loop,u')]
      |                   |
     [u]      ---->      [u']

Arrows:
- tr_P(loop,u) --p--> u
- tr_P(loop,u) --ap_{tr_P(loop)}(α)--> tr_P(loop,u')
- tr_P(loop,u') --{p'}--> u'
- u --α--> u'
```
commutes.
Therefore it follows from the induction principle of the circle that for any `(u,p):Σ(u:P(base)) tr_P(loop,u)=u`, there is a dependent function `f:Π(x:S^1) P(x)` equipped with an identification
```text
α : f(base)=u,
```
and an identification `β` witnessing that the square
<!-- rosetta-diagram: b9d50548abb6; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[tr_P(loop,f(base))]---->[tr_P(loop,u)]
         |                     |
     [f(base)]      ---->     [u]

Arrows:
- tr_P(loop,f(base)) --{apd_{f}(loop)}--> f(base)
- tr_P(loop,f(base)) --ap_{tr_P(loop)}(α)--> tr_P(loop,u)
- tr_P(loop,u) --{p}--> u
- f(base) --α--> u
```
commutes.

<!-- rosetta-item-end: remark-21.1.3 -->
