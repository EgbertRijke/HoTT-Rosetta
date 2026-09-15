# Exercise 13.15

```agda
module exercise-13-15-morphisms-over-a-type where

```

## Problem statement

For any two maps `f:A→ X` and `g:B→ X`, define the type of **morphisms from `f` to `g` over `X`** by
```text
hom-slice_X(f,g)≔ Σ(h:A→ B) f~ g∘ h.
```
In other words, the type `hom-slice_X(f,g)` is the type of maps `h:A→ B` equipped with a homotopy witnessing that the triangle

```text
 [A]                 [B]

           [X]

Arrows:
- A --f--> X
- A --h--> B
- B --g--> X
```
commutes.

<div class="subexenum">

Consider a family `P` of types over `X`.
Show that the map
```text
(Π(x:X) fib(f, x)→ P(x))→(Π(a:A) P(f(a)))
```
given by `h↦ h_{f(a)}(a,refl)` is an equivalence.

Construct three equivalences `α`, `β`, and `γ` as shown in the following diagram, and show that this triangle commutes:

```text
                                   [hom-slice_X(f,g)]

[(Π(x:X) fib(f, x)→fib(g, x))]                            [Π(a:A) fib(g, f(a))]

Arrows:
- hom-slice_X(f,g) --α--> (Π(x:X) fib(f, x)→fib(g, x))
- hom-slice_X(f,g) --β--> Π(a:A) fib(g, f(a))
- (Π(x:X) fib(f, x)→fib(g, x)) --γ--> Π(a:A) fib(g, f(a))
```
Given a morphism `(h,H):hom-slice_X(f,g)` over `X`, we also say that `α(h,H)` is its **action on fibers**.

Given `(h,H):hom-slice_X(f,g)`, show that the following are equivalent:

1.  The map `h:A→ B` is an equivalence.

2.  The action on fibers
```text
α(h,H):Π(x:X) fib(f, x)→fib(g, x)
```
    is a family of equivalences.

3.  The precomposition function
```text
_∘ (h,H) : hom-slice_X(g,i)→hom-slice_X(f,i)
```
    given by `(k,K)∘ (h,H) ≔ (k∘ h,H ∙ (K· h))` is an equivalence for each map `i:C→ X`.

Conclude that the type `Σ(h:A ≃ B) f~ g∘ h` is equivalent to the type of families of equivalences
```text
Π(x:X) fib(f, x)≃fib(g, x).
```

</div>

## Solution

<!-- rosetta-item: exercise-13-15 -->

No formalization has been curated yet.
