# Chapter 10 Contractible types and contractible maps

```agda
module chapter-10-contractible-types-and-contractible-maps where
```

A contractible type is a type which has, up to identification, only one element.
In other words, a contractible type is a type that comes equipped with a point,
and an identification of this point with any point.

We may think of contractible types as singletons up to homotopy, and indeed we
show that the unit type is an example of a contractible type.
Moreover, we show that contractible types satisfy an induction principle that is
very similar to the induction principle of the unit type.

Another case of an inductive type with a single constructor is the type of
identifications `p : a = x` with a fixed starting point `a : A`.
To specify such an identification, we have to give its end point `x : A` as well
as the identification `p : a = x`, and the path induction principle asserts that
in order to show something about all such identifications, it suffices to show
that thing in the case where the end point is `a`, and the path is `refl(a)`.
This suggests that the total space

```text
  Σ(x : A) a = x
```

of all paths with starting point `a : A` is contractible.
This important fact will be shown in Theorem 10.1.4, and it is the basis for
the fundamental theorem of identity types.

Next, we introduce the *fiber* of a map `f : A → B`.
The fiber of `f` at `b : B` consists of the type of elements `a : A` equipped
with an identification `p : f(a) = b`.
In other words, the fiber of `f` at `b` is the preimage of `f` at `b`.
In Theorem 10.3.4 and Theorem 10.4.6 we show that a map is an equivalence if
and only if its fibers are contractible.
The condition that the fibers of a map are contractible is analogous to the set
theoretic notion of bijective map, or one-to-one correspondence.


```agda
open import section-10-1-contractible-types
open import section-10-2-singleton-induction
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-1-identity-types-contractible
open import exercise-10-2-contractible-retracts
open import exercise-10-3-contractible-equivalences
open import exercise-10-4-finite-types-not-contractible
open import exercise-10-5-contractible-products
open import exercise-10-6-dependent-pair-contractible-base
open import exercise-10-7-fibers-of-projections
open import exercise-10-8-fiber-replacement
```
