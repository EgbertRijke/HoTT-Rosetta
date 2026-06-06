# Chapter 11 The fundamental theorem of identity types

```agda
module chapter-11-the-fundamental-theorem-of-identity-types where
```

For many types it is useful to have a characterization of their identity types.
For example, we have used a characterization of the identity types of the fibers
of a map in order to conclude that any equivalence is a contractible map.
The fundamental theorem of identity types is our main tool to carry out such
characterizations, and with the fundamental theorem it becomes a routine task to
characterize an identity type whenever that is of interest.
We note that the fundamental theorem also appears as Theorem 5.8.4 in the HoTT
Book.

In our first application of the fundamental theorem of identity types we show
that any equivalence is an embedding.
Embeddings are maps that induce equivalences on identity types, i.e., they are
the homotopical analogue of injective maps.
In our second application we characterize the identity types of coproducts.

Throughout this book we will encounter many more occasions to characterize
identity types.
For example, we will show in this chapter that the identity type of the natural
numbers is equivalent to its observational equality, and later we will show that
the loop space of the circle is equivalent to `ℤ`.

In order to prove the fundamental theorem of identity types, we first prove the
basic fact that a family of maps is a family of equivalences if and only if it
induces an equivalence on total spaces.


```agda
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-3-equality-on-the-natural-numbers
open import section-11-4-embeddings
open import section-11-5-disjointness-of-coproducts
open import section-11-6-the-structure-identity-principle
open import exercise-11-1-coproduct-embeddings
open import exercise-11-2-paths-along-equivalences
open import exercise-11-3-homotopic-embeddings
open import exercise-11-4-embedding-triangles
open import exercise-11-5-composite-embeddings-equivalences
open import exercise-11-6-embeddings-from-coproducts
open import exercise-11-7-coproduct-functor-reflection
open import exercise-11-8-total-map-retractions
open import exercise-11-9-embedding-from-path-sections
open import exercise-11-10-path-split-maps
open import exercise-11-11-fiber-triangles
```
