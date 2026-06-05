# Section 5.4 Transport

```agda
module section-5-4-transport where
```

Dependent types also come with an action on identifications:  the *transport*
functions.
Given an identification `p : x = y` in the base type `A`, we can transport any
element `b : B(x)` to the fiber `B(y)`.

## Definition 5.4.1

Let `A` be a type, and let `B` be a type family over `A`.
We will construct a **transport**

```text
  tr_B : Π(x, y : A) x = y → B(x) → B(y).
```

## Construction

We construct `tr_B(p)` by induction on `p : x = y`, taking

```text
  tr_B(refl) ≔  id.
```

## Prelude to Definition 5.4.2

Thus we see that type theory cannot distinguish between identified elements `x`
and `y`, because for any type family `B` over `A` one obtains an element of
`B(y)` from the elements of `B(x)`.

As an application of the transport function we construct the *dependent* action
on paths of a dependent function `f : Π(x : A) B(x)`.
Note that for such a dependent function `f`, and an identification `p : x = y`,
it does not make sense to directly compare `f(x)` and `f(y)`, since the type of
`f(x)` is `B(x)` whereas the type of `f(y)` is `B(y)`, which might not be
exactly the same type.
However, we can first *transport* `f(x)` along `p`, so that we obtain the
element `tr_B(p, f(x))` which is of type `B(y)`.
Now we can ask whether it is the case that `tr_B(p, f(x)) = f(y)`.
The dependent action on paths of `f` establishes this identification.

## Definition 5.4.2

Given a dependent function `f : Π(a : A) B(a)` and an identification
`p : x = y` in `A`, we construct an identification

```text
  apd_f(p) : tr_B(p, f(x)) = f(y).
```

## Construction

The identification `apd_f(p)` is constructed by the induction principle for
identity types.
Thus, it suffices to construct an identification

```text
  apd_f(refl) : tr_B(refl, f(x)) = f(x).
```

Since transporting along `refl` is the identity function on `B(x)`, we simply
take `apd_f(refl) ≔ refl`.
