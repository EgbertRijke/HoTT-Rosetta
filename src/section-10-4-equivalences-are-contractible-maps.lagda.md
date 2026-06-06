# Section 10.4 Equivalences are contractible maps

```agda
module section-10-4-equivalences-are-contractible-maps where
```

In Theorem 10.4.6 we will show the converse to Theorem 10.3.5, i.e., we will
show that any equivalence is a contractible map.
We will do this in two steps.

First we introduce a new notion of *coherently invertible map*, for which we can
easily show that such maps have contractible fibers.
Then we show that any equivalence is a coherently invertible map.

Recall that an invertible map is a map `f : A → B` equipped with `g : B → A` and
homotopies

```text
  G : f ∘ g ~ id
  H : g ∘ f ~ id.
```

Then we observe that both `G · f` and `f · H` are homotopies of the same type

```text
  f ∘ g ∘ f ~ f.
```

A coherently invertible map is an invertible map for which there is a further
homotopy `G · f ~ f · H`.

## Definition 10.4.1

Consider a map `f : A → B`.
We say that `f` is **coherently invertible** if it comes equipped with

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id
  K : G · f ~ f · H.
```

We will write `is-coh-invertible(f)` for the type of quadruples `(g, G, H, K)`.

Although we will encounter the notion of coherently invertible map on some
further occasions, the following proposition is our main motivation for
considering it.

## Proposition 10.4.2

Any coherently invertible map has contractible fibers.

## Proof

Consider a map `f : A → B` equipped with

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id
  K : G · f ~ f · H,
```

and let `y : B`.
Our goal is to show that `fib_f(y)` is contractible.
For the center of contraction we take `(g(y), G(y))`.
In order to construct a contraction, it suffices to construct a dependent
function of type

```text
  Π(x : A) Π(p : f(x) = y) Eq-fib_f((g(y), G(y)), (x, p)).
```

By path induction on `p : f(x) = y` it suffices to construct a dependent
function of type

```text
  Π(x : A) Eq-fib_f((g(f(x)), G(f(x))), (x, refl(f(x)))).
```

By definition of `Eq-fib_f`, we have to construct for each `x : A` an
identification `α : g(f(x)) = x` equipped with a further identification

```text
  G(f(x)) = ap f α ∙ refl(f(x)).
```

Such a dependent function is constructed as `λ x. (H(x), K'(x))`, where the
homotopy `H : g ∘ f ~ id` is given by assumption, and the homotopy

```text
  K' : Π(x : A) G(f(x)) = ap f (H(x)) ∙ refl(f(x))
```

is defined as `K ∙ right-unit-htpy(f · H)⁻¹`.

Our next goal is to show that for any map `f : A → B` equipped with

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id,
```

we can improve the homotopy `G` to a new homotopy `G' : f ∘ g ~ id` for which
there is a further homotopy

```text
  f · H ~ G' · f.
```

Note that this situation is analogous to the situation in the proof of
Theorem 10.2.3, where we improved the contraction `C` so that it satisfied
`C(c) = refl`.
The extra coherence `f · H ~ G' · f` is then used in the proof that the fibers
of an equivalence are contractible.

## Definition 10.4.3

Let `f, g : A → B` be functions, and consider `H : f ~ g` and `p : x = y` in
`A`.
We define the identification

```text
  nat-htpy(H, p) : ap f p ∙ H(y) = H(x) ∙ ap g p
```

witnessing that the naturality square of the homotopy `H` at `p` commutes.

## Construction

By path induction on `p` it suffices to construct an identification

```text
  ap f refl(x) ∙ H(x) = H(x) ∙ ap g refl(x).
```

Since `ap f refl(x) ≐ refl(f(x))` and `ap g refl(x) ≐ refl(g(x))`, and since
`refl(f(x)) ∙ H(x) ≐ H(x)`, we see that the path `right-unit(H(x))⁻¹` is of the
asserted type.

## Definition 10.4.4

Consider `f : A → A` and `H : f ~ id_A`.
We construct an identification `H(f(x)) = ap f (H(x))`, for any `x : A`.

## Construction

By the naturality of homotopies with respect to identifications, the square

```text
  f(f(x)) --H(f(x))--> f(x)
     |                  |
  ap f (H(x))           H(x)
     |                  |
     v                  v
   f(x) ----H(x)-----> x
```

commutes.
This gives the desired identification `H(f(x)) = ap f (H(x))`.

## Lemma 10.4.5

Let `f : A → B` be a map equipped with an inverse, i.e., consider

```text
  g : B → A
  G : f ∘ g ~ id
  H : g ∘ f ~ id.
```

Then there is a homotopy `G' : f ∘ g ~ id` equipped with a further homotopy

```text
  K : f · H ~ G' · f.
```

Thus we obtain a map `has-inverse(f) → is-coh-invertible(f)`.

## Proof

For each `y : B`, we construct the identification `G'(y)` as the concatenation

```text
  f(g(y)) = f(g(f(g(y)))) = f(g(y)) = y.
```

In order to construct a homotopy `f · H ~ G' · f`, it suffices to show that a
certain square involving `G` and `H` commutes for every `x : A`.
Recall from Definition 10.4.4 that we have `H(g(f(x))) = ap(g ∘ f)(H(x))`.
Using this identification, we see that it suffices to show that a naturality
square for the homotopy `G · f : f ∘ g ∘ f ~ f` commutes.
This commutes by Definition 10.4.3.

Now we put the pieces together to conclude that any equivalence has contractible
fibers.

## Theorem 10.4.6

Any equivalence is a contractible map.

## Proof

We have seen in Proposition 10.4.2 that any coherently invertible map is a
contractible map.
Moreover, any equivalence has the structure of an invertible map by
Proposition 9.2.7, and any invertible map is coherently invertible by
Lemma 10.4.5.

The following corollary is very similar to Theorem 10.1.4, which asserts that
the type `Σ(x : A) a = x` is contractible.
However, we haven't yet established that the equivalence `(a = x) ≃ (x = a)`
induces an equivalence on total spaces.
However, using the fact that equivalences are contractible maps we can give a
direct proof.

## Corollary 10.4.7

Let `A` be a type, and let `a : A`.
Then the type

```text
  Σ(x : A) x = a
```

is contractible.

## Proof

By Example 9.2.3, the identity function is an equivalence.
Therefore, the fibers of the identity function are contractible by
Theorem 10.4.6.
Note that `Σ(x : A) x = a` is exactly the fiber of `id_A` at `a : A`.
