# Section 9.1 Homotopies

```agda
module section-9-1-homotopies where
```

In type theory we are very limited in constructing identifications of functions.
The following example illustrates a case where type theory provides no rules to
construct an identification between two maps, even though they are pointwise
equal.

## Remark 9.1.1

Consider the negation function `neg-bool : bool → bool` on the booleans, which
was defined in Exercise 4.2.
Type theory does not provide any means to show that

```text
  neg-bool ∘ neg-bool = id.
```

The best we can do is to construct an identification

```text
  neg-neg-bool(b) : neg-bool(neg-bool(b)) = b
```

for any `b : bool`.
Indeed, `neg-neg-bool` is defined using the induction principle of `bool`, by

```text
  neg-neg-bool(true)  := refl(true)
  neg-neg-bool(false) := refl(false).
```

Therefore we see that, while we cannot identify `neg-bool ∘ neg-bool` with
`id`, we can define a *pointwise identification* between the values of
`neg-bool ∘ neg-bool` and `id`.

The observations in Remark 9.1.1 are an instance of a general phenomenon in type
theory: it is often much easier to construct a *pointwise identification*
between the values of two maps, than it is to construct an identification
between those two maps.
In fact, the prevalent notion of sameness of maps is the notion of pointwise
identification.
Since they are so important, we will give them a name and call them
*homotopies*.

## Definition 9.1.2

Let `f, g : Π(x : A) B(x)` be two dependent functions.
The type of **homotopies** from `f` to `g` is defined as the type of pointwise
identifications, i.e., we define

```text
  f ~ g := Π(x : A) f(x) = g(x).
```

## Example 9.1.3

By Remark 9.1.1 we have a homotopy

```text
  neg-neg-bool : neg-bool ∘ neg-bool ~ id.
```

## Remark 9.1.4

We will use homotopies, for example, to express the commutativity of diagrams.
For example, we say that a triangle

```text
      h
  A ----> B
   \    /
  f \  / g
     X
```

**commutes** if it comes equipped with a homotopy `H : f ~ g ∘ h`.
Similarly, we say that a square

```text
  A  ----> A'
  |        |
  |        |
  v        v
  B  ----> B'
```

commutes if it comes equipped with a homotopy `h ∘ f ~ f' ∘ g`.

Note that the type of homotopies `f ~ g` is defined for dependent functions,
and moreover the type of homotopies is itself a dependent function type.
The definition of homotopies is therefore set up in such a way that we may also
consider homotopies *between* homotopies, and even further homotopies between
those higher homotopies.
More concretely, if `H, K : f ~ g` are two homotopies, then the type of
homotopies `H ~ K` between them is just the type

```text
  Π(x : A) H(x) = K(x).
```

Since homotopies are pointwise identifications, we can use the groupoidal
structure of identity types to also define the groupoidal structure of
homotopies.
In this case, however, we state the groupoid laws as *homotopies* and
*homotopies between homotopies* rather than as identifications.

## Definition 9.1.5

For any type family `B` over `A` we define the operations on homotopies

```text
  refl-htpy   : Π(f : Π(x : A) B(x)) f ~ f
  inv-htpy    : Π(f g : Π(x : A) B(x)) (f ~ g) → (g ~ f)
  concat-htpy :
    Π(f g h : Π(x : A) B(x)) (f ~ g) → ((g ~ h) → (f ~ h))
```

pointwise by

```text
  refl-htpy(f)      := λ x. refl(f(x))
  inv-htpy(H)       := λ x. H(x)⁻¹
  concat-htpy(H, K) := λ x. H(x) ∙ K(x).
```

We will often write `H⁻¹` for `inv-htpy(H)`, and `H ∙ K` for
`concat-htpy(H, K)`.

## Proposition 9.1.6

Homotopies satisfy the groupoid laws:

1. Concatenation of homotopies is associative up to homotopy, i.e., there is a
homotopy

```text
  assoc-htpy(H, K, L) : (H ∙ K) ∙ L ~ H ∙ (K ∙ L)
```

for any homotopies `H : f ~ g`, `K : g ~ h` and `L : h ~ i`.

2. Homotopies satisfy the left and right unit laws up to homotopy, i.e., there
are homotopies

```text
  left-unit-htpy(H)  : refl-htpy_f ∙ H ~ H
  right-unit-htpy(H) : H ∙ refl-htpy_g ~ H
```

for any homotopy `H`.

3. Homotopies satisfy the left and right inverse laws up to homotopy, i.e.,
there are homotopies

```text
  left-inv-htpy(H)  : H⁻¹ ∙ H ~ refl-htpy_g
  right-inv-htpy(H) : H ∙ H⁻¹ ~ refl-htpy_f
```

for any homotopy `H`.

## Proof

The homotopy `assoc-htpy(H, K, L)` is defined pointwise by

```text
  assoc-htpy(H, K, L, x) := assoc(H(x), K(x), L(x)).
```

The other homotopies are similarly defined pointwise.

Apart from the groupoid operations and their laws, we will occasionally need
*whiskering* operations.
Whiskering operations are operations that allow us to compose homotopies with
functions.
There are two situations where we want this: post-composing a homotopy by a
function, and pre-composing a homotopy by a function.

## Definition 9.1.7

We define the following **whiskering** operations on homotopies:

1. Suppose `H : f ~ g` for two functions `f, g : A → B`, and let `h : B → C`.
We define

```text
  h · H := λ x. ap h (H(x)) : h ∘ f ~ h ∘ g.
```

2. Suppose `f : A → B` and `H : g ~ h` for two functions `g, h : B → C`.
We define

```text
  H · f := λ x. H(f(x)) : g ∘ f ~ h ∘ f.
```
