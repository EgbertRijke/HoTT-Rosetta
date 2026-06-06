# Section 13.1 Equivalent forms of function extensionality

```agda
module section-13-1-equivalent-forms-of-function-extensionality where
```

The function extensionality principle characterizes the identity type of an
arbitrary dependent function type.
It asserts that the type `f = g` of identifications between two dependent
functions is equivalent to the type of homotopies `f ~ g`.
By Theorem `thm:id_fundamental` there are three equivalent ways of doing this.

## Proposition 13.1.1

Consider a dependent function `f : Π(x : A) B(x)`.
The following are equivalent:

1. The **function extensionality principle** holds at `f`: for each
   `g : Π(x : A) B(x)`, the family of maps

```text
  htpy-eq : (f = g) → (f ~ g)
```

defined by `htpy-eq(refl(f)) := refl-htpy_f` is a family of equivalences.

2. The total space

```text
  Σ(g : Π(x : A) B(x)) f ~ g
```

is contractible.

3. The principle of **homotopy induction**: for any family of types `P(g, H)`
   indexed by `g : Π(x : A) B(x)` and `H : f ~ g`, the evaluation function

```text
  (Π(g : Π(x : A) B(x)) Π(H : f ~ g) P(g, H)) →
  P(f, refl-htpy_f),
```

given by `s ↦ s(f, refl-htpy_f)`, has a section.

## Proof

This theorem follows directly from Theorem `thm:id_fundamental`.

There is, however, yet a fourth condition equivalent to the function
extensionality principle: the *weak* function extensionality principle.
The weak function extensionality principle asserts that any dependent product
of contractible types is again contractible.

The following theorem is stated with respect to an arbitrary universe `𝒰`,
because we will use it in Theorem `thm:funext-univalence` to show that the
univalence axiom implies function extensionality.

## Theorem 13.1.2

Consider a universe `𝒰`.
The following are equivalent:

1. The function extensionality principle holds in `𝒰`: For every type family
   `B` over `A` in `𝒰` and any `f g : Π(x : A) B(x)`, the map

```text
  htpy-eq : (f = g) → (f ~ g)
```

is an equivalence.

2. The **weak function extensionality principle** holds in `𝒰`: For every type
   family `B` over `A` in `𝒰` one has

```text
  (Π(x : A) is-contr(B(x))) → is-contr(Π(x : A) B(x)).
```

## Proof

First, we show that function extensionality implies weak function
extensionality.
Suppose that each `B(a)` is contractible with center of contraction `c(a)` and
contraction `C_a : Π(y : B(a)) c(a) = y`.
Then we take `c := λ a → c(a)` to be the center of contraction of
`Π(x : A) B(x)`.
To construct the contraction we have to define a term of type

```text
  Π(f : Π(x : A) B(x)) c = f.
```

Let `f : Π(x : A) B(x)`.
By function extensionality we have a map `(c ~ f) → (c = f)`, so it suffices
to construct a term of type `c ~ f`.
Here we take `λ a → C_a(f(a))`.
This completes the proof that function extensionality implies weak function
extensionality.

It remains to show that weak function extensionality implies function
extensionality.
By Proposition 13.1.1 it suffices to show that the type

```text
  Σ(g : Π(x : A) B(x)) f ~ g
```

is contractible for any `f : Π(x : A) B(x)`.
In order to do this, we first note that we have a section-retraction pair

```text
  (Σ(g : Π(x : A) B(x)) f ~ g)
    -- i --> (Π(x : A) Σ(b : B(x)) f(x) = b)
    -- r --> (Σ(g : Π(x : A) B(x)) f ~ g).
```

Here we have the functions

```text
  i := λ (g, H) → λ x → (g(x), H(x))
  r := λ p → (λ x → pr1(p(x)), λ x → pr2(p(x))).
```

Their composite is homotopic to the identity function by the computation rule
for `Σ`-types and the `η`-rule for `Π`-types:

```text
  r(i(g, H)) ≐ r(λ x → (g(x), H(x)))
            ≐ (λ x → g(x), λ x → H(x))
            ≐ (g, H).
```

Now we observe that the type `Π(x : A) Σ(b : B(x)) f(x) = b` is a product of
contractible types, so it is contractible by our assumption of the weak
function extensionality principle.
The claim now follows, because retracts of contractible types are contractible
by Exercise `ex:contr_retr`.

We will henceforth assume the function extensionality principle as an axiom.

## Axiom 13.1.3

For any type family `B` over `A`, and any two dependent functions
`f g : Π(x : A) B(x)`, the map

```text
  htpy-eq : (f = g) → (f ~ g)
```

is an equivalence.
We will write `eq-htpy` for its inverse.

## Remark 13.1.4

The function extensionality axiom is added to type theory by adding the rule

```text
  Γ, x : A ⊢ B(x) type
  Γ ⊢ f : Π(x : A) B(x)
  Γ ⊢ g : Π(x : A) B(x)
  --------------------------------
  Γ ⊢ funext : is-equiv(htpy-eq_{f,g}).
```

In the following theorem we extend the weak function extensionality principle
to general truncation levels.

## Theorem 13.1.5

For any type family `B` over `A` one has

```text
  (Π(x : A) is-trunc(k, B(x))) →
  is-trunc(k, Π(x : A) B(x)).
```

## Proof

The theorem is proven by induction on `k ≥ -2`.
The base case is just the weak function extensionality principle, which was
shown to follow from function extensionality in Theorem 13.1.2.

For the inductive step, assume that the `k`-truncated types are closed under
`Π`-types, and consider a family `B` of `(k + 1)`-truncated types.
To show that the type `Π(x : A) B(x)` is `(k + 1)`-truncated, we have to show
that the type `f = g` is `k`-truncated for every `f g : Π(x : A) B(x)`.
By function extensionality, the type `f = g` is equivalent to `f ~ g` for any
two dependent functions `f g : Π(x : A) B(x)`.
Now observe that `f ~ g` is a dependent product of `k`-truncated types, and
therefore it is `k`-truncated by the inductive hypothesis.
Since the `k`-truncated types are closed under equivalences by
Proposition 12.4.5, it follows that the type `f = g` is `k`-truncated.

## Corollary 13.1.6

Suppose `B` is a `k`-type.
Then `A → B` is also a `k`-type, for any type `A`.

## Remark 13.1.7

It follows that `¬ A` is a proposition for each type `A`.
Note that it requires function extensionality even just to prove that `¬ P` is
a proposition for any proposition `P`.
