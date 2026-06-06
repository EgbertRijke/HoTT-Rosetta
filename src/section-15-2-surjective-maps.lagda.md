# Section 15.2 Surjective maps

```agda
module section-15-2-surjective-maps where
```

A map `f : A → B` is surjective if for every `b : B` there is an
*unspecified* element `a : A` that maps to `b`.
We define this property using the propositional truncation.

## Definition 15.2.1

A map `f : A → B` is said to be **surjective** if there is an element of type

```text
  is-surj(f) := Π(b : B) ∥ fib(f, b) ∥.
```

## Example 15.2.2

Any equivalence is a surjective map, since its fibers are contractible.
More generally, any map that has a section is surjective.
Those are sometimes called **split epimorphisms**.
Note that having a section is stronger than surjectivity, since in general we
do not have a function `∥ fib(f, b) ∥ → fib(f, b)`.

In Exercise 14.4 we showed the dependent universal property of the
propositional truncation: a map `f : A → B` into a proposition `B` satisfies
the universal property of the propositional truncation if and only if for every
family of propositions `P` over `B`, the precomposition map

```text
  _ ∘ f : (Π(b : B) P(b)) → (Π(a : A) P(f(a)))
```

is an equivalence.
In the following proposition we show that, if we omit the condition that `B` is
a proposition, then `f` satisfies this dependent universal property if and only
if `f` is surjective.

## Proposition 15.2.3

Consider a map `f : A → B`.
Then the following are equivalent:

1. The map `f : A → B` is surjective.
2. The map `f : A → B` satisfies the **dependent universal property of a
   surjective map**: For any family `P` of propositions over `B`, the
   precomposition map

```text
  _ ∘ f : (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
```

is an equivalence.
In other words, any subtype of `B` that contains all the elements of the form
`f(x)` contains all the elements of `B`.

3. For any `k ≥ -2`, and for any family `P` of `(k + 1)`-truncated types over
   `B`, the precomposition map

```text
  _ ∘ f : (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
```

is a `k`-truncated map.

## Proof

To prove that (i) implies (ii), suppose first that `f` is surjective, and
consider the commuting square

```text
  Π(y : B) P(y) ------------------> Π(x : A) P(f(x))
       |                                      ^
       v                                      |
  Π(y : B) ∥ fib(f, y) ∥ → P(y) --> Π(y : B) fib(f, y) → P(y).
```

In this square, the bottom map is an equivalence by Exercise `ex:equiv-pi` and
by the universal property of the propositional truncation of `fib(f, y)`.
The map on the right is an equivalence by Exercise `ex:pi-fib`.
Furthermore, the map on the left is an equivalence by Exercises `ex:equiv-pi`
and `ex:up-unit`, because the type `∥ fib(f, y) ∥` is contractible by the
assumption that `f` is surjective.
Therefore it follows that the top map is an equivalence, which completes the
proof that (i) implies (ii).

The proof that (ii) implies (iii) is by induction on `k`.
The base case holds by assumption.
For the inductive step, it suffices by Theorem 12.4.7 to show that
`ap_{_ ∘ f}` is `k`-truncated for any `g h : Π(y : B) P(y)`.
Notice that we have a commuting square

```text
  (g = h) ------------------> (g ∘ f = h ∘ f)
     |                                |
     v                                v
  Π(y : B) g(y) = h(y) --> Π(x : A) g(f(x)) = h(f(x)).
```

The vertical maps on the left and right are equivalences by function
extensionality, and the bottom map is `k`-truncated by the inductive
hypothesis.
This implies that `ap_{_ ∘ f}` is `k`-truncated.

To prove that (iii) implies (i), note that the assumption in (iii) implies that
the precomposition function

```text
  _ ∘ f :
    (Π(y : B) ∥ fib(f, y) ∥) →
    (Π(x : A) ∥ fib(f, f(x)) ∥)
```

is an equivalence.
Hence it suffices to construct an element of type `∥ fib(f, f(x)) ∥` for each
`x : A`.
This is easy, because we have

```text
  η(x, refl(f(x))) : ∥ fib(f, f(x)) ∥.
```

As a corollary we obtain that any surjective map into a proposition satisfies
the universal property of the propositional truncation.

## Corollary 15.2.4

For any map `f : A → P` into a proposition `P`, the following are equivalent:

1. The map `f` satisfies the universal property of the propositional truncation
   of `A`.
2. The map `f` is surjective.

Using the characterization of surjective maps of Proposition 15.2.3, we can
also give a new characterization of the image of a map.

## Theorem 15.2.5

Consider a commuting triangle

```text
      q
  A ----> B
   \    /
  f \  / m
     X
```

in which `m` is an embedding.
Then the following are equivalent:

1. The embedding `m` satisfies the universal property of the image inclusion of
   `f`.
2. The map `q` is surjective.

## Proof

First assume that `m` satisfies the universal property of the image inclusion
of `f`, and consider the composite function

```text
  (Σ(y : B) ∥ fib(q, y) ∥) --pr1--> B --m--> X.
```

Note that `m ∘ pr1` is a composition of embeddings, so it is an embedding.
By the universal property of `m` there is a unique map `h` for which the
triangle

```text
  B ----h----> Σ(y : B) ∥ fib(q, y) ∥
   \             /
  m \           / m ∘ pr1
     X
```

commutes.
Now note that `pr1 ∘ h` is a map such that `m ∘ (pr1 ∘ h) ~ m`.
The identity function is another map for which we have `m ∘ id ~ m`, so it
follows by uniqueness that `pr1 ∘ h ~ id`.
In other words, the map `h` is a section of the projection map.
Therefore we obtain by Corollary 13.2.3 a dependent function

```text
  Π(b : B) ∥ fib(q, b) ∥,
```

showing that `q` is surjective.

For the converse, suppose that `q` is surjective.
To prove that `m` satisfies the universal property of the image factorization
of `f`, it suffices to construct a map

```text
  hom-slice_X(f, m') → hom-slice_X(m, m')
```

for any embedding `m' : B' → X`.
To see that there is such an equivalence, we make the following calculation

```text
  hom-slice_X(m, m')
    ≃ Π(b : B) fib(m', m(b))
    ≃ Π(a : A) fib(m', m(q(a)))
    ≃ Π(a : A) fib(m', f(a))
    ≃ hom-slice_X(f, m').
```

The first and fourth equivalences are by Exercise `ex:triangle_fib`, the second
is by Proposition 15.2.3, and the third is by `f ~ m ∘ q`.

## Corollary 15.2.6

Every map factors uniquely as a surjective map followed by an embedding.

## Proof

Consider a map `f : A → X`, and two factorizations

```text
      q                         q'
  A ----> B                 A ----> B'
   \    /                    \    /
  f \  / i                  f \  / i'
     X                         X
```

of `f` where `m` and `m'` are embeddings, and `q` and `q'` are surjective.
Then both `m` and `m'` satisfy the universal property of the image
factorization of `f` by Theorem 15.2.5.
Now it follows by Theorem 15.1.8 that the type of `(e, H) : hom-slice_X(i, i')`
in which `e` is an equivalence, equipped with an identification

```text
  (e, H) ∘ (q, I) = (q', I')
```

in `hom-slice_X(f, i')`, is contractible.
