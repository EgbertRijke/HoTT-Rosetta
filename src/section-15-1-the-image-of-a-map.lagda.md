# Section 15.1 The image of a map

```agda
module section-15-1-the-image-of-a-map where
```

## The universal property of the image

Recall from Exercise `ex:triangle_fib` that we made the following definition:

## Definition 15.1.1

Let `f : A → X` and `g : B → X` be maps.
A **morphism from `f` to `g` over `X`** consists of a map `h : A → B` equipped
with a homotopy `H : f ~ g ∘ h` witnessing that the triangle

```text
      h
  A ----> B
   \    /
  f \  / g
     X
```

commutes.
Thus, we define the type

```text
  hom-slice_X(f, g) := Σ(h : A → B) f ~ g ∘ h.
```

Composition of morphisms over `X` is defined by

```text
  (k, K) ∘ (h, H) := (k ∘ h, concat(H, K · h)).
```

## Definition 15.1.2

Consider a commuting triangle

```text
      q
  A ----> I
   \    /
  f \  / i
     X
```

with `H : f ~ i ∘ q`, where `i` is an embedding.
We say that `i` satisfies the **universal property of the image of `f`** if the
precomposition function

```text
  _ ∘ (q, H) : hom-slice_X(i, m) → hom-slice_X(f, m)
```

is an equivalence for every embedding `m : B ↪ X`.

## Lemma 15.1.3

For any `f : A → X` and any embedding `m : B → X`, the type
`hom-slice_X(f, m)` is a proposition.

## Proof

Recall from Exercise `ex:triangle_fib` that the type `hom-slice_X(f, m)` is
equivalent to the type

```text
  Π(a : A) fib(m, f(a)).
```

Furthermore, recall from Theorem 12.2.3 that a map is an embedding if and only
if its fibers are propositions.
Thus we see that the type `Π(a : A) fib(m, f(a))` is a product of
propositions, hence it is a proposition by Theorem 13.1.5.

## Proposition 15.1.4

Consider a commuting triangle

```text
      q
  A ----> I
   \    /
  f \  / i
     X
```

with `H : f ~ i ∘ q`, where `i` is an embedding.
Then the following are equivalent:

1. The embedding `i` satisfies the universal property of the image inclusion of
   `f`.
2. For every embedding `m : B → X` there is a map

```text
  hom-slice_X(f, m) → hom-slice_X(i, m).
```

## Proof

Since `hom-slice_X(f, m)` is a proposition for every embedding `m : B → X`, the
claim follows immediately by the observation made in Remark 14.1.2.

## The existence of the image

The image of a map `f : A → X` can be defined using the propositional
truncation.

## Definition 15.1.5

For any map `f : A → X` we define the **image** of `f` to be the type

```text
  im(f) := Σ(x : X) ∥ fib(f, x) ∥.
```

Furthermore, we define:

1. The **image inclusion**

```text
  i_f : im(f) → X
```

to be the projection `pr1`.

2. The map

```text
  q_f : A → im(f)
```

to be the map given by `q_f(x) := (f(x), η(x, refl(f(x))))`.

3. The homotopy `I_f : f ~ i_f ∘ q_f` witnessing that the triangle

```text
      q_f
  A ----> im(f)
   \      /
  f \    / i_f
     X
```

commutes, to be given by `I_f(x) := refl(f(x))`.

## Proposition 15.1.6

The image inclusion `i_f : im(f) → X` of any map `f : A → X` is an embedding.

## Proof

The claim follows directly by Corollary 12.2.4, because the type
`∥ fib(f, x) ∥` is a proposition for each `x : X`.

## Theorem 15.1.7

The image inclusion `i_f : im(f) → X` of any map `f : A → X` satisfies the
universal property of the image inclusion of `f`.

## Proof

Consider an embedding `m : B ↪ X`.
Note that we have a commuting square

```text
  hom-slice_X(i_f, m) ----> hom-slice_X(f, m)
          |                         |
          v                         v
  Π(x : X) fib(i_f, x) → fib(m, x)
      ----> Π(x : X) fib(f, x) → fib(m, x)
```

in which all four types are propositions, and the vertical maps are
equivalences.
Therefore it suffices to construct a map

```text
  (Π(x : X) fib(f, x) → fib(m, x)) →
  (Π(x : X) fib(i_f, x) → fib(m, x)).
```

The fiber `fib(i_f, x)` is equivalent to the propositional truncation
`∥ fib(f, x) ∥` and the type `fib(m, x)` is a proposition by the assumption
that `m` is an embedding.
Therefore we obtain the desired map by the universal property of the
propositional truncation.

## The uniqueness of the image

We will now show that the universal property of the image implies that the
image is determined uniquely up to equivalence.

## Theorem 15.1.8

Let `f` be a map, and consider two commuting triangles

```text
      q                         q'
  A ----> B                 A ----> B'
   \    /                    \    /
  f \  / i                  f \  / i'
     X                         X
```

with `I : f ~ i ∘ q` and `I' : f ~ i' ∘ q'`, in which `i` and `i'` are assumed
to be embeddings.
Then, if any two of the following three properties hold, so does the third:

1. The embedding `i` satisfies the universal property of the image inclusion of
   `f`.
2. The embedding `i'` satisfies the universal property of the image inclusion
   of `f`.
3. The type of equivalences `e : B ≃ B'` equipped with a homotopy witnessing
   that the triangle

```text
      e
  B ----> B'
   \    /
  i \  / i'
     X
```

commutes is contractible.

## Proof

First, we show that if (i) and (ii) hold, then (iii) holds.
Note that the type `hom-slice_X(i, i')` is a proposition, since `i'` is assumed
to be an embedding.
Therefore it suffices to show that the unique map `h : B → B'` such that the
triangle

```text
      h
  B ----> B'
   \    /
  i \  / i'
     X
```

commutes, is an equivalence.
To see this, note that by Exercise `ex:triangle_fib` it suffices to show that
the action on fibers

```text
  fib(i, x) → fib(i', x)
```

is an equivalence for each `x : X`.
This follows from the universal property of `i'`, since we similarly obtain a
family of maps

```text
  fib(i', x) → fib(i, x)
```

indexed by `x : X`, and the types `fib(i, x)` and `fib(i', x)` are propositions
by the assumptions that `i` and `i'` are embeddings.

Now we will show that (iii) implies that (i) holds if and only if (ii) holds.
We will assume a morphism `(e, H) : hom-slice_X(i, i')` such that the map `e`
is an equivalence.
Furthermore, consider an embedding `m : C → X`.
Then the fact that (i) holds if and only if (ii) holds follows from the
equivalence

```text
  (hom-slice_X(f, m) → hom-slice_X(i, m)) ≃
  (hom-slice_X(f, m) → hom-slice_X(i', m)).
```
