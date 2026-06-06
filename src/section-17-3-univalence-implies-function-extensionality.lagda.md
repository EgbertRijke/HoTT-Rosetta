# Section 17.3 Univalence implies function extensionality

```agda
module section-17-3-univalence-implies-function-extensionality where
```

One of the first applications of the univalence axiom was Voevodsky's theorem
that the univalence axiom on a universe `𝒰` implies function extensionality for
types in `𝒰`.
The proof uses the fact that weak function extensionality implies function
extensionality.
We will also make use of the following lemma.

## Lemma 17.3.1

For any equivalence `e : X ≃ Y` in a univalent universe `𝒰`, and any type `A`,
the post-composition map

```text
  e ∘ _ : (A → X) → (A → Y)
```

is an equivalence.

This statement was also part of Exercise `ex:equiv-postcomp`.
That exercise is solved using function extensionality.
However, since our present goal is to derive function extensionality from the
univalence axiom, we cannot make use of that exercise.
Therefore we give a new proof, using the univalence axiom.

## Proof

Since `𝒰` is assumed to be a univalent universe, it satisfies by
Theorem 17.1.1 the principle of equivalence induction.
Therefore, it suffices to show that the post-composition map

```text
  id ∘ _ : (A → X) → (A → X)
```

is an equivalence.
This post-composition map is of course just the identity map on `A → X`, so it
is indeed an equivalence.

## Theorem 17.3.2

For any universe `𝒰`, the univalence axiom on `𝒰` implies function
extensionality on `𝒰`.

## Proof

Note that by Theorem 13.1.2 it suffices to show that univalence implies weak
function extensionality.
We note that the proof of Theorem 13.1.2 also goes through when it is
restricted to types in `𝒰`.

Suppose that `B : A → 𝒰` is a family of contractible types.
Our goal is to show that the product `Π(x : A) B(x)` is contractible.
Since each `B(x)` is contractible, the projection map
`pr1 : (Σ(x : A) B(x)) → A` is an equivalence by Exercise `ex:proj_fiber`.

Now it follows by Lemma 17.3.1 that `pr1 ∘ _` is an equivalence.
Consequently, it follows from Theorem `thm:contr_equiv` that the fibers of

```text
  pr1 ∘ _ : (A → Σ(x : A) B(x)) → (A → A)
```

are contractible.
In particular, the fiber at `id_A` is contractible.
Therefore it suffices to show that `Π(x : A) B(x)` is a retract of

```text
  Σ(f : A → Σ(x : A) B(x)) pr1 ∘ f = id_A.
```

In other words, we construct a section-retraction pair

```text
  (Π(x : A) B(x)) →
  (Σ(f : A → Σ(x : A) B(x)) pr1 ∘ f = id_A) →
  (Π(x : A) B(x)).
```

We define the function `i` by

```text
  i(f) := (λ x → (x, f(x)), refl_id).
```

To see that this definition is correct, we need to know that

```text
  λ x → pr1(x, f(x)) ≐ id.
```

This is indeed the case, by the `λ`-equality rule for `Π`-types.

Next, we define the function `r`.
Consider a function `h : A → Σ(x : A) B(x)` equipped with an identification
`p : pr1 ∘ h = id`.
Then we have the homotopy `htpy-eq(p) : pr1 ∘ h ~ id`.
Furthermore, we obtain `pr2(h(x)) : B(pr1(h(x)))`.
Using these ingredients, we define `r` by

```text
  r((h, p), x) := tr_B(htpy-eq(p, x), pr2(h(x))).
```

It remains to construct a homotopy `H : r ∘ i ~ id`.
We simply compute

```text
  r(i(f)) ≐ r(λ x → (x, f(x)), refl)
          ≐ tr_B(htpy-eq(refl, x), pr2(x, f(x)))
          ≐ tr_B(refl, f(x))
          ≐ f(x).
```

Thus we see that `r ∘ i ≐ id` by an application of the `η`-rule for `Π`-types.
Therefore we simply define `H(f) := refl`.
