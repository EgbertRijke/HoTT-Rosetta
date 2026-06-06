# Section 11.6 The structure identity principle

```agda
module section-11-6-the-structure-identity-principle where
```

We often encounter a type consisting of certain objects equipped with further
structure.
For example, the fiber of a map `f : A → B` at `b : B` is the type of elements
`a : A` equipped with an identification `p : f(a) = b`.
Such *structure* types occur all over mathematics, and it is important to have
an efficient characterization of their identity types.
A general structure type is just a `Σ`-type, and we're asking for a
characterization of its identity type.

Recall from Theorem 9.3.4 that the identity type of the type `Σ(x : A) B(x)` at
a pair `(a, b)` can be characterized as

```text
  ((a, b) = (x, y)) ≃ Σ(p : a = x) tr_B(p, b) = y.
```

However, this characterization of the identity type of `Σ(x : A) B(x)` is not
as clear and useful as we like it to be, because it uses the transport function,
which is completely generic.
Our plan is to use identity systems on `A` and on `B(a)` to arrive at a more
useful characterization of the identity type of `Σ(x : A) B(x)`.

In order to abstract away this characterization, let `C : A → 𝕌` be the family
of types given by `C(x) := a = x`, and let

```text
  D : Π(x : A) B(x) → (C(x) → 𝕌)
```

be the family of types given by `D(x, y, p) := tr_B(p, b) = y`.
Then `C` is an identity system on `A` at `a`, and the type family
`y ↦ D(a, y, refl)` is an identity system on `B(a)` at `b`.
This suggests the following definition of dependent identity systems.

## Definition 11.6.1

Consider a type `A` equipped with an identity system `C` based at `a : A`, and
let `c : C(a)`.
Furthermore, consider a type family `B` over `A`.
A **dependent identity system** over `C` at `b : B(a)` consists of a type family

```text
  D : Π(x : A) B(x) → (C(x) → 𝕌)
```

equipped with an element `d : D(a, b, c)` such that `y ↦ D(a, y, c)` is an
identity system at `b`.

## Theorem 11.6.2

Consider a type family `B` over `A`, elements `a : A` and `b : B(a)`, and an
identity system `C` of `A` with `c : C(a)`.
Furthermore, consider a type family

```text
  D : Π(x : A) B(x) → (C(x) → 𝕌)
```

equipped with an element `d : D(a, b, c)`.
Then the following are equivalent:

1. Any family of maps

```text
  (b = y) → D(a, y, c)
```

indexed by `y : B(a)` is a family of equivalences.
2. The total space

```text
  Σ(y : B(a)) D(a, y, c)
```

is contractible.
3. `D` is a dependent identity system over `C` at `b : B(a)`.
4. Any family of maps

```text
  ((a, b) = (x, y)) → Σ(z : C(x)) D(x, y, z)
```

indexed by `(x, y) : Σ(x : A) B(x)` is a family of equivalences.
5. The total space

```text
  Σ((x, y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x, y, z)
```

is contractible.
6. The type family

```text
  (x, y) ↦ Σ(z : C(x)) D(x, y, z)
```

is an identity system at `(a, b) : Σ(x : A) B(x)`.

## Proof

The first three statements as well as the last three statements are equivalent
by Theorem 11.2.2.
Therefore it suffices to show that the second and fifth statements are
equivalent.
Note that there is an equivalence

```text
  Σ((x, y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x, y, z)
    ≃ Σ((x, z) : Σ(x : A) C(x)) Σ(y : B(x)) D(x, y, z).
```

This equivalence, its inverse, and the homotopies witnessing that the inverse is
indeed an inverse are all straightforward to construct using pattern matching.
Furthermore, notice that the type `Σ(x : A) C(x)` is contractible with center of
contraction `(a, c)` since `C` is assumed to be an identity system at `a : A`.
Therefore it follows that

```text
  Σ((x, y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x, y, z)
    ≃ Σ(y : B(a)) D(a, y, c).
```

## Example 11.6.3

By the structure identity principle in combination with the fundamental theorem
of identity types, it becomes completely routine to characterize identity types
of structures.
We only have to show that the types

```text
  Σ(x : A) C(x)
  Σ(y : B(a)) D(a, y, c)
```

are contractible.
To illustrate this use of the structure identity principle, we give an
alternative characterization of the fiber of a map `f : A → B` at `b : B`.
We claim that

```text
  ((x, p) = (y, q)) ≃ fib_ap_f(p ∙ q⁻¹)
                  ≐ Σ(α : x = y) ap f α = (p ∙ q)⁻¹.
```

To see this, we apply Theorem 11.6.2.
Note that `Σ(y : A) x = y` is contractible by Theorem 10.1.4 with center of
contraction `(x, refl(f(x)))`.
Therefore it suffices to show that the type

```text
  Σ(q : f(x) = b) refl(f(x)) = (p ∙ q)⁻¹
```

is contractible.
This type is equivalent to `Σ(q : f(x) = b) p = q`, which is again contractible
by Theorem 10.1.4.
