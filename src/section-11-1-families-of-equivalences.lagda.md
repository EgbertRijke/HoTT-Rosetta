# Section 11.1 Families of equivalences

```agda
module section-11-1-families-of-equivalences where
```

## Definition 11.1.1

Consider a family of maps

```text
  f : Π(x : A) B(x) → C(x).
```

We define the map

```text
  tot(f) : Σ(x : A) B(x) → Σ(x : A) C(x)
```

by `λ (x, y). (x, f(x, y))`.

## Lemma 11.1.2

For any family of maps `f : Π(x : A) B(x) → C(x)` and any
`t : Σ(x : A) C(x)`, there is an equivalence

```text
  fib_tot(f)(t) ≃ fib_f(pr1(t))(pr2(t)).
```

## Proof

We first define

```text
  φ : Π(t : Σ(x : A) C(x)) fib_tot(f)(t) → fib_f(pr1(t))(pr2(t))
```

by pattern matching by

```text
  φ((x, f(x, y)), ((x, y), refl)) := (y, refl).
```

For the proof that `φ(t)` is an equivalence, for each `t : Σ(x : A) C(x)`, we
construct a map

```text
  ψ(t) : fib_f(pr1(t))(pr2(t)) → fib_tot(f)(t)
```

equipped with homotopies `G(t) : φ(t) ∘ ψ(t) ~ id` and
`H(t) : ψ(t) ∘ φ(t) ~ id`.
Each of these definitions is given by pattern matching:

```text
  ψ((x, f(x, y)), (y, refl))          := ((x, y), refl)
  G((x, f(x, y)), (y, refl))          := refl
  H((x, f(x, y)), ((x, y), refl))     := refl.
```

## Theorem 11.1.3

Let `f : Π(x : A) B(x) → C(x)` be a family of maps.
The following are equivalent:

1. For each `x : A`, the map `f(x)` is an equivalence.
In this case we say that `f` is a **family of equivalences**.
2. The map `tot(f) : Σ(x : A) B(x) → Σ(x : A) C(x)` is an equivalence.

## Proof

By Theorems 10.3.5 and 10.4.6 it suffices to show that `f(x)` is a contractible
map for each `x : A`, if and only if `tot(f)` is a contractible map.
Thus, we will show that `fib_f(x)(c)` is contractible if and only if
`fib_tot(f)(x, c)` is contractible, for each `x : A` and `c : C(x)`.
However, by Lemma 11.1.2 these types are equivalent, so the result follows by
Exercise 10.3.

Now consider the situation where we have a map `f : A → B`, and a family `C`
over `B`.
Then we have the map

```text
  λ (x, z). (f(x), z) : Σ(x : A) C(f(x)) → Σ(y : B) C(y).
```

We claim that this map is an equivalence when `f` is an equivalence.
The technique to prove this claim is the same as the technique we used in
Theorem 11.1.3: first we note that the fibers are equivalent to the fibers of
`f`, and then we use the fact that a map is an equivalence if and only if its
fibers are contractible to finish the proof.

The converse of the following lemma does not hold.

## Lemma 11.1.4

Consider a map `f : A → B`, and let `C` be a type family over `B`.
If `f` is an equivalence, then the map

```text
  σ_f(C) := λ (x, z). (f(x), z) :
    Σ(x : A) C(f(x)) → Σ(y : B) C(y)
```

is an equivalence.

## Proof

We claim that for each `t : Σ(y : B) C(y)` there is an equivalence

```text
  fib_σ_f(C)(t) ≃ fib_f(pr1(t)).
```

We obtain such an equivalence by constructing functions and homotopies by
pattern matching:

```text
  φ((f(x), z), ((x, z), refl))       := (x, refl)
  ψ((f(x), z), (x, refl))            := ((x, z), refl)
  G((f(x), z), (x, refl))            := refl
  H((f(x), z), ((x, z), refl))       := refl.
```

Now the claim follows, since `φ` is a contractible map if and only if `f` is a
contractible map.

Now we use Lemma 11.1.4 to obtain a generalization of Theorem 11.1.3.

## Definition 11.1.5

Consider a map `f : A → B` and a family of maps

```text
  g : Π(x : A) C(x) → D(f(x)),
```

where `C` is a type family over `A`, and `D` is a type family over `B`.
In this situation we also say that `g` is a **family of maps over `f`**.
Then we define

```text
  tot_f(g) : Σ(x : A) C(x) → Σ(y : B) D(y)
```

by `tot_f(g)(x, z) := (f(x), g(x, z))`.

## Theorem 11.1.6

Suppose that `g` is a family of maps over `f` as in Definition 11.1.5, and
suppose that `f` is an equivalence.
Then the following are equivalent:

1. The family of maps `g` over `f` is a family of equivalences.
2. The map `tot_f(g)` is an equivalence.

## Proof

Note that we have a commuting triangle

```text
  Σ(x : A) C(x) --tot_f(g)--> Σ(y : B) D(y)
       \                         ^
        \ tot(g)                /
         v                     / σ_f(D)
       Σ(x : A) D(f(x)).
```

By the assumption that `f` is an equivalence, it follows that the map

```text
  Σ(x : A) D(f(x)) → Σ(y : B) D(y)
```

is an equivalence.
Therefore it follows that `tot_f(g)` is an equivalence if and only if `tot(g)`
is an equivalence.
Now the claim follows, since `tot(g)` is an equivalence if and only if `g` is a
family of equivalences.
