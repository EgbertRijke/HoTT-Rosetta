# Exercise 14.9 Interval

```agda
module exercise-14-9-interval where
```

## Problem statement

In this exercise we introduce the **interval** as a higher inductive type `𝕀`,
equipped with two point constructors and one path constructor

```text
  source target : 𝕀
  path-𝕀        : source = target.
```

The induction principle of `𝕀` asserts that for any type family `P` over `𝕀`,
if we have

```text
  u : P(source)
  v : P(target)
  p : tr_P(path-𝕀, u) = v,
```

then there is a section `f : Π(x : 𝕀) P(x)` equipped with identifications

```text
  α : f(source) = u
  β : f(target) = v
```

and an identification `γ` witnessing that the square

```text
  tr_P(path-𝕀, f(source)) --ap_{tr_P(path-𝕀)}(α)--> tr_P(path-𝕀, u)
            |                                             |
        apd_f(path-𝕀)                                    p
            |                                             |
            v                                             v
        f(target) -------------------β------------------> v
```

commutes.
Note that the constructors of `𝕀` induce a map

```text
  ε :
    (Π(x : 𝕀) P(x)) →
    (Σ(u : P(source)) Σ(v : P(target)) tr_P(path-𝕀, u) = v)
```

given by `f ↦ (f(source), f(target), apd_f(path-𝕀))`.

Characterize the identity types of the codomain of the map `ε` in the following
way: Construct an equivalence from the type `(u, v, q) = (u', v', q')` to the
type

```text
  Σ(α : u = u') Σ(β : v = v')
    concat(q, β) = concat(ap_{tr_P(path-𝕀)}(α), q'),
```

for any `(u, v, q)` and `(u', v', q')` in the codomain of `ε`.

## Solution

## Problem statement

Prove the dependent universal property of `𝕀`, i.e., show that the map `ε` is
an equivalence.

## Solution

## Problem statement

Show that `𝕀` is contractible.

## Solution
