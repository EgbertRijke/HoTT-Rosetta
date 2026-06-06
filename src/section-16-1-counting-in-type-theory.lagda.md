# Section 16.1 Counting in type theory

```agda
module section-16-1-counting-in-type-theory where
```

When someone counts the elements of a finite set `A`, they go through the
elements of `A` one by one, at each stage keeping track of how many elements
have been counted so far.
This process results in the number `|A|` of elements of the set `A`, and
moreover it gives a bijection from the standard finite set with `|A|` elements.
In other words, to count the elements of `A` is to give an equivalence from one
of the standard finite sets to the set `A`.
We turn this into a definition.

## Definition 16.1.1

For each type `A`, we define the type

```text
  count(A) := Σ(k : ℕ) (Fin(k) ≃ A).
```

The elements of `count(A)` are called **countings** of `A`.
When we have `(k, e) : count(A)`, we also say that `A` **has `k` elements**.

Note that the type `count(A)` is often not a proposition.
For instance, different equivalences of type `Fin(k) ≃ Fin(k)` induce
different elements of type `count(Fin(k))`.

## Example 16.1.2

It follows immediately from the definition of countings that every standard
finite type can be counted in a canonical way: For any `k : ℕ` we have
`(k, id) : count(Fin(k))`.
It also follows immediately from the definition of countings that types
equipped with countings are closed under equivalences.

## Example 16.1.3

Suppose `A` comes equipped with a counting `(k, e) : count(A)`.
Then `k = 0` if and only if `A` is empty.
Indeed, the inverse of `e` is a map `e^{-1} : A → empty`.
Conversely, if we have `f : is-empty(A)`, then the map `f : A → empty` is
automatically an equivalence.
This shows that `Fin(k) ≃ empty`, and a short argument by induction on `k`
yields that `k = 0`.

## Example 16.1.4

A type `A` has one element if and only if it is contractible.
Indeed, the type `Fin(1)` is contractible, so it follows from the 3-for-2
property of contractible types, Exercise `ex:contr_retr`, that there is an
equivalence `Fin(1) ≃ A` if and only if `A` is contractible.

## Example 16.1.5

A proposition `P` comes equipped with a counting if and only if it is decidable.
To see this, note that for any type `X`, if we have `(k, e) : count(X)`, then
it follows that `X` is decidable.
This is shown by induction on `k`.
In the case where `k = 0`, it follows that `X` is empty, and hence that `X` is
decidable.
In the case where `k` is a successor, the bijection `e : Fin(k) ≃ X` gives us
the element `e(star) : X`.
Again we conclude that `X` is decidable.

Conversely, if `P` is decidable, then we can construct a counting of `P` by
case analysis on `d : P + ¬ P`.
If `P` holds, then it is contractible and hence equivalent to `Fin(1)`.
If `¬ P` holds, then `P` is equivalent to `Fin(0)`.

## Remark 16.1.6

We also note that any type `A` equipped with a counting `e : Fin(k) ≃ A` has
decidable equality.
This follows from Proposition `prp:has-decidable-equality-Fin`, where we showed
that `Fin(k)` has decidable equality, for any `k : ℕ`.

## Theorem 16.1.7

We make the following claims about countings:

1. Consider two types `A` and `B`.
   The following are equivalent:

   1. Both `A` and `B` come equipped with a counting.
   2. The coproduct `A + B` comes equipped with a counting.

2. Consider a type family `B` indexed by a type `A`.
   Consider the following three conditions:

   1. The type `A` comes equipped with a counting.
   2. The type `B(x)` comes equipped with a counting, for each `x : A`.
   3. The type `Σ(x : A) B(x)` comes equipped with a counting.

   If (a) holds, then (b) holds if and only if (c) holds.
   Furthermore, if both (b) and (c) hold and if `B` comes equipped with a
   section `f : Π(x : A) B(x)`, then (a) holds.

Consequently, if `P` is a subtype of a type `A` equipped with a counting, then
we have

```text
  count(Σ(x : A) P(x)) ↔ Π(x : A) is-decidable(P(x)).
```

## Proof

We will first prove the forward direction of (1).
Then we will prove both claims in (2), and we will prove the reverse direction
of claim (1) last.

For the forward direction of claim (1), suppose we have equivalences
`e : Fin(k) ≃ A` and `f : Fin(l) ≃ B`.
The equivalences `e` and `f` induce via Exercises `ex:coproduct_functor` and
`ex:laws-Fin` a composite equivalence

```text
  A + B ≃ Fin(k) + Fin(l) ≃ Fin(k + l),
```

from which we obtain an element of type `count(A + B)`.

Next, we will prove the forward direction in the first claim of (2), i.e., we
will prove that if `A` comes equipped with an equivalence `e : Fin(k) ≃ A`, and
if `B` is a family of types over `A` equipped with

```text
  f : Π(x : A) count(B(x)),
```

then the total space `Σ(x : A) B(x)` also has a counting.
The proof is by induction on `k`.
Note that in the base case, where `k = 0`, the type `Σ(x : A) B(x)` is empty,
so it has a counting.
For the inductive step, note that `Σ` distributes from the right over
coproducts.
This gives an equivalence

```text
  Σ(x : A) B(x)
    ≃ Σ(x : Fin(k + 1)) B(e(x))
    ≃ (Σ(x : Fin(k)) B(e(inl(x)))) + B(e(inr(star))).
```

The type `Σ(x : Fin(k)) B(e(inl(x)))` has a counting by the inductive
hypothesis, and the type `B(e(inr(star)))` has a counting by assumption.
Therefore, it follows that the total space `Σ(x : A) B(x)` has a counting.

Now we will prove the converse direction of the first claim in (2).
Suppose that `A` comes equipped with `e : Fin(k) ≃ A`, and that
`Σ(x : A) B(x)` comes equipped with `f : Fin(l) ≃ Σ(x : A) B(x)`.
By Example 16.1.5 it suffices to show that, for `a : A`, the type `B(a)` is a
decidable subtype of `Σ(x : A) B(x)`.
Consider the map

```text
  i : B(a) → Σ(x : A) B(x)
```

given by `b ↦ (a, b)`.
For `(x, y) : Σ(x : A) B(x)`, we have the equivalences

```text
  fib_i(x, y)
    ≃ Σ(b : B(a)) (a, b) = (x, y)
    ≃ Σ(b : B(a)) Σ(p : a = x) tr_B(p, b) = y
    ≃ Σ(p : a = x) fib(tr_B(p), y)
    ≃ a = x.
```

Here we used that `tr_B(p)` is an equivalence, and therefore has contractible
fibers.
Now note that the type `a = x` is a decidable proposition by Remark 16.1.6.

Next, we will prove the second claim in (2).
Suppose that `B` is a family over `A` that comes equipped with a section
`b : Π(x : A) B(x)`, and suppose that each `B(x)` has a counting, and that the
total space `Σ(x : A) B(x)` has a counting.
Then we have a map

```text
  g : A → Σ(x : A) B(x)
```

given by `a ↦ (a, b(a))`.
The fibers of `g` can be computed by the following equivalences:

```text
  fib_g(x, y)
    ≃ Σ(a : A) (a, b(a)) = (x, y)
    ≃ Σ(a : A) Σ(p : a = x) tr_B(p, b(a)) = y
    ≃ tr_B(p, b(x)) = y.
```

Note that the type `tr_B(p, b(x)) = y` is a decidable proposition by
Remark 16.1.6.
Now it follows by the forward direction of the first claim in (2) that `A` has
a counting.

It remains to prove the converse direction of (1).
Note that the forward direction of the first claim in (2) implies that
countings on a type `X` induce countings on any decidable subtype of `X`.
Note that both `A` and `B` are decidable subtypes of the coproduct `A + B`.
Any counting of `A + B` therefore induces countings of `A` and of `B`.

## Corollary 16.1.8

Consider two types `A` and `B`.
We make two claims:

1. If both `A` and `B` come equipped with a counting, then the product
   `A × B` has a counting.
2. If the product `A × B` comes equipped with a counting, then we have two
   functions

```text
  B → count(A)
  A → count(B).
```

## Proof

The first claim follows from condition (2a) in Theorem 16.1.7, and the second
claim follows from condition (2b) in Theorem 16.1.7.
