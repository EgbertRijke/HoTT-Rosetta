# Section 8.6 Boolean reflection

```agda
module section-8-6-boolean-reflection where
```

We have shown that the type `is-prime(n)` is decidable for every `n`.
In other words, there is an element `d(n) : is-decidable(is-prime(n))` for every
`n`.
In principle, we can therefore check whether any *specific* natural number `n`
is prime by inspecting the element `d(n)`: if it is of the form `inl(x)` for
some `x : is-prime(n)`, then `n` is prime; if it is of the form `inr(f)` for
some `f : ¬ is-prime(n)`, then `n` is not prime.
In other words, we evaluate the element `d(n)` using the computation rules of
type theory, and then we see whether `n` is prime or not.

Computers can perform such evaluations, but it is often unfeasible to carry out
such evaluations by hand.
Moreover, even for computers the task of evaluating a proof term like
`is-decidable-is-prime(n)` may quickly get out of hand.
With the formalization of the material in this book, the proof assistant Agda
returns a proof term of 430 lines of code when we simply ask it to evaluate the
term `is-decidable-is-prime(7)`, and it returned a proof term of 69373 lines of
code when we asked it to evaluate the term `is-decidable-is-prime(37)`.
There is a much better way to do this: *boolean reflection*.

## Definition 8.6.1

For any type `A` we define the map

```text
  booleanization : is-decidable(A) → bool
```

by

```text
  booleanization(inl(a)) := true
  booleanization(inr(f)) := false.
```

## Theorem 8.6.2

For any type `A` and any decision `d : is-decidable(A)`, there is a map

```text
  boolean-reflection : (booleanization(d) = true) → A
```

such that `boolean-reflection(inl(a)) ≐ a`.

## Proof

First, recall that by Exercise 6.2 there is a map `γ : (false = true) → ∅`.
We use this to construct `boolean-reflection` by pattern matching as follows:

```text
  boolean-reflection(inl(a), p) := a
  boolean-reflection(inr(f), p) := ex-falso(γ(p)).
```

## Remark 8.6.3

Since the number 37 is a prime, it follows that the booleanization of the term

```text
  d(37) : is-decidable(is-prime(37))
```

has the value `booleanization(d(37)) ≐ true`.
By boolean reflection it therefore follows that

```text
  is-prime-thirty-seven :=
    boolean-reflection(d(37), refl) : is-prime(37).        (*)
```

The term in `is-prime-thirty-seven` does not, however, contain any explicit
information as to why the number 37 is prime.
The reason that it type checks is simply that `d(37)` is judgmentally equal to
some term of the form `inl(t) : is-decidable(is-prime(37))` and therefore it
follows that `refl` is an identification of type

```text
  booleanization(d(37)) = true.
```

To see that `is-prime-thirty-seven` is indeed an element of type `is-prime(37)`
therefore requires us to evaluate the term `d(37)`.
This is not doable by hand.
Computer proof assistants, however, are capable of performing this task.
In a proof assistant, we may therefore use boolean reflection to offload the
task of evaluating the decision algorithm of a decidable type to the computer.
This technique has been essential in the formalization of the Feit-Thompson
theorem in Coq.
The book *Mathematical Components* contains more information about using boolean
reflection effectively in formalized mathematics.

Do not, however, "solve" your homework problems with boolean reflection.
If your teaching assistant cannot evaluate your solution, they will conclude
that you haven't demonstrated your clear understanding of the problem.
