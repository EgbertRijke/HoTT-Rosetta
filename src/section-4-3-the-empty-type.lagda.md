# Section 4.3 The empty type

```agda
module section-4-3-the-empty-type where
```

The empty type is a degenerate example of an inductive type.
It does *not* come equipped with any constructors, and therefore there are also no computation rules.
The induction principle merely asserts that any type family has a section.
In other words: if we assume the empty type has a term, then we can prove anything.

### Definition 4.3.1

We define the **empty type** to be a type `∅` satisfying the induction principle that for any family of types `P(x)` indexed by `x : ∅`, there is a term

```text
  ind_∅ : Π{x : ∅} P(x).
```

It is again a special case of the induction principle that we have a function

```text
  ex-falso ≔ ind_∅ : ∅ → A
```

for any type `A`.
Indeed, to obtain this function one first weakens `A` to obtain the constant family over `∅` with value `A`, and then the induction principle gives the desired function.
The function `ex-falso` can be used to draw any conclusion after deriving a contradiction, because *ex falso quodlibet*.

We can also use the empty type to define the negation operation on types.

### Definition 4.3.2

For any type `A` we define **negation** of `A` by

```text
  ¬ A ≔ A → ∅.
```

We also say that a type `A` **is empty** if it comes equipped with an element of type `¬ A`.
Therefore, we also define

```text
  is-empty(A) ≔ A → ∅.
```

### Remark 4.3.3

Since `¬ A` is the type of functions from `A` to `∅`, a proof of `¬ A` is given by assuming that `A` holds, and then constructing an element of the empty type.
In other words, we prove `¬ A` by assuming `A` and deriving a contradiction.
This proof technique is called **proof of negation**.

Proofs of negation should not be confused with proofs by contradiction.
Even though a proof of negation involves deriving a contradiction, in logic a **proof by contradiction** of a proposition `P` is an argument where we conclude that `P` holds after showing that `¬ P` implies a contradiction.
In other words, a proof by contradiction uses the logical step `¬¬ P ⇒ P`, which is also called **double negation elimination**.

In type theory, however, note that the type `¬¬ A` is the type of functions
  
```text
  (A → ∅) → ∅.
```

This type is quite different from the type `A` itself, and with the given rules of type theory it is not possible to construct a function `¬¬ A → A` unless more is known about the type `A`.
In other words, before one can prove by contradiction that there is an element in `A`, one has to construct a function `¬¬ A → A`, and it depends on the specific type `A` whether this is possible at all.
In \cref{ex:dne-is-decidable} we will see a situation where we can indeed construct a function `¬¬ A → A`.
In practice, however, we will rarely use double negation elimination.

### Proposition 4.3.4

In the following proposition we illustrate how to work with the type theoretic definition of negation.

For any two types `P` and `Q`, there is a function
  
```text
  (P → Q) → (¬ Q → ¬ P).
```

#### Proof

The desired function is defined by `λ`-abstraction, so we begin by assuming that we have a function `f : P → Q`.
Then we have to construct a function `¬ Q → ¬ P`, which is again constructed by `λ`-abstraction.
We assume that we have `q̃ : ¬ Q`.
By our definition of `¬ Q` we see that `q̃` is a function `Q → ∅`.
Now we have to construct a term of type `¬ P`, which is the type of functions `P → ∅`.
We apply `λ`-abstraction once more, so we assume `p : P`.
Now we have

```text
  f : P → Q
  q̃ : Q → ∅
  p : P,
```

and our goal is to construct a term of the empty type.

Since we have `f : P → Q` and `p : P`, we obtain `f(p) : Q`.
Moreover, we have `q̃ : Q → ∅`, so we obtain `q̃(f(p)) : ∅`.
This completes the proof.
The function we have constructed is
  
```text
  λ f. λ q̃. λ p. q̃(f(p)) : (P → Q) → (¬ Q → ¬ P). □
```

We leave it to the reader to construct the corresponding natural deduction tree, that formally constructs a function

```text
  (P → Q) → (¬ Q → ¬ P).
```
