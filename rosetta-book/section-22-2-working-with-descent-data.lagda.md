# Section 22.2 Working with descent data

```agda
module section-22-2-working-with-descent-data where
```

The equivalence

```text
(S¹ → 𝒰) ≃ Σ(X : 𝒰) X ≃ X
```

yields that for any type family `A` over the circle the type of descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy `H` witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes is contractible.
In the remainder of this section we study arbitrary type families over the circle equipped with such descent data, which will put us in a good position to prove things about the universal cover of the circle.

## Proposition 22.2.1

Consider a type family `A` over the circle and consider descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Furthermore, consider two elements `x,y : X`.
Then we have an equivalence

```text
ᾱ : (e(x) = y) ≃ (tr_{A}(loop,α(x)) = α(y)).
```

### Proof

_Proof._ Note that the commutativity of the square implies that

```text
tr_A(loop,α(x)) = α(e(x)).
```

By Theorem 11.2.2 it therefore suffices to prove that the total space

```text
Σ(y : X) tr_A(loop,α(x)) = α(y)
```

is contractible.
This type is equivalent to `fib(α, tr_A(loop,α(x)))`, which is contractible because `α` is an equivalence. ◻

In the following proposition we show that sections of a type family `A` equipped with descent data `(X,e)` are equivalently described as fixed points for `e : X ≃ X`.

## Proposition 22.2.2

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α:X≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Then there is a commuting square

```text
  [Π(t:S¹) A(t)]----> [Σ(x:X) e(x)=x]
         |                   |
ev_base  |                   | pr1
         V                   V
     [A(base)] --α^{-1}-->  [X]
```

in which the top map is an equivalence.

### Proof

_Proof._ By the dependent universal property of the circle we have an equivalence

```text
(Π(t : S¹) A(t)) ≃ Σ(x:A(base)) tr_A(loop,x) = x.
```

This equivalence fits in a commuting triangle

```text
                    [Π(t : S¹) A(t)]
                   /                \
                  /                  \ dgen_{S¹}
                 V                    V
[Σ(x : X) e(x) = x] --{tot_α(ᾱ)}--> [Σ(x : A(base)) tr_A(loop,x) = x]
```

where the map on the left is given by `s ↦ (α^{-1}(s(base)),ᾱ^{-1}(apd_{s}(loop)))`.
The bottom map and the map on the right are equivalences, so it follows by the 3-for-2 property of equivalences that the map on the left is an equivalence. ◻

The following corollary can be used to compare type families over the circle.
In particular, we will use it to compare the identity type of the circle with the universal cover.

## Corollary 22.2.3

Consider two type families `A` and `B` over the circle equipped with descent data `(X,e)` and `(Y,f)`, equivalences `α : X ≃ A(base)` and `β : Y ≃ B(base)`, and homotopies `H` and `K` witnessing that the squares

```text
 [X] --α-->[A(base)]         [Y] --β-->[B(base)]
  |           |               |           |
e |           | tr_A(loop)  f |           | tr_B(loop)
  V           V               V           V
 [X] --α-->[A(base)]         [Y] --β-->[B(base)]
```

commute, respectively.
Then there is a commuting square

```text
[(Π(t:S¹) A(t)→ B(t))]  ----------> [Σ(h:X→ Y) h∘ e~ f∘ h]
           |                                 |
   ev_base |                                 | pr1
           V                                 V
  [(A(base)→ B(base))] --h↦β^{-1}∘h∘α--> [(X→ Y)]
```

in which the top map is an equivalence.

### Proof

_Proof._ The claim follows once we observe that `(Y^X,λ h. f∘ h∘ e^{-1})` is descent data for the family of types `(A(t) → B(t))` indexed by `t : S¹`.
Indeed, we have the equivalence `h ↦ β ∘ h ∘ α^{-1} : Y^X ≃ B(base)^{A(base)}` for which the square

```text
            [Y^X]--h↦β∘h∘α^{-1}-->[B(base)^{A(base)}]
              |                           |
h↦f∘h∘e^{-1}  |                           | tr_{t ↦ A(t) → B(t)}(loop)
              V                           V
            [Y^X]--h↦β∘h∘α^{-1}-->[B(base)^{A(base)}]
```

commutes. ◻

## Corollary 22.2.4

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Then there is a commuting square

_Square-shaped diagram (automatic draft)._

```text
[(Π(t:S¹) E_(S¹)(t)→ A(t))]-------------> [Σ(h:ℤ → X) h∘ succ-ℤ ~ e∘ h]
              |                                          |
      ev_base |                                          | pr1
              V                                          V
  [(E_(S¹)(base)→ A(base))] --h↦α^{-1}∘h∘(k↦k_{E})--> [(ℤ → X)]
```

in which the top map is an equivalence.

In other words, a family of maps `E_(S¹)(t) → A(t)` indexed by `t : S¹` is equivalently described as a map `h : ℤ → X` for which the square

```text
      [ℤ] --h--> [X]
       |          |
succ-ℤ |          | e
       V          V
      [ℤ] --h--> [X]
```

commutes.
It is now time to prove the universal property of the integers.
