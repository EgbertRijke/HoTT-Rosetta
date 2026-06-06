# Section 10.2 Singleton induction

```agda
module section-10-2-singleton-induction where
```

Contractible types are singletons up to homotopy.
Indeed, every element of a contractible type can be identified with the center
of contraction.
Therefore we can prove an induction principle for contractible types that is
similar to the induction principle of the unit type.

## Definition 10.2.1

Suppose `A` comes equipped with an element `a : A`.
Then we say that `A` satisfies **singleton induction** if for every type family
`B` over `A`, the map

```text
  ev-pt : (Π(x : A) B(x)) → B(a)
```

defined by `ev-pt(f) := f(a)` has a section.
In other words, if `A` satisfies singleton induction we have a function and a
homotopy

```text
  sing-ind_a  : B(a) → Π(x : A) B(x)
  sing-comp_a : ev-pt ∘ sing-ind_a ~ id
```

for any type family `B` over `A`.

## Example 10.2.2

Note that the singleton induction principle is almost the same as the induction
principle for the unit type, the difference being that the computation rule in
the singleton induction for `A` is stated using an *identification* rather than
as a judgmental equality.
The unit type `𝟙` comes equipped with a function

```text
  ind-𝟙 : B(⋆) → Π(x : 𝟙) B(x)
```

for every type family `B` over `𝟙`, satisfying the judgmental equality
`ind-𝟙(b, ⋆) ≐ b` for every `b : B(⋆)` by the computation rule.
Therefore, we obtain the homotopy

```text
  λ b. refl(b) : ev-pt ∘ ind-𝟙 ~ id,
```

and we conclude that the unit type satisfies singleton induction.

## Theorem 10.2.3

Let `A` be a type.
The following are equivalent:

1. The type `A` is contractible.
2. The type `A` comes equipped with an element `a : A`, and satisfies singleton
induction.

## Proof

Suppose `A` is contractible with center of contraction `a` and contraction `C`.
First we observe that, without loss of generality, we may assume that `C` comes
equipped with an identification `p : C(a) = refl(a)`.
To see this, note that we can always define a new contraction `C'` by

```text
  C'(x) := C(a)⁻¹ ∙ C(x),
```

which satisfies the requirement by the left inverse law.

To show that `A` satisfies singleton induction let `B` be a type family over
`A`, and suppose we have `b : B(a)`.
Our goal is to define

```text
  ind-sing_a(b) : Π(x : A) B(x).
```

Let `x : A`.
Since we have an identification `C(x) : a = x`, and an element `b` in `B(a)`, we
may transport `b` along the path `C(x)` to obtain

```text
  ind-sing_a(b, x) := tr_B(C(x), b) : B(x).
```

Therefore, the function `ind-sing_a(b)` is defined to be the dependent function
`λ x. tr_B(C(x), b)`.
Now we have to show that `ind-sing_a(b, a) = b`.
Then we have the chain of identifications

```text
  tr_B(C(a), b) = tr_B(refl(a), b) = b.
```

This shows that the computation rule is satisfied, which completes the proof
that `A` satisfies singleton induction.

For the converse, suppose that `a : A` and that `A` satisfies singleton
induction.
Our goal is to show that `A` is contractible.
For the center of contraction we take the element `a : A`.
By singleton induction applied to `B(x) := a = x` we have the map

```text
  ind-sing_a : a = a → Π(x : A) a = x.
```

Therefore `ind-sing_a(refl(a))` is a contraction.
