# Section 5.2 The groupoidal structure of types

```agda
module section-5-2-the-groupoidal-structure-of-types where

open import universe-levels
open import section-5-1-the-inductive-definition-of-identity-types
```

We show that identifications can be *concatenated* and *inverted*, which
corresponds to the transitivity and symmetry of the identity type.

## Definition 5.2.1

Let `A` be a type.
We define the **concatenation** operation

```text
  concat : Π(x, y, z : A) x = y → y = z → x = z.
```

We will write `p ∙ q` for `concat(p, q)`.

## Construction

We first construct a function

```text
  f(x) : Π(y : A) x = y → Π(z : A) y = z → x = z
```

for any `x : A`.
By the induction principle for identity types, it suffices to construct

```text
  f(x, x, refl) : Π(z : A) x = z → x = z.
```

Here we have the function `λ z. id_(x ＝ z)`.
The function `f(x)` we obtain via identity elimination is explicitly thus
defined as

```text
  f(x) ≔ path-ind_x(λ z. id) : Π(y : A) x = y → Π(z : A) y = z → x = z.
```

To finish the construction of `concat`, we use Exercise 2.4 to swap the order of
the third and fourth variable of `f`, i.e., we define

```text
  concat(p, q) ≔ f(x, y, p, z, q).
```

```agda
module _
  {l : Level} {A : Type l}
  where

  infixl 15 _∙_
  _∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  refl ∙ q = q

  concat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  concat p z q = p ∙ q
```

## Definition 5.2.2

Let `A` be a type.
We define the **inverse operation**

```text
  inv : Π(x, y : A) x = y → y = x.
```

Most of the time we will write `p⁻¹` for `inv(p)`.

## Construction

By the induction principle for identity types, it suffices to construct

```text
  inv (refl) :  x = x,
```

for any `x : A`.
Here we take `inv(refl) ≔ refl`.

```agda
module _
  {l : Level} {A : Type l}
  where

  inv : {x y : A} → x ＝ y → y ＝ x
  inv refl = refl
```

## Prelude to Definition 5.2.3

The next question is whether the concatenation and inverting operations on
identifications behave as expected.
More concretely:  is concatenation of identifications associative, does it
satisfy the unit laws, and is the inverse of an identification indeed a
two-sided inverse?

For example, in the case of associativity we are asking to compare the
identifications

```text
  (p ∙ q) ∙ r    and    p ∙ (q ∙ r)
```

for any `p : x = y`, `q : y = z`, and `r : z = w` in a type `A`.
The computation rules of the identity type are not strong enough to conclude
that `(p ∙ q) ∙ r` and `p ∙ (q ∙ r)` are judgmentally equal.
However, both `(p ∙ q) ∙ r` and `p ∙ (q ∙ r)` are elements of the same
type: they are identifications of type `x = w`.
Since the identity type is a type like any other, we can ask whether there is an
*identification*

```text
  (p ∙ q) ∙ r = p ∙ (q ∙ r).
```

This is a very useful idea: While it is often impossible to show that two
elements of the same type are judgmentally equal, it may be the case that those
two elements can be *identified*.
Indeed, we identify two elements by constructing an element of the identity
type, and we can use all the type theory at our disposal in order to construct
such an element.
In this way we can show, for example, that addition on the natural numbers or on
the integers is associative and satisfies the unit laws.
And indeed, here we will show that concatenation of identifications is
associative and satisfies the unit laws.

## Definition 5.2.3

Let `A` be a type and consider three consecutive identifications

```text
      p       q       r
  x ===== y ===== z ===== w
```

in `A`.
We define the **associator**

```text
  assoc(p, q, r) :  (p ∙ q) ∙ r = p ∙ (q ∙ r).
```

## Construction

By the induction principle for identity types it suffices to show that

```text
  Π(z : A) Π(q : x = z)
  Π(w : A) Π(r : z = w) (refl ∙ q) ∙ r = refl ∙ (q ∙ r).
```

Let `q : x = z` and `r : z = w`.
Note that by the computation rule of identity types we have a judgmental
equality `refl ∙ q ≐ q`.
Therefore we conclude that


```text
  (refl ∙ q) ∙ r ≐ q ∙ r.
```

Similarly we have a judgmental equality `refl ∙ (q ∙ r) ≐ q ∙ r`.
Thus we see that the left-hand side and the right-hand side in

```text
  (refl ∙ q) ∙ r = refl ∙ (q ∙ r)
```

are judgmentally equal, so we can simply define `assoc(refl, q, r) ≔ refl`.

```agda
module _
  {l : Level} {A : Type l}
  where

  assoc :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
  assoc refl q r = refl
```

## Definition 5.2.4

Let `A` be a type.
We define the left and right **unit law operations**, which assigns to each `p :
x = y` the identifications

```text
   left-unit(p) : refl ∙ p = p,
  right-unit(p) : p ∙ refl = p,
```

respectively.

## Construction

By identification elimination it suffices to construct

```text
   left-unit(refl) : refl ∙ refl =  refl,
  right-unit(refl) : refl ∙ refl =  refl.
```

In both cases we take `refl`.

```agda
  left-unit : {x y : A} {p : x ＝ y} → refl ∙ p ＝ p
  left-unit = refl

  right-unit : {x y : A} {p : x ＝ y} → p ∙ refl ＝ p
  right-unit {p = refl} = refl
```

## Definition 5.2.5

Let `A` be a type.
We define left and right **inverse law operations**

```text
   left-inv(p) : p⁻¹ ∙ p =  refl,
  right-inv(p) : p ∙ p⁻¹ =  refl.
```

## Construction

By identification elimination it suffices to construct

```text
   left-inv(refl) : refl⁻¹ ∙ refl = refl
  right-inv(refl) : refl ∙ refl⁻¹ = refl.
```

Using the computation rules we see that

```text
  refl⁻¹ ∙ refl ≐ refl ∙ refl ≐ refl,
```

so we define `left-inv(refl) ≔ refl`.
Similarly it follows from the computation rules that

```text
  refl ∙ refl⁻¹ ≐ refl⁻¹ ≐ refl,
```

so we again define `right-inv(refl) ≔ refl`.

```agda
module _
  {l : Level} {A : Type l}
  where

  left-inv : {x y : A} (p : x ＝ y) → inv p ∙ p ＝ refl
  left-inv refl = refl

  right-inv : {x y : A} (p : x ＝ y) → p ∙ inv p ＝ refl
  right-inv refl = refl
```

## Remark 5.2.6

We have seen that the associator, the unit laws, and the inverse laws, are all
proven by constructing an identification of identifications.
And indeed, there is nothing that would stop us from considering identifications
of those identifications of identifications.
We can go up as far as we like in the *tower of identity types*, which is
obtained by iteratively taking identity types.

The iterated identity types give types in homotopy type theory a very intricate
structure.
One important way of studying this structure is via the homotopy groups of
types, a subject that we will gradually be working towards.

## Agda-unimath sources

- The concatenation operation, inverse operation, and all higher identifications are defined in `foundation-core.identity-types`