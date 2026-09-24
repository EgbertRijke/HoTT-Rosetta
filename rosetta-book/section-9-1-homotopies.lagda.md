# Section 9.1 Homotopies

```agda
module section-9-1-homotopies where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import exercise-4-2-boolean-operations
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import exercise-5-2-inverse-concatenation-maps
```

In type theory we are very limited in constructing identifications of functions.
The following example illustrates a case where type theory provides no rules to construct an identification between two maps, even though they are pointwise equal.

## Remark 9.1.1

Consider the negation function `neg-bool : bool→bool` on the booleans, which was defined in Exercise 4.2.
Type theory does not provide any means to show that

```text
  neg-bool ∘ neg-bool = id.
```

The best we can do is to construct an identification

```text
  neg-neg-bool(b) : neg-bool(neg-bool(b)) = b
```

for any `b : bool`.
Indeed, `neg-neg-bool` is defined using the induction principle of `bool`, by

```text
   neg-neg-bool(true) ≔ refl,
  neg-neg-bool(false) ≔ refl.
```

Therefore we see that, while we cannot identify `neg-bool ∘ neg-bool` with `id`, we can define a *pointwise identification* between the values of `neg-bool ∘ neg-bool` and `id`.

```agda
is-involution-neg-bool : (b : bool) → neg-bool (neg-bool b) ＝ b
is-involution-neg-bool true = refl
is-involution-neg-bool false = refl
```

The observations in Remark 9.1.1 are an instance of a general phenomenon in type theory: It is often much easier to construct a *pointwise identification* between the values of two maps, than it is to construct an identification between those two maps.
In fact, the prevalent notion of sameness of maps is the notion of pointwise identification.
Since they are so important, we will give them a name and call them *homotopies*.

## Definition 9.1.2

Let `f, g : Π(x : A) B(x)` be two dependent functions.
The type of **homotopies** from `f` to `g` is defined as the type of pointwise identifications, i.e., we define

```text
  f ~ g ≔ Π(x : A) f(x) = g(x).
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _~_
  _~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f ~ g = (x : A) → f x ＝ g x
```

## Example 9.1.3

By Remark 9.1.1 we have a homotopy

```text
  neg-neg-bool : neg-bool ∘ neg-bool ~ id.
```

## Remark 9.1.4

We will use homotopies, for example, to express the commutativity of diagrams.
For example, we say that a triangle

```text
      h
  A ----> B
   \     /
  f \   / g
     ∨ ∨
      X
```

**commutes** if it comes equipped with a homotopy `H : f ~ g ∘ h`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle-maps :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps left right top = left ~ right ∘ top

  coherence-triangle-maps' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps' left right top = right ∘ top ~ left
```

Similarly, we say that a square

```text
         g
    A ------> A'
    |         |
  f |         | f'
    ∨         ∨
    B ------> B'
         h
```

commutes if it comes equipped with a homotopy `h ∘ f ~ f' ∘ g`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X)
  where

  coherence-square-maps : UU (l3 ⊔ l4)
  coherence-square-maps = bottom ∘ left ~ right ∘ top

  coherence-square-maps' : UU (l3 ⊔ l4)
  coherence-square-maps' = right ∘ top ~ bottom ∘ left
```

Note that the type of homotopies `f ~ g` is defined for dependent functions, and moreover the type of homotopies is itself a dependent function type.
The definition of homotopies is therefore set up in such a way that we may also consider homotopies *between* homotopies, and even further homotopies between those higher homotopies.
More concretely, if `H, K : f ~ g` are two homotopies, then the type of homotopies `H ~ K` between them is just the type

```text
  Π(x : A) H(x) = K(x).
```

Since homotopies are pointwise identifications, we can use the groupoidal structure of identity types to also define the groupoidal structure of homotopies.
In this case, however, we state the groupoid laws as *homotopies* and *homotopies between homotopies* rather than as identifications.

## Definition 9.1.5

For any type family `B` over `A` we define the operations on homotopies

```text
    refl-htpy : Π(f : Π(x : A) B(x)) f ~ f,
     inv-htpy : Π(f, g : Π(x : A) B(x)) (f ~ g) → (g ~ f),
  concat-htpy : Π(f, g, h : Π(x : A) B(x)) (f ~ g) → ((g ~ h) → (f ~ h)),
```

pointwise by

```text
      refl-htpy(f) ≔ λ x. refl,
       inv-htpy(H) ≔ λ x. H(x)⁻¹,
  concat-htpy(H,K) ≔ λ x. H(x) ∙ K(x).
```

We will often write `H⁻¹` for `inv-htpy(H)`, and `H ∙ K` for `concat-htpy(H,K)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-htpy : {f : (x : A) → B x} → f ~ f
  refl-htpy x = refl

  refl-htpy' : (f : (x : A) → B x) → f ~ f
  refl-htpy' f = refl-htpy

  inv-htpy : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv-htpy H x = inv (H x)

  infixl 15 _∙h_

  _∙h_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  (H ∙h K) x = (H x) ∙ (K x)

  concat-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
  concat-htpy H h K x = concat (H x) (h x) (K x)

  concat-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ g → f ~ h
  concat-htpy' f K H = H ∙h K

  concat-inv-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → f ~ h → g ~ h
  concat-inv-htpy = concat-htpy ∘ inv-htpy

  concat-inv-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ h → f ~ g
  concat-inv-htpy' f K = concat-htpy' f (inv-htpy K)
```

## Proposition 9.1.6

Homotopies satisfy the groupoid laws:

1. Concatenation of homotopies is associative up to homotopy, i.e., there is a homotopy

   ```text
     assoc-htpy(H,K,L) : (H ∙ K) ∙ L~H ∙ (K ∙ L)
   ```

   for any homotopies `H : f ~ g`, `K : g ~ h` and `L : h ~ i`.

2. Homotopies satisfy the left and right unit laws up to homotopy, i.e., there are homotopies

   ```text
      left-unit-htpy(H) : refl-htpy(f) ∙ H ~ H
     right-unit-htpy(H) : H ∙ refl-htpy(g) ~ H
   ```

   for any homotopy `H`.

3. Homotopies satisfy the left and right inverse laws up to homotopy, i.e., there are homotopies

   ```text
      left-inv-htpy(H) : H⁻¹ ∙ H ~ refl-htpy(g)
     right-inv-htpy(H) : H ∙ H⁻¹ ~ refl-htpy(f)
   ```

   for any homotopy `H`.

### Proof

The homotopy `assoc-htpy(H,K,L)` is defined pointwise by

```text
  assoc-htpy(H,K,L,x) ≔ assoc(H(x),K(x),L(x)).
```

The other homotopies are similarly defined pointwise. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k)
  where

  assoc-htpy : (H ∙h K) ∙h L ~ H ∙h (K ∙h L)
  assoc-htpy x = assoc (H x) (K x) (L x)

  inv-htpy-assoc-htpy : H ∙h (K ∙h L) ~ (H ∙h K) ∙h L
  inv-htpy-assoc-htpy = inv-htpy assoc-htpy

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} {H : f ~ g}
  where

  left-unit-htpy : refl-htpy ∙h H ~ H
  left-unit-htpy x = left-unit

  inv-htpy-left-unit-htpy : H ~ refl-htpy ∙h H
  inv-htpy-left-unit-htpy = inv-htpy left-unit-htpy

  right-unit-htpy : H ∙h refl-htpy ~ H
  right-unit-htpy x = right-unit

  inv-htpy-right-unit-htpy : H ~ H ∙h refl-htpy
  inv-htpy-right-unit-htpy = inv-htpy right-unit-htpy

  left-inv-htpy : inv-htpy H ∙h H ~ refl-htpy
  left-inv-htpy = left-inv ∘ H

  inv-htpy-left-inv-htpy : refl-htpy ~ inv-htpy H ∙h H
  inv-htpy-left-inv-htpy = inv-htpy left-inv-htpy

  right-inv-htpy : H ∙h inv-htpy H ~ refl-htpy
  right-inv-htpy = right-inv ∘ H

  inv-htpy-right-inv-htpy : refl-htpy ~ H ∙h inv-htpy H
  inv-htpy-right-inv-htpy = inv-htpy right-inv-htpy
```

Apart from the groupoid operations and their laws, we will occasionally need *whiskering* operations.
Whiskering operations are operations that allow us to compose homotopies with functions.
There are two situations where we want to do this:

```text
     ---->                                   ---->
 [A]   ⇓   [B] ----> [C]       [A] ----> [B]   ⇓   [C]
     ---->                                   ---->
```

## Definition 9.1.7

We define the following **whiskering** operations on homotopies:

1. Suppose `H : f ~ g` for two functions `f, g : A → B`, and let `h : B → C`.
   We define

   ```text
     h · H ≔ λ x. ap_{h}(H(x)) : h ∘ f ~ h ∘ g.
   ```

2. Suppose `f : A → B` and `H : g ~ h` for two functions `g, h : B → C`.
   We define

   ```text
     H · f ≔ λ x. H(f(x)) : g ∘ f ~ h ∘ f.
   ```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  left-whisker-comp :
    (h : {x : A} → B x → C x)
    {f g : (x : A) → B x} → f ~ g → h ∘ f ~ h ∘ g
  left-whisker-comp h H x = ap h (H x)

  infixr 17 _·l_

  _·l_ = left-whisker-comp

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  right-whisker-comp :
    {g h : {x : A} (y : B x) → C x y}
    (H : {x : A} → g {x} ~ h {x})
    (f : (x : A) → B x) → g ∘ f ~ h ∘ f
  right-whisker-comp H f x = H (f x)

  infixl 16 _·r_

  _·r_ = right-whisker-comp
```

## Supplement

### Transposition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h) (M : H ∙h K ~ L)
  where

  left-transpose-htpy-concat : K ~ inv-htpy H ∙h L
  left-transpose-htpy-concat x =
    left-transpose-eq-concat (H x) (K x) (L x) (M x)

  inv-htpy-left-transpose-htpy-concat : inv-htpy H ∙h L ~ K
  inv-htpy-left-transpose-htpy-concat = inv-htpy left-transpose-htpy-concat

  right-transpose-htpy-concat : H ~ L ∙h inv-htpy K
  right-transpose-htpy-concat x =
    right-transpose-eq-concat (H x) (K x) (L x) (M x)

  inv-htpy-right-transpose-htpy-concat : L ∙h inv-htpy K ~ H
  inv-htpy-right-transpose-htpy-concat = inv-htpy right-transpose-htpy-concat
```

### Left whiskering of homotopies with respect to concatenation

Left whiskering of homotopies with respect to concatenation is an operation

```text
  (H : f ~ g) {I J : g ~ h} → I ~ J → H ∙h I ~ H ∙h J.
```

We implement the left whiskering operation of homotopies with respect to
concatenation as an instance of a general left whiskering operation.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-whisker-concat-htpy :
    {f g h : (x : A) → B x} (H : f ~ g) {K L : g ~ h} → K ~ L → H ∙h K ~ H ∙h L
  left-whisker-concat-htpy H K x = left-whisker-concat (H x) (K x)

  left-unwhisker-concat-htpy :
    {f g h : (x : A) → B x} (H : f ~ g) {I J : g ~ h} → H ∙h I ~ H ∙h J → I ~ J
  left-unwhisker-concat-htpy H K x = left-unwhisker-concat (H x) (K x)
```

### Right whiskering of homotopies with respect to concatenation

Right whiskering of homotopies with respect to concatenation is an operation

```text
  {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J.
```

We implement the right whiskering operation of homotopies with respect to
concatenation as an instance of a general right whiskering operation.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-whisker-concat-htpy :
    {f g h : (x : A) → B x} {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J
  right-whisker-concat-htpy J K x = right-whisker-concat (J x) (K x)

  right-unwhisker-concat-htpy :
    {f g h : (x : A) → B x} {H I : f ~ g} (J : g ~ h) → H ∙h J ~ I ∙h J → H ~ I
  right-unwhisker-concat-htpy H K x = right-unwhisker-concat (H x) (K x)
```

### Whiskering preserves function composition

In other words, whiskering is an action of functions on homotopies.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : A → UU l3} {D : A → UU l4}
  where

  inv-preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    (k ∘ h) ·l H ~ k ·l (h ·l H)
  inv-preserves-comp-left-whisker-comp k h H x = ap-comp k h (H x)

  preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    k ·l (h ·l H) ~ (k ∘ h) ·l H
  preserves-comp-left-whisker-comp k h H =
    inv-htpy (inv-preserves-comp-left-whisker-comp k h H)

module _
  { l1 l2 l3 l4 : Level}
  { A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  { D : (x : A) (y : B x) (z : C x y) → UU l4}
  { f g : {x : A} {y : B x} (z : C x y) → D x y z}
  ( h : {x : A} (y : B x) → C x y) (k : (x : A) → B x)
  ( H : {x : A} {y : B x} → f {x} {y} ~ g {x} {y})
  where

  preserves-comp-right-whisker-comp : (H ·r h) ·r k ~ H ·r (h ∘ k)
  preserves-comp-right-whisker-comp = refl-htpy
```

### Left whiskering higher homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x}
  where

  left-whisker-comp² :
    (h : {x : A} → B x → C x) {H H' : f ~ g} (α : H ~ H') → h ·l H ~ h ·l H'
  left-whisker-comp² h α = ap h ·l α
```

### Right whiskering higher homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {f g : {x : A} (y : B x) → C x y} {H H' : {x : A} → f {x} ~ g {x}}
  where

  right-whisker-comp² :
    (α : {x : A} → H {x} ~ H' {x}) (h : (x : A) → B x) → H ·r h ~ H' ·r h
  right-whisker-comp² α h = α ·r h
```

### Coherences of commuting triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  where

  coherence-triangle-homotopies :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies left right top = left ~ top ∙h right

  coherence-triangle-homotopies' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies' left right top = top ∙h right ~ left
```

### Homotopies preserve the laws of the action on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) {K K' : g ~ h} → K ~ K' → H ∙h K ~ H ∙h K'
  ap-concat-htpy H L x = ap (concat (H x) (h x)) (L x)

  ap-concat-htpy' :
    {H H' : f ~ g} (K : g ~ h) → H ~ H' → H ∙h K ~ H' ∙h K
  ap-concat-htpy' K L x =
    ap (concat' (f x) (K x)) (L x)

  ap-binary-concat-htpy :
    {H H' : f ~ g} {K K' : g ~ h} → H ~ H' → K ~ K' → H ∙h K ~ H' ∙h K'
  ap-binary-concat-htpy {H} {H'} {K} {K'} HH KK =
    ap-concat-htpy H KK ∙h ap-concat-htpy' K' HH

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy : H ~ H' → inv-htpy H ~ inv-htpy H'
  ap-inv-htpy K x = ap inv (K x)
```
