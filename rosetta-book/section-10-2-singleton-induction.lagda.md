# Section 10.2 Singleton induction

```agda
module section-10-2-singleton-induction where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
```

<!-- rosetta-item: section-10.2 -->

Contractible types are singletons up to homotopy.
Indeed, every element of a contractible type can be identified with the center of contraction.
Therefore we can prove an induction principle for contractible types that is similar to the induction principle of the unit type.

## Definition 10.2.1

<!-- rosetta-item: definition-10.2.1; latex-label: defn:singleton-induction -->

Suppose `A` comes equipped with an element `a:A`.
Then we say that `A` satisfies **singleton induction** if for every type family `B` over `A`, the map
```text
ev-pt:(Π(x:A) B(x))→ B(a)
```
defined by `ev-pt(f)≔ f(a)` has a section.
In other words, if `A` satisfies singleton induction we have a function and a homotopy
```text
\singind_{a} : B(a)→ Π(x:A) B(x)
\singcomp_{a} : ev-pt∘ \singind_{a} ~ id
```
for any type family `B` over `A`.

<!-- rosetta-agda-block: definition-10.2.1-singleton-induction -->

```agda
is-singleton :
  (l1 : Level) {l2 : Level} (A : Type l2) → A → Type (lsuc l1 ⊔ l2)
is-singleton l A a = (B : A → Type l) → section (ev-point a {B})

ind-is-singleton :
  {l1 l2 : Level} {A : Type l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → Type l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

compute-ind-is-singleton :
  {l1 l2 : Level} {A : Type l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → Type l2) → (ev-point a {B} ∘ ind-is-singleton a H B) ~ id
compute-ind-is-singleton a H B = pr2 (H B)
```
<!-- rosetta-item-end: definition-10.2.1 -->

## Example 10.2.2

<!-- rosetta-item: example-10.2.2 -->

Note that the singleton induction principle is almost the same as the induction principle for the unit type, the difference being that the ‘computation rule’ in the singleton induction for `A` is stated using an *identification* rather than as a judgmental equality.
The unit type `unit` comes equipped with a function
```text
ind-unit:B(⋆)→ Π(x:unit) B(x)
```
for every type family `B` over `unit`, satisfying the judgmental equality `ind-unit(b,⋆)≐ b` for every `b:B(⋆)` by the computation rule.
Therefore, we obtain the homotopy
```text
λ b. refl:ev-pt∘ind-unit ~id,
```
and we conclude that the unit type satisfies singleton induction.

<!-- rosetta-item-end: example-10.2.2 -->

## Theorem 10.2.3

<!-- rosetta-item: theorem-10.2.3; latex-label: thm:contractible -->

Let `A` be a type.
The following are equivalent:

1.  The type `A` is contractible.

2.  The type `A` comes equipped with an element `a:A`, and satisfies singleton induction.

### Proof

<!-- rosetta-item: subheading-10.2-proof -->

*Proof.* Suppose `A` is contractible with center of contraction `a` and contraction `C`.
First we observe that, without loss of generality, we may assume that `C` comes equipped with an identification `p:C(a)=refl`.
To see this, note that we can always define a new contraction `C'` by
```text
C'(x)≔C(a)^{-1} ∙ C(x),
```
which satisfies the requirement by the left inverse law, constructed in Definition 5.2.5.

To show that `A` satisfies singleton induction let `B` be a type family over `A`, and suppose we have `b:B(a)`.
Our goal is to define
```text
ind-sing_a(b):Π(x:A) B(x).
```
Let `x:A`.
Since we have an identification `C(x):a=x`, and an element `b` in `B(a)`, we may transport `b` along the path `C(x)` to obtain
```text
ind-sing_a(b,x)≔ tr_B(C(x),b):B(x).
```
Therefore, the function `ind-sing_a(b)` is defined to be the dependent function `λ x. tr_B(C(x),b)`.
Now we have to show that `ind-sing_a(b,a)=b`.
Then we have the identifications
<!-- rosetta-diagram: 110350baa917; review: pending -->

*Linear diagram (automatic draft).*

```text
[tr_B(C(a),b)]---->[[4em] tr_B(refl,b)]----> [b]

Arrows:
- tr_B(C(a),b) --ap_{λ \omega. tr_B(\omega,b)}(p)--> [4em] tr_B(refl,b)
- [4em] tr_B(refl,b) --refl--> b
```
This shows that the computation rule is satisfied, which completes the proof that `A` satisfies singleton induction.

For the converse, suppose that `a:A` and that `A` satisfies singleton induction.
Our goal is to show that `A` is contractible.
For the center of contraction we take the element `a:A`.
By singleton induction applied to `B(x)≔ a=x` we have the map
```text
ind-sing_{a} : a=a → Π(x:A) a=x.
```
Therefore `ind-sing_{a}(refl)` is a contraction. ◻

<!-- rosetta-agda-block: theorem-10.2.3-contractible-singleton-induction -->

```agda
ind-singleton :
  {l1 l2 : Level} {A : Type l1} (a : A) (is-contr-A : is-contr A)
  (B : A → Type l2) → B a → (x : A) → B x
ind-singleton a is-contr-A B b x =
  tr B (inv (contraction is-contr-A a) ∙ contraction is-contr-A x) b

compute-ind-singleton :
  {l1 l2 : Level} {A : Type l1}
  (a : A) (is-contr-A : is-contr A) (B : A → Type l2) →
  (ev-point a {B} ∘ ind-singleton a is-contr-A B) ~ id
compute-ind-singleton a is-contr-A B b =
  ap (λ p → tr B p b) (left-inv (contraction is-contr-A a))
```

<!-- rosetta-agda-block: theorem-10.2.3-singleton-induction-iff-contractible -->

```agda
is-singleton-is-contr :
  {l1 l2 : Level} {A : Type l1} (a : A) → is-contr A → is-singleton l2 A a
pr1 (is-singleton-is-contr a is-contr-A B) =
  ind-singleton a is-contr-A B
pr2 (is-singleton-is-contr a is-contr-A B) =
  compute-ind-singleton a is-contr-A B

abstract
  is-contr-ind-singleton :
    {l1 : Level} (A : Type l1) (a : A) →
    ({l2 : Level} (B : A → Type l2) → B a → (x : A) → B x) → is-contr A
  pr1 (is-contr-ind-singleton A a S) = a
  pr2 (is-contr-ind-singleton A a S) = S (λ x → a ＝ x) refl

abstract
  is-contr-is-singleton :
    {l1 : Level} (A : Type l1) (a : A) →
    ({l2 : Level} → is-singleton l2 A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (pr1 ∘ S)
```
<!-- rosetta-item-end: theorem-10.2.3 -->
