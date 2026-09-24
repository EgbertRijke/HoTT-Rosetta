# Section 16.2 Double counting in type theory

```agda
module section-16-2-double-counting-in-type-theory where
```

In combinatorics, counting arguments often proceed by showing that two finite sets are isomorphic—or, in the language of type theory, by showing that two finite types are equivalent.
The idea here is, of course, that when we count the elements of a type twice correctly, then both countings must result in the same number.
However, this is something that we must prove before we can use it.
In other words, we must show that

```text
  (Fin_{k} ≃ Fin_{l}) → (k = l)
```
for any two natural numbers `k` and `l`.
We will prove this claim as a consequence of the following general fact.

## Proposition 16.2.1

For any two types `X` and `Y`, there is a map

```text
  (X + unit ≃ Y + unit) → (X ≃ Y).
```

### Proof

We prove the claim in four steps.
We will write `i` for `inl : X → X + unit` and also for `inl : Y → Y + unit`, and we will write `⋆` for `inr(⋆) : X + unit` and also for `inr(⋆) : Y + unit`.

1. We first show that for any equivalence `e : X + unit ≃ Y + unit` and any `x : X` equipped with an identification `p : e(i(x)) = ⋆`, that there is an element

   ```text
     star-value(e,x,p) : Y
   ```
    
   equipped with an identification

   ```text
     α : i(star-value(e,x,p)) = e(⋆).
   ```

   To see this, note that the map `e` is injective.
   The elements `i(x)` and `⋆` are distinct, so it follows that the elements `e(i(x))` and `e(⋆)` are distinct.
   In particular, we have `e(⋆) ≠ ⋆`.
   Therefore it follows that there is an element `y : Y` equipped with an identification `i(y) = e(⋆)`.

2. Next, we construct for every equivalence `e : X + unit ≃ Y + unit` a map `f : X → Y` equipped with identifications

   ```text
     β : Π(y : Y) (e(i(x)) = i(y)) → (f(x) = y)
     γ : Π(p : e(i(x)) = ⋆) f(x) = star-value(e,x,p).
   ```

   In order to construct the map `f : X → Y`, we first construct a dependent function

   ```text
     f' : Π(x : X) Π(u : Y + unit) ((e(i(x)) = u) → Y).
   ```

   This function is defined by pattern matching on `u`, by

   ```text
     f'(x,i(y),p) ≔ y
        f'(x,⋆,p) ≔ star-value(e,x,p)
   ```

   Then we define `f(x) ≔ f'(x,e(i(x)),refl)`.
   By the definition of `f'` it then follows that we have an identification

   ```text
     f(x) ≐ f'(x,e(i(x)),refl)
          = f'(x,i(y),p)
          ≐ y
   ```
   
   for any `y : Y` and `p : e(i(x)) = i(y)`, and that we have an identification

   ```text
     f(x) ≐ f'(x,e(i(x)),refl)
          = f'(x,⋆,p)
          ≐ star-value(e,x,p)
   ```
    
   for any `p : e(i(x)) = ⋆`.

3. The inverse function `g : Y → X` is constructed in the same way as the
   function `f : X → Y`, using the equivalence `e⁻¹ : Y + unit ≃ X + unit`.
   This function comes equipped with

   ```text
     δ : Π(x : X) (e⁻¹(i(y)) = i(x)) → (g(y) = x)
     ε : Π(p : e⁻¹(i(y)) = ⋆) g(y) = star-value(e⁻¹,y,p).
   ```

4. It remains to show that `f` and `g` are inverse to each other.
   The proof that `g` is a retraction of `f` is similar to the proof that `g`
   is a section of `f`, so we will only prove the latter.
   In other words, we will construct an identification

   ```text
     f(g(y)) = y
   ```

   for any `y : Y`. The proof is by case analysis on `(e⁻¹(i(y)) = ⋆) + (e⁻¹(i(y)) ≠ ⋆)`. In the case where `p : e⁻¹(i(y)) = ⋆`, we have the identification

   ```text
     ε(p) : g(y) = star-value(e⁻¹,y,p).
   ```

   Furthermore, we have the identification

   ```text
     γ(q) : f(g(y)) = star-value(e,g(y),q),
   ```
   
   where `q : e(i(g(y))) = ⋆` is the composite of the identifications

   ```text
     e(i(g(y))) = e(i(star-value(e⁻¹,y,p)))
                = e(e^{-1}(⋆))
                =⋆.
   ```

   Using the identification `γ(q)`, we obtain

   ```text
     i(f(g(y))) = i(star-value(e,g(y),q))
                = e(⋆)
                = e(e⁻¹(i(y)))
                = i(y).
   ```

   Since `i : Y → Y + unit` is injective, it follows that `f(g(y)) = y`. ◻

## Theorem 16.2.2

For any two natural numbers `k` and `l`, there is a map

```text
  (Fin_{k} ≃ Fin_{l}) → (k = l).
```

### Proof

The proof is by induction on `k` and `l`.
In the base case, where both `k` and `l` are zero, the claim is obvious.
If `k` is zero and `l` is a successor, then we have `0 : Fin_{l}`.
Any equivalence `e : Fin_{k} ≃ Fin_{l}` now gives us the element

```text
  e⁻¹(0) : empty,
```

which is of course absurd.
Similarly, if `k` is a successor and `l` is zero, we obtain `e(0) : empty`, which is again absurd.
If both `k` and `l` are a successor, then we have by Proposition 16.2.1 the composite

```text
  (Fin_{k+1} ≃ Fin_{l+1}) ---> (Fin_{k} ≃ Fin_{l}) ---> (k = l) ---> (k+1 = l+1)
                                                                               ◻
```


```text
abstract
  double-counting-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
    number-of-elements-count count-C ＝
    sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x))
  double-counting-Σ count-A count-B count-C =
    ( double-counting count-C (count-Σ count-A count-B)) ∙
    ( number-of-elements-count-Σ count-A count-B)

abstract
  sum-number-of-elements-count-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : count (Σ A B)) →
    sum-count-ℕ e
      ( λ x → number-of-elements-count (count-fiber-count-Σ-count-base e f x)) ＝
    number-of-elements-count f
  sum-number-of-elements-count-fiber-count-Σ e f =
    ( inv
      ( number-of-elements-count-Σ e (count-fiber-count-Σ-count-base e f))) ∙
    ( double-counting (count-Σ e (count-fiber-count-Σ-count-base e f)) f)

abstract
  double-counting-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
    number-of-elements-count (count-B x) ＝
    number-of-elements-count (count-fiber-count-Σ-count-base count-A count-C x)
  double-counting-fiber-count-Σ count-A count-B count-C x =
    double-counting
      ( count-B x)
      ( count-fiber-count-Σ-count-base count-A count-C x)

abstract
  sum-number-of-elements-count-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
    sum-count-ℕ
      ( count-base-count-Σ b count-ΣAB count-B)
      ( λ x → number-of-elements-count (count-B x)) ＝
    number-of-elements-count count-ΣAB
  sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ b count-ΣAB count-B)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-A : count A) (count-B : (x : A) → count (B x))
    (count-ΣAB : count (Σ A B)) →
    number-of-elements-count (count-base-count-Σ b count-ΣAB count-B) ＝
    number-of-elements-count count-A
  double-counting-base-count-Σ b count-A count-B count-ΣAB =
    double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

abstract
  sum-number-of-elements-count-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
    ( count-B : (x : A) → count (B x)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    sum-count-ℕ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( λ x → number-of-elements-count (count-B x)) ＝
    number-of-elements-count count-ΣAB
  sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    number-of-elements-count
      ( count-base-count-Σ' count-ΣAB count-B count-nB) ＝
    number-of-elements-count count-A
  double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
    double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A
```
