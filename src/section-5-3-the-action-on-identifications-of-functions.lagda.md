# Section 5.3 The action on identifications of functions

```agda
module section-5-3-the-action-on-identifications-of-functions where
```

Using the induction principle of the identity type we can show that every
function preserves identifications.
In other words, every function sends identified elements to identified elements.
Note that this is a form of continuity for functions in type theory: If there is
an identification that identifies two points `x` and `y` of a type `A`, then
there also is an identification that identifies the values `f(x)` and `f(y)` in
the codomain of `f`.

## Definition 5.3.1

Let `f : A → B` be a map. We define the **action on paths** of `f` as an
operation

```text
  ap_f : Π(x, y : A) x = y → f(x) = f(y).
```

Moreover, there are operations

```text
      ap-id_A  : Π(x, y : A) Π(p : x = y) p = ap_(id)(p),
  ap-comp(f,g) : Π(x, y : A) Π(p : x = y) ap_g(ap_f(p)) = ap_(g ∘ f)(p).
```

## Construction

First we define `ap_f` by the induction principle of identity types, taking

```text
  ap_f(refl) ≔ refl.
```

Next, we construct `ap-id_A` by the induction principle of identity types,
taking

```text
  ap-id_A(refl) ≔ refl.
```

Finally, we construct `ap-comp(f,g)` by the induction principle of identity
types, taking

```text
  ap-comp(f, g, refl) ≔ refl.
```

## Definition 5.3.2

Let `f : A → B` be a map.
Then there are identifications

```text
       ap-refl(f, x) : ap_f(refl) = refl
        ap-inv(f, p) : ap_f(p⁻¹) = ap_f(p)⁻¹
  ap-concat(f, p, q) : ap_f(p ∙ q) = ap_f(p) ∙ ap_f(q)
```

for every `p : x = y` and `q : x = y`.

## Construction

To construct `ap-refl(f,x)` we simply observe that `ap_f(refl) ≐ refl`, so we
take

```text
  ap-refl(f,x) ≔ refl.
```

We construct `ap-inv(f,p)` by identification elimination on `p`, taking

```text
  ap-inv(f, refl) ≔ refl.
```

Finally we construct `ap-concat(f,p,q)` by identification elimination on `p`,
taking

```text
  ap-concat(f, refl, q)  ≔  refl.
```
