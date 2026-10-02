# Section 19.5 The Eckmann-Hilton argument

```agda
module section-19-5-the-eckmann-hilton-argument where
```

The Eckmann-Hilton argument is used to show that `π_n(A)` is an abelian group for all `n ≥ 2`.
This is achieved by constructing an identification

```text
p ∙ q = q ∙ p
```

for all `p,q : Ω^2(A)`.
Note that identification elimination is not immediately applicable here, since both `p` and `q` are identifications of type `refl = refl` with neither endpoint free.
Therefore, we must come up with something else.

## Definition 19.5.1

Consider a binary operation `f : A → (B → C)`.
The **binary action on paths** of `f` is the family of functions

```text
ap-binary_f : (x = x') → ((y = y') → (f(x,y) = f(x',y')))
```

indexed by `x,x' : A` and `y,y' : B` given by `ap-binary_f(refl,refl) ≔ refl`.

## Lemma 19.5.2

The binary action on paths of `f : A → (B → C)` satisfies the following laws:

```text
ap-binary_f(refl,q) = ap_{f(x)}(q)
ap-binary_f(p,refl) = ap_{f(_,y)}(p)
```

and moreover both triangles in the following diagram commute:

```text
           [f(x,y)] ---ap_{f(_,y)}(p)--> [f(x',y)]
               |    \                        |
ap_{f(x,_)}(q) |        \ ap-binary_f(p,q)   | ap_{f(x',_)}(q)
               |            \                |
               |                \            |
               V                    V        V
           [f(x,y')] --ap_{f(_,y')}(p)--> [f(x',y')]
```

### Proof

_Proof._ The proof is immediate by identification elimination on `p` and `q`, where applicable. ◻

## Example 19.5.3

One particular binary operation to which we can apply the binary action on paths is concatenation of identifications

```text
_ ∙ _ : (x = y) → ((y = z) → (x = z))
```

This results in the **horizontal concatenation** operation

```text
_ ∙_h _ : (p = p') → ((q = q') → (p ∙ q = p' ∙ q')).
```

In other words, for any two identifications `r : p = p'` and `s : q = q'` as in the diagram

```text
[x] ----p----> [y] ----q----> [z]
        ⇓ r            ⇓ s
[x] ----p'---> [y] ----q'---> [z]
```

The repeated endpoint labels in these diagrams denote the same points.
We obtain `r ∙_h s ≔ ap-binary_{_ ∙ _}(r,s) : p ∙ q = p' ∙ q'`.
The **vertical concatenation** operation, which concatenates `r : p = p'` and `r' : p' = p''` as in the diagram

```text
[x] ----p----> [y]
        ⇓ r
[x] ----p'---> [y]
        ⇓ r'
[x] ----p''--> [y]
```

is given by ordinary concatenation of identifications.

## Lemma 19.5.4

Horizontal concatenation satisfies the following left and right unit laws:

```text
refl_refl ∙_h s = s
r ∙_h refl_refl = r.
```

### Proof

_Proof._ This follows by identification elimination on `r` and `s`, or alternatively via Lemma 19.5.2. ◻

In the following lemma we establish the **interchange law** for horizontal and vertical concatenation.

## Lemma 19.5.5

Consider a diagram of the form

```text
[x] ----p----> [y] ----q----> [z]
        ⇓ r            ⇓ s
[x] ----p'---> [y] ----q'---> [z]
        ⇓ r'           ⇓ s'
[x] ----p''--> [y] ----q''--> [z]
```

Then there is an identification

```text
(r ∙ r') ∙_h (s ∙ s') = (r ∙_h s) ∙ (r' ∙_h s').
```

### Proof

_Proof._ We use path induction on both `r` and `s`.
Then it suffices to show that

```text
(refl ∙ r') ∙_h (refl ∙ s') = (refl ∙_h refl) ∙ (r' ∙_h s')
```

Using the unit laws for ordinary concatenation, we see that both sides reduce to `r' ∙_h s'`. ◻

## Theorem 19.5.6

Consider a pointed type `A`, and let `r,s : Ω^2(A)`.
Then there is an identification

```text
r ∙ s = s ∙ r
```

### Proof

_Proof._ First we observe that `r ∙ s = r ∙_h s` by the following calculation using the unit laws from Lemma 19.5.4 and the interchange law from Lemma 19.5.5:

```text
r ∙ s = (r ∙_h refl_refl) ∙ (refl_refl ∙_h s)
= (r ∙ refl_refl) ∙_h (refl_refl ∙ s)
= r ∙_h s
```

Similarly, we observe that `r ∙_h s = s ∙ r` by the following calculation:

```text
r ∙_h s = (refl_refl ∙ r) ∙_h (s ∙ refl_refl)
= (refl_refl ∙_h s) ∙ (r ∙_h refl_refl)
= s ∙ r.
```

These two calculations combined prove the claim. ◻

## Corollary 19.5.7

For `n ≥ 2`, the `n`-th homotopy group of any pointed type is abelian.

### Proof

_Proof._ By Proposition 19.4.6 it follows that `π_n(A)` is isomorphic to the second homotopy group of some pointed type, for every `n ≥ 2`.
Therefore it suffices to prove the claim for `π_2(A)` for every pointed type `A`.

Our goal is to show that

```text
Π(r,s : π_2(A)) rs = sr.
```

Since we are constructing an identification in a set, we can use the dependent universal property of `0`-truncation on both `r` and `s`, stated in Theorem 18.5.2.
Therefore it suffices to show that

```text
Π(r,s : Ω^2(A)) η(r)η(s) = η(s)η(r).
```

The claim now follows, because

```text
η(r)η(s) = η(r ∙ s) = η(s ∙ r) = η(s)η(r).
```

 ◻
