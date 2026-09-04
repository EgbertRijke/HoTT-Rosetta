# Section 13.4 Composing with equivalences

```agda
module section-13-4-composing-with-equivalences where
```

<!-- rosetta-item: section-13.4 -->

We show in the following theorem that a map `f:A→ B` is an equivalence if and only if precomposing by `f` is an equivalence.

## Theorem 13.4.1

<!-- rosetta-item: theorem-13.4.1; latex-label: ex:equiv_precomp -->

For any map `f:A→ B`, the following are equivalent:

1.  `f` is an equivalence.

2.  For any type family `P` over `B` the map
```text
(Π(y:B) P(y))→(Π(x:A) P(f(x)))
```
    given by `h↦ h∘ f` is an equivalence.

3.  For any type `X` the map
```text
(B→ X)→ (A→ X)
```
    given by `g↦ g∘ f` is an equivalence.

### Proof

<!-- rosetta-item: subheading-13.4-proof -->

*Proof.* To show that (i) implies (ii), we first recall from Lemma 10.4.5 that any equivalence is also coherently invertible.
Therefore `f` comes equipped with
```text
g : B → A
G : f∘ g ~ id[B]
H : g∘ f ~ id[A]
K : G· f ~ f· H.
```
Then we define the inverse of `_∘ f` to be the map
```text
φ:(Π(x:A) P(f(x)))→(Π(y:B) P(y))
```
given by `h↦ λ y. tr_P(G(y),h(g(y)))`.

To see that `φ` is a section of `_∘ f`, let `h:Π(x:A) P(f(x))`.
By function extensionality it suffices to construct a homotopy `φ(h)∘ f~ h`.
In other words, we have to show that
```text
tr_P(G(f(x)),h(g(f(x)))=h(x)
```
for any `x:A`.
Now we use the additional homotopy `K` from our assumption that `f` is coherently invertible.
Since we have `K(x):G(f(x))=ap_{f}(H(x))` it suffices to show that
```text
tr_P(ap_{f}(H(x)),h(g(f(x))))=h(x).
```
A simple path-induction argument yields that
```text
tr_P(ap_{f}(p))~ tr_{P∘ f}(p)
```
for any path `p:x=y` in `A`, so it suffices to construct an identification
```text
tr_{P∘ f}(H(x),h(g(f(x))))=h(x).
```
We have such an identification by `apd_{h}(H(x))`.

To see that `φ` is a retraction of `_∘ f`, let `h:Π(y:B) P(y)`.
By function extensionality it suffices to construct a homotopy `φ(h∘ f)~ h`.
In other words, we have to show that
```text
tr_P(G(y),h(f(g(y))))=h(y)
```
for any `y:B`.
We have such an identification by `apd_{h}(G(y))`.
This completes the proof that (i) implies (ii).

Note that (iii) is an immediate consequence of (ii), since we can just choose `P` to be the constant family `X`.

It remains to show that (iii) implies (i).
Suppose that
```text
_∘ f:(B→ X)→ (A→ X)
```
is an equivalence for every type `X`.
Then its fibers are contractible by Theorem 10.4.6.
In particular, choosing `X≐ A` we see that the fiber
```text
fib(_∘ f, id[A])≐ Σ(h:B→ A) h∘ f=id[A]
```
is contractible.
Thus we obtain a function `h:B→ A` and a homotopy `H:h∘ f~id[A]` showing that `h` is a retraction of `f`.
We will show that `h` is also a section of `f`.
To see this, we use that the fiber
```text
fib(_∘ f, f)≐ Σ(i:B→ B) i∘ f=f
```
is contractible (choosing `X≔ B`).
Of course we have `(id[B],refl)` in this fiber.
However we claim that there also is an identification `p:(f∘ h)∘ f=f`, showing that `(f∘ h,p)` is in this fiber, because
```text
(f∘ h)∘ f ≐ f∘ (h∘ f)
= f∘ id[A]
≐ f
```
From the contractibility of the fiber we obtain an identification `(id[B],refl)=(f∘ h,p)`.
In particular we obtain that `id[B]=f∘ h`, showing that `h` is a section of `f`. ◻

<!-- rosetta-item-end: theorem-13.4.1 -->
