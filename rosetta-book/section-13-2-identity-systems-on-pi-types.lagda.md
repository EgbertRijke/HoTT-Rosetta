# Section 13.2 Identity systems on Π-types

```agda
module section-13-2-identity-systems-on-pi-types where
```

<!-- rosetta-item: section-13.2 -->

Recall from Section 11.6 that the *structure identity principle* is a way to obtain an identity system on a `Σ`-type.
Identity systems were defined in Definition 11.2.1.
In this section we will describe how to obtain identity systems on a `Π`-type.
We will first show that `Π`-types distribute over `Σ`-types.
This theorem is sometimes called the *type theoretic principle of choice* because it can be seen as the Curry-Howard interpretation of the axiom of choice.

## Theorem 13.2.1

<!-- rosetta-item: theorem-13.2.1; latex-label: thm:choice -->

Consider a family of types `C(x,y)` indexed by `x:A` and `y:B(x)`.
Then the map
```text
choice:(Π(x:A) Σ(y:B(x)) C(x,y))→ (Σ(f:Π(x:A) B(x)) Π(x:A) C(x,f(x)))
```
given by
```text
choice(h):=(λ x. pr 1(h(x)),λ x. pr 2(h(x))).
```
is an equivalence.

### Proof

<!-- rosetta-item: subheading-13.2-proof -->

*Proof.* We define the map
```text
choice^{-1}:(Σ(f:Π(x:A) B(x)) Π(x:A) C(x,f(x)))→ Π(x:A) Σ(y:B(x)) C(x,y)
```
by `choice^{-1}(f,g):=λ x. (f(x),g(x))`.
Then we have to construct homotopies
```text
choice∘choice^{-1}~id, and
choice^{-1}∘choice~id.
```
For the first homotopy it suffices to construct an identification
```text
choice(choice^{-1}(f,g))=(f,g)
```
for any `f:Π(x:A) B(x)` and any `g:Π(x:A) C(x,f(x))`.
We compute the left-hand side as follows:
```text
choice(choice^{-1}(f,g))
≐ choice(λ x. (f(x),g(x)))
≐ (λ x. f(x),λ x. g(x)).
```
By the `η`-rule for `Π`-types we have the judgmental equalities `f≐ λ x. f(x)` and `g≐λ x. g(x)`.
Therefore we have the identification
```text
refl:choice(choice^{-1}(f,g))=(f,g).
```
This completes the construction of the first homotopy.

For the second homotopy we have to construct an identification
```text
choice^{-1}(choice(h))=h
```
for any `h:Π(x:A) Σ(y:B(x)) C(x,y)`.
We compute the left-hand side as follows:
```text
choice^{-1}(choice(h))
≐ choice^{-1}(λ x. pr 1(h(x)),(λ x. pr 2(h(x))))
≐ λ x. (pr 1(h(x)),pr 2(h(x)))
```
However, it is *not* the case that `(pr 1(h(x)),pr 2(h(x)))≐ h(x)` for any `h:Π(x:A) Σ(y:B(x)) C(x,y)`.
Nevertheless, we have the identification
```text
eq-pair(refl,refl):(pr 1(h(x)),pr 2(h(x)))= h(x).
```
Therefore we obtain the required homotopy by function extensionality:
```text
λ h. eq-htpy(λ x. eq-pair(refl,refl)):choice^{-1}∘choice~id.
```
 ◻

<!-- rosetta-item-end: theorem-13.2.1 -->

The fact that `Π`-types distribute over `Σ`-types has many useful consequences.
The most straightforward consequence is the following.

## Corollary 13.2.2

<!-- rosetta-item: corollary-13.2.2 -->

For any two types `A` and `B`, and any type family `C` over `B`, we have an equivalence
```text
(A→Σ(y:B) C(y))≃(Σ(f:A→ B) Π(x:A) C(f(x))).
```

<!-- rosetta-item-end: corollary-13.2.2 -->

Another direct consequence of the distributivity of `Π`-types over `Σ`-types is the fact that
```text
Π(b:B) fib(f, b)≃Σ(g:B→ A) f∘ g~ id.
```
In the following corollary we use the distributivity of `Π`-types over `Σ`-types to show that dependent functions are sections of projection maps.

## Corollary 13.2.3

<!-- rosetta-item: corollary-13.2.3; latex-label: ex:pi_sec -->

Consider a type family `B` over `A`, and consider the projection map
```text
pr 1:(Σ(x:A) B(x)) → A.
```
Then we have an equivalence
```text
sec(pr 1)≃Π(x:A) B(x).
```

### Proof

<!-- rosetta-item: subheading-13.2-proof-2 -->

*Proof.* Theorem 13.2.1 gives the first equivalence in the following calculation:
```text
Σ(h:A→Σ(x:A) B(x)) pr 1∘ h~ id
≃ Σ((f,g):Σ(f:A→ A) Π(x:A) B(f(x))) f~ id
≃ Σ((f,H):Σ(f:A→ A) f~ id) Π(x:A) B(f(x))
≃ Π(x:A) B(x)
```
In the second equivalence we used Exercise 9.5 to swap the family `f↦ Π(x:A) B(f(x))` with the family `f↦ f~id`, and in the third equivalence we used the fact that
```text
Σ(f:A→ A) f~id
```
is contractible, with center of contraction `(id,refl-htpy)`.
One way to see that it is contractible is by Exercise 13.1.
A direct way to see this, is by another application of Theorem 13.2.1.
This gives an equivalence
```text
(Σ(f:A→ A) f~id)≃ (Π(x:A) Σ(y:A) y=x),
```
and the right-hand side is a product of contractible types. ◻

<!-- rosetta-item-end: corollary-13.2.3 -->

In the final application of distributivity of `Π`-types over `Σ`-types we obtain a general way of constructing identity systems of `Π`-types.

## Theorem 13.2.4

<!-- rosetta-item: theorem-13.2.4; latex-label: cor:Eq-Pi -->

Consider a family `B` of types over `A`, and for each `b:B(a)` consider an identity system `E(b)` at `b`.
Furthermore, consider a dependent function `f:Π(x:A) B(x)`.
Then the family of types
```text
Π(x:A) E(f(x),g(x))
```
indexed by `g:Π(x:A) B(x)` is an identity system at `f`.

### Proof

<!-- rosetta-item: subheading-13.2-proof-3 -->

*Proof.* By Theorem 11.2.2 it suffices to show that the type
```text
Σ(g:Π(x:A) B(x)) Π(x:A) E(f(x),g(x))
```
is contractible.
By Theorem 13.2.1 it follows that this type is equivalent to the type
```text
Π(x:A) Σ(y:B(x)) E(f(x),y).
```
This is a product of contractible types because each `E(f(x))` is an identity system at `f(x):B(x)`.
This product is therefore contractible by the weak function extensionality principle. ◻

<!-- rosetta-item-end: theorem-13.2.4 -->
