# Section 20.2 Observational equality of W-types

```agda
module section-20-2-observational-equality-of-w-types where
```

<!-- rosetta-item: section-20.2 -->

Each element `x:W(A,B)` has symbol `symbol(x):A` and a family of components `component(x):B(symbol(x))→W(A,B)`.
Therefore, we have a map
```text
η : W(A,B)→ Σ(x:A) (B(x)→W(A,B))
```
given by `η(x)≔(symbol(x),component(x))`.

## Proposition 20.2.1

<!-- rosetta-item: proposition-20.2.1; latex-label: prp:algebra-W -->

The map `η:W(A,B)→Σ(x:A) (B(x)→W(A,B))` is an equivalence.

### Proof

<!-- rosetta-item: subheading-20.2-proof -->

*Proof.* We define
```text
ε : (Σ(x:A) (B(x)→W(A,B)))→W(A,B)
```
by `ε(x,α)≔tree(x,α)`.
The fact that `ε` is an inverse of `η` follows easily. ◻

<!-- rosetta-item-end: proposition-20.2.1 -->

The fact that we have an equivalence
```text
W(A,B)≃Σ(x:A) (B(x)→W(A,B)),
```
suggests a way to characterize the identity type of `W(A,B)`.
Indeed, any equivalence is an embedding, and therefore we also have
```text
(x=y)≃ (η(x)=η(y)).
```
The latter is an identity type in a `Σ`-type, which can be characterized as a `Σ`-type of identity types.
We therefore define the following observational equality relation on `W(A,B)`.

## Definition 20.2.2

<!-- rosetta-item: definition-20.2.2 -->

Suppose `A` and each `B(x)` are in `𝒰`.
We define a binary relation
```text
Eq_W : W(A,B)→ W(A,B)→ 𝒰
```
recursively by
```text
Eq_W(tree(x,α),tree(y,β)) ≔ Σ(p:x=y) Π(z:B(x)) α(z)=β(tr_B(p,z))
```

<!-- rosetta-item-end: definition-20.2.2 -->

## Theorem 20.2.3

<!-- rosetta-item: theorem-20.2.3; latex-label: thm:EqW -->

The observational equality relation `Eq_W` on `W(A,B)` is reflexive, and the canonical map
```text
(x=y)→ Eq_W(x,y)
```
is an equivalence for each `x,y:W(A,B)`.

### Proof

<!-- rosetta-item: subheading-20.2-proof-2 -->

*Proof.* The element `refl-Eq_W(x):Eq_W(x,x)` is defined recursively as
```text
refl-Eq_W(tree(x,α))≔ (refl,refl-htpy_α).
```
This proof of reflexivity induces the canonical map `(x=y)→Eq_W(x,y)`.
To show that it is an equivalence for each `x,y:W(A,B)`, we apply the fundamental theorem of identity types, by which it suffices to show that the type
```text
Σ(y:W(A,B)) Eq_W(x,y)
```
is contractible for each `x:W(A,B)`.
The center of contraction is the pair `(x,refl-Eq_W(x))`.
For the contraction, we have to construct a function
```text
h:Π(y:W(A,B)) Π(p:Eq_W(x,y)) (x,refl-Eq_W(x))=(y,p).
```
By the induction principle of W-types, it suffices to define
```text
h(tree(y,β),(p,H))≔ (x,(refl,refl-htpy))=(y,(p,H)).
```
Here we proceed by identification elimination on `p:x=y`, followed by homotopy induction on the homotopy `H:α~ β`.
Thus, it suffices to construct an identification
```text
(x,(refl,refl-htpy))=(x,(refl,refl-htpy)),
```
which we have by reflexivity. ◻

<!-- rosetta-item-end: theorem-20.2.3 -->

## Theorem 20.2.4

<!-- rosetta-item: theorem-20.2.4 -->

Consider a type family `B` over a type `A`, and let `k:𝕋` be a truncation level.
If `A` is a `(k+1)`-type, then so is `W(A,B)`.

### Proof

<!-- rosetta-item: subheading-20.2-proof-3 -->

*Proof.* Suppose that `A` is a `(k+1)`-type.
In order to show that `W(A,B)` is a `(k+1)`-type, we have to show that its identity types are `k`-types.
The proof is by induction on `x,y:W(A,B)`.
For `x≐tree(a,α)` and `y≐tree(b,β)`, we have the equivalence
```text
(tree(a,α)=tree(b,β))≃Σ(p:a=b) Π(z:B(a)) α(z)=β(tr_B(p,z))
```
Note that the type `a=b` is a `k`-type by the assumption that `A` is a `(k+1)`-type.
Furthermore, the type `α(z)=β(tr_B(p,z))` is a `k`-type by the induction hypothesis.
Therefore it follows that the type on the right-hand side of the displayed equivalence is a `k`-type, and this completes the proof. ◻

<!-- rosetta-item-end: theorem-20.2.4 -->
