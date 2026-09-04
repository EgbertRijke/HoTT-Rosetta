# Section 20.1 The type of well-founded trees

```agda
module section-20-1-the-type-of-well-founded-trees where
```

<!-- rosetta-item: section-20.1 -->

## Definition 20.1.1

<!-- rosetta-item: definition-20.1.1 -->

Consider a type family `B` over `A`.
The **W-type** `W(A,B)` is defined as the inductive type with constructor
```text
tree : Π(x:A) (B(x)→ W(A,B))→ W(A,B).
```
The induction principle of the W-type `W(A,B)` asserts that, for any type family `P` over `W(A,B)`, any dependent function
```text
h : Π(x:A) Π(α:B(x)→ W(A,B)) (Π(y:B(x)) P(α(x)))→ P(tree(x,α))
```
determines a dependent function
```text
ind_W(h):Π(x:W(A,B)) P(x)
```
that satisfies the judgmental equality
```text
ind_W(h,tree(x,α))≐ h(x,α,λ y. ind_W(h,α(y))).
```
The elements of W-types are called **(well-founded) trees**.

<!-- rosetta-item-end: definition-20.1.1 -->

## Remark 20.1.2

<!-- rosetta-item: remark-20.1.2 -->

Some authors write `sup` for the constructor of a W-type.
The intuition that `tree(a,α)` is a supremum of the family of elements `α(y)` indexed by `y:B(a)` is, however, somewhat misleading, because `tree(a,α)` does not satisfy the defining properties of a supremum.

<!-- rosetta-item-end: remark-20.1.2 -->

## Remark 20.1.3

<!-- rosetta-item: remark-20.1.3 -->

When we define a dependent function
```text
f:Π(x:W(A,B)) P(x)
```
via the induction principle of W-types, we will often display that definition by pattern matching.
Such definitions are then displayed as
```text
f(tree(x,α))≔ h(x,α,λ y. f(α(y))),
```
which contains all the information to carry out the construction via the induction principle of W-types.
The advantage of definitions by pattern matching is that they directly display the defining judgmental equality the function being defined.

<!-- rosetta-item-end: remark-20.1.3 -->

## Remark 20.1.4

<!-- rosetta-item: remark-20.1.4; latex-label: rmk:constant-W -->

For any `x:A`, the function
```text
tree(x):(B(x)→W(A,B))→W(A,B)
```
takes a family of elements `α(y):W(A,B)` indexed by `y:B(x)` and collects them into an element `tree(x,α):W(A,B)`.
Since the element `tree(x,α)` has been constructed out of a family `α(y)` of elements of `W(A,B)` indexed by `y:B(x)`, we say that the type `B(x)` is the **arity** of `tree(x,α)`.
In other words, there is a function
```text
arity : W(A,B)→𝒰
```
given by `arity(tree(x,α))≔ B(x)`.
The element `x:A` is the **symbol** of the operation `tree(x):(B(x)→W(A,B))→W(A,B)`.
Note that there might be many different symbols `x,y:A` for which the operations `tree(x)` and `tree(y)` have equivalent arities, i.e., for which `B(x)≃ B(y)`.

Furthermore, the **components** of `tree(x,α)` are the elements `α(y):W(A,B)` indexed by `y:B(x)`.
In other words, we have
```text
component : Π(w:W(A,B)) arity(w) → W(A,B),
```
given by `component(tree(x,α))≔α`.

In the special case where `B(x)` is empty, there is exactly one family of elements `α(y):W(A,B)` indexed by `y:B(x)`.
Therefore, it follows that any `x:A` such that `B(x)` is empty induces a constant in the W-type `W(A,B)`.
More precisely, if we are given a map `h:B(x)→ empty`, then we can define the **constant**
```text
c_x(h)≔ tree(x,ex-falso∘ h).
```
The elements of `w:W(A,B)` for which the type `B(arity(w))` is empty are called the **constants** of `W(A,B)`.
In other words, the predicate
```text
is-constant_W : W(A,B)→Prop_𝒰
```
is defined by `is-constant_W(w)≔is-empty(B(arity(w)))`.

On the other hand, if each type `B(x)` is inhabited, then there are no such constants and we will see in the following proposition that the W-type `W(A,B)` is empty in this case.

<!-- rosetta-item-end: remark-20.1.4 -->

## Proposition 20.1.5

<!-- rosetta-item: proposition-20.1.5; latex-label: prp:is-empty-W -->

Consider a family `B` of types over `A`.
Then the following are equivalent:

1.  For each `x:A`, the type `B(x)` is nonempty.

2.  The `W`-type `W(A,B)` is empty.

In particular, if each `B(x)` is inhabited, then `W(A,B)` is empty.

### Proof

<!-- rosetta-item: subheading-20.1-proof -->

*Proof.* To prove that (i) implies (ii), assume that `¬¬(B(x))` holds for each `x:A`.
Our goal is to construct a function `f:W(A,B)→ empty`.
By the induction principle of W-types it suffices to construct a function of type
```text
Π(x:A) Π(α:B(x)→W(A,B)) (Π(y:B(x)) empty)→empty.
```
This type is judgmentally equal to the type
```text
Π(x:A) Π(α:B(x)→W(A,B)) ¬¬(B(x)),
```
so we obtain the desired function from the assumption that `¬¬(B(x))` holds for every `x:A`.

To prove that (ii) implies (i), suppose that `W(A,B)` is empty and let `x:A`.
To show that `¬¬(B(x))` holds, assume that `¬(B(x))` holds.
In other words, assume a function `h:B(x)→empty`.
Then we have the constant element `c_x(h):W(A,B)`.
This is impossible, since `W(A,B)` was assumed to be empty. ◻

<!-- rosetta-item-end: proposition-20.1.5 -->

## Example 20.1.6

<!-- rosetta-item: example-20.1.6; latex-label: eg:Nat-W -->

Consider the type family `P` over `bool` given by
```text
P(false) ≔ empty and P(true) ≔ unit.
```
We claim that the W-type `N≔ W(bool,P)` is equivalent to `ℕ`.
The idea is that the constructor `tree` of `W(bool,P)` splits into one nullary constructor with symbol `false` and arity `P(false)≐empty`, and one unary constructor with symbol `true` and arity `P(true)≐unit`.

More formally, we define the zero element `z:N` and the successor function `s:N→ N` by
```text
z≔ tree(false,ex-falso) and s(x)≔ tree(true,const_x).
```
Thus, we obtain a function `f:ℕ→ N` that satisfies `f(0)≐ z` and `f(succ-ℕ(n))≐ s(f(n))`.
It’s inverse `g:N→ ℕ` is defined via the induction principle of W-types by
```text
g(tree(false,α)) ≔ 0
g(tree(true,α)) ≔ succ-ℕ(g(α(⋆))).
```
It is immediate from these definitions that `g(f(n))=n` for all `n:ℕ`.
It remains to construct an identification `p(x):f(g(x))=x` for all `x:N`.
Such an identification is constructed inductively.
First, there is an identification
```text
p(tree(false,α)) : tree(false,ex-falso)=tree(false,α)
```
by the fact that `ex-falso=α` for any `α:empty→ N`.
Second, there is an identification
```text
p(tree(true,α)) : tree(true,const_{α(⋆)})=tree(true,α)
```
by the fact that `const_{α(⋆)}=α` for any map `α:unit→ N`.
This completes the construction of the equivalence `ℕ≃ N`.

<!-- rosetta-item-end: example-20.1.6 -->

## Example 20.1.7

<!-- rosetta-item: example-20.1.7; latex-label: eg:planar-binary-tree-W -->

Consider the type family `B` over `bool` given by
```text
B(false) ≔ empty and B(true) ≔ bool.
```
Then the W-type `W(bool,B)` is equivalent to the type of **oriented binary rooted trees**, which is the inductive type with constructors
```text
node : T_2
{[_,_]} : T_2→ (T_2 → T_2).
```
We leave the construction of the equivalence `T_2≃W(bool,B)` as Exercise 20.1.
The reason we call the elements of `T_2` oriented binary rooted trees is that in a tree of the form `[T_1,T_2]` we can see by inspection which branch is on the left and which branch is on the right.

<!-- rosetta-item-end: example-20.1.7 -->

## Example 20.1.8

<!-- rosetta-item: example-20.1.8; latex-label: eg:binary-tree-W -->

Consider the type `A≔ unit+BS_2`, where `BS_2` is the type of `2`-element types.
We define the family `B` over `A` by pattern matching:
```text
B(inl(x)) ≔ empty
B(inr(X)) ≔ X.
```
The type of **binary rooted trees** is the W-type `W(A,B)` for this choice of `A` and `B`.
We can also present the type of binary rooted trees as an inductive type with the following constructors:
```text
node : Bin-Tree
bin-tree : Π(X:BS_2) Bin-Tree^X→ Bin-Tree.
```
There is an important qualitative difference between the type of oriented binary rooted trees and the type of binary rooted trees.
Given two distinct oriented binary rooted trees `T_1` and `T_2`, the two oriented binary rooted trees `[T_1,T_2]` and `[T_2,T_1]` will also be distinct.
On the other hand, given two binary rooted trees `T_1` and `T_2`, the binary rooted trees
```text
bin-tree (bool,ind-bool(T_1,T_2))
bin-tree(bool,ind-bool(T_2,T_1))
```
can always be identified.
In the terminology of Exercise 19.10, the constructor `bin-tree` of `Bin-Tree` is equivalently described as a commutative binary operation on `Bin-Tree`.

<!-- rosetta-item-end: example-20.1.8 -->

## Example 20.1.9

<!-- rosetta-item: example-20.1.9; latex-label: eg:finitely-branching-tree-W -->

The W-type `W(ℕ,Fin)` is the type of **oriented finitely branching rooted trees**.
On the other hand, we define the type of **(unoriented) finitely branching rooted trees** to be the W-type `W(𝔽,T)`.
The qualitive difference between the types of oriented and unoriented finitely branching rooted trees is similar to the qualitative difference between types of oriented and unoriented binary rooted trees.
In the type of oriented finitely branching rooted trees, we record the ordering of the branches while in the type of unoriented finitely branching rooted trees there are identifications between trees that have the same branches up to permutation.

<!-- rosetta-item-end: example-20.1.9 -->
