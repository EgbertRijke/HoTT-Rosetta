# Section 1.4 Derivations

```agda
module section-1-4-derivations where
```

<!-- rosetta-item: section-1.4 -->

A **derivation** in type theory is a finite tree in which each node is a valid rule of inference.
At the root of the tree we find the conclusion, and in the leaves of the tree we find the hypotheses.
We give two examples of derivations: a derivation showing that any variable can be changed to a fresh one, and a derivation showing that any two variables that do not mutually depend on one another can be swapped in order.

Given a derivation with hypotheses `H_1,…,H_n` and conclusion `C`, we can form a new inference rule

<!-- rosetta-proof-tree: 620b08c35c1c; review: pending -->

*Proof tree (automatic faithful draft).*

```text
H_1   ⋯   H_n
─────────────
     $C$
```

Such a rule is called **derivable**, because we have a derivation for it.
In order to keep proof trees reasonably short and manageable, we use the convention that any derived rules can be used in future derivations.

### Changing variables

<!-- rosetta-item: subheading-1.4-changing-variables -->

Variables can always be changed to fresh variables.
We show that this is the case by showing that the inference rule

<!-- rosetta-proof-tree: 025a45734b09; review: pending -->

*Proof tree (automatic faithful draft).*

```text
      Γ, x:A, \Delta⊢ J
────────────────────────────── x'/x
Γ, x':A, \Delta[x'/x]⊢ J[x'/x]
```

is derivable, where `x'` is a variable that does not occur in the context `Γ, x:A, \Delta`.

Indeed, we have the following derivation using substitution, weakening, and the generic element:

<!-- rosetta-proof-tree: 45daab3d47a0; review: pending -->

*Proof tree (automatic faithful draft).*

```text
      Γ⊢ A type         Γ⊢ A type   Γ, x:A, \Delta⊢ J
───────────── \delta   ───────────────────────────── W
    Γ, x':A⊢ x':A             Γ, x':A, x:A, \Delta⊢ J
────────────────────────────────────────────────────── $S$
            Γ, x':A, \Delta[x'/x]⊢ J[x'/x]
```

In this derivation it is the application of the weakening rule where we have to check that `x'` does not occur in the context `Γ, x:A, \Delta`.

### Interchanging variables

<!-- rosetta-item: subheading-1.4-interchanging-variables -->

The **interchange rule** states that if we have two types `A` and `B` in context `Γ`, and we make a judgment in context `Γ, x:A, y:B, \Delta`, then we can make that same judgment in context `Γ, y:B, x:A, \Delta` where the order of `x:A` and `y:B` is swapped.
More formally, the interchange rule is the following inference rule

<!-- rosetta-proof-tree: ad3dfd3afb9c; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ B \textrm{type}   Γ, x:A, y:B, \Delta⊢ J
───────────────────────────────────────────
          $Γ, y:B, x:A, \Delta⊢ J$
```

Just as the rule for changing variables, we claim that the interchange rule is a derivable rule.

The idea of the derivation for the interchange rule is as follows: If we have a judgment
```text
Γ, x:A, y:B, \Delta⊢J,
```
then we can change the variable `y` to a fresh variable `y'` and weaken the judgment to obtain the judgment
```text
Γ, y:B, x:A, y':B, \Delta[y'/y]⊢J[y'/y].
```
Now we can substitute `y` for `y'` to obtain the desired judgment `Γ, y:B, x:A, \Delta⊢J`.
The formal derivation is as follows:

<!-- unsupported LaTeX environment: small -->

<!-- rosetta-proof-tree: 5f39ae928f51; review: pending -->

*Proof tree (automatic faithful draft).*

```text
 Γ⊢ B \textrm{type}                                    Γ, x:A, y:B, \Delta⊢ J
──────────────────                        ───────────────────────────────────
      Γ, y:B⊢ y:B    Γ⊢ B \textrm{type}   Γ, x:A, y':B, \Delta[y'/y]⊢ J[y'/y]
──────────────────   ────────────────────────────────────────────────────────
   Γ, y:B, x:A⊢ y:B                Γ, y:B, x:A, y':B, \Delta[y'/y]⊢ J[y'/y]
─────────────────────────────────────────────────────────────────────────────
                            Γ, y:B, x:A, \Delta⊢ J
```
