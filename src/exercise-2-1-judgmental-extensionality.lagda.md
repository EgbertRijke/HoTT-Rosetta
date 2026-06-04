# Exercise 2.1 Judgmental extensionality of functions

The `η`-rule is often seen as a judgmental extensionality principle.
Use the `η`-rule to show that if `f` and `g` take equal values, then they must be equal, i.e., give a derivation for the rule

```text
    \Axiom Γ ⊢ f : Π(x:A) B(x)`
    \noLine
    \UnaryInf Γ ⊢ g : Π(x:A) B(x)`
    \noLine
    \UnaryInf Γ, x : A ⊢ f(x) ≐ g(x) : B(x)`
    \UnaryInf Γ ⊢ f ≐ g : Π(x:A) B(x).`
```

--

## Exercise 2.2 The right unit law of function composition

Give a derivation for the right unit law of Lemma 2.2.7.

--

## Exercise 2.3 The constant map

\begin{subexenum}
  \item Construct the \define{constant map}\index{constant map|textbf}\index{function!constant map|textbf}\index{const x@ const_x|textbf}\index{function!const@ const|textbf}
    \begin{prooftree}
      \AxiomC Γ ⊢ A type
      \UnaryInfC Γ, y : B⊢ const_y:A→ B`.}
    \end{prooftree}
  \item Show that
    \begin{prooftree}
      \AxiomC Γ ⊢ f:A→ B
      \UnaryInfC Γ,z:C⊢ const_z∘ f≐const_z : A→ C`.}
    \end{prooftree}
  \item Show that
    \begin{prooftree}
      \AxiomC Γ ⊢ A type
      \AxiomC Γ ⊢ g:B→ C
      \BinaryInfC Γ,y:B⊢ g∘const_y≐ const_{g(y)}:A→ C`.}
    \end{prooftree}
  \end{subexenum}

--

## Exercise 2.4 The swapping arguments function

  \begin{subexenum}
  \item Define the \define{swap function}\index{function!swap|textbf}\index{swap function|textbf}
    \begin{prooftree}
      \AxiomC Γ ⊢ A type
      \AxiomC Γ ⊢ B type
      \AxiomC Γ,x:A,y:B⊢ C(x,y) type
      \TrinaryInfC Γ ⊢ σ:\Big(Π(x:A)\prd{y:B}C(x,y)\Big)→\Big(\prd{y:B}Π(x:A)C(x,y)\Big)
    \end{prooftree}
    that swaps the order of the arguments.
  \item Show that
  \end{subexenum}
  \vspace{-.5\baselineskip}
  \begin{small}
    \begin{prooftree}
      \AxiomC Γ ⊢ A type
      \AxiomC Γ ⊢ B type
      \AxiomC Γ,x:A,y:B⊢ C(x,y) type
      \TrinaryInfC Γ ⊢ σ∘σ≐\idfunc:\Big(Π(x:A)\prd{y:B}C(x,y)\Big)→ \Big(Π(x:A)\prd{y:B}C(x,y)\Big).
    \end{prooftree}
  \end{small}
