# HoTT Rosetta

The HoTT Rosetta pairs natural language and formalized mathematics in homotopy type theory, an extension of Martin-Löf's intensional dependent type theory with Voevodsky's univalence axiom with some higher inductive types.

This repository will ultimately cover the contents of [Egbert Rijke](https://egbertrijke.github.io/)'s book [Introduction to Homotopy Type Theory](https://www.cambridge.org/us/universitypress/subjects/mathematics/logic-categories-and-sets/introduction-homotopy-type-theory) published in November 2025 by Cambridge University Press. The source natural language text comes from the [arXiv version](https://arxiv.org/abs/2212.11082), whose LaTeX source files are included here for convenience.

The formalizations are in [agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html). The code is copied from or derived from the [agda-unimath library](https://unimath.github.io/agda-unimath/).

The main contents of this repository are literate agda files, with agda codeblocks embedded in a markdown file containing natural language text converted from the LaTeX. These codeblocks can be typechecked by agda. This repository compiles independently of any particular agda library. These files are intended to be both human-readable, providing an introduction to homotopy theory both in natural language and in agda, and machine readable, providing training data for autoformalization agents targeting homotopy type theory.

This repository also contains an introductory HoTT (auto)formalization benchmark in the form of unsolved exercises.
The file `BENCHMARK.md` contains a list of where those exercises can be found.

## Layout

- `latex-book/`: LaTeX source
- `rosetta-book/`: maintained literate Agda

The prose comes from the [arXiv book](https://arxiv.org/abs/2212.11082), and
formalizations are sourced from
[agda-unimath](https://unimath.github.io/agda-unimath/).

## Organization of the files

- For every chapter, there is a file, which imports all the sections and exercises of that chapter. This file also contains the introduction to that chapter. The file names for these chapter files take the following form:

  ```text
  chapter-1-dependent-type-theory.lagda.md
  ```

- Each section and each exercise gets its own file:

  ```text
  exercise-1-1-exercise.lagda.md
  section-1-1-judgements-and-contexts-in-type-theory.lagda.md
  ```

## Compiling the repository

To work with this repository:
 1. Make a local copy
 2. Download and install agda, along with an agda language server in an editor of your choice (e.g. emacs, VSCode)
 3. Open any of the "literate agda" `.lagda.md` files and use `Ctrl+c` `Ctrl+l` to load and typecheck.
 4. New code can be added inside an agda codeblock:

    ````text
    ```agda
    is-contr : {l : Level} → Type l → Type l
    is-contr A = Σ A (λ a → (x : A) → a ＝ x)
    ```
    ````

## Development and contributions

Edit the Rosetta files directly. Existing Markdown and Agda edits are permanent;
generation is used only to create missing files. Accepted content changes are
shared between this repository and the development fork.

Backend tools, review software, and development documentation live in
[daniel-carranza/HoTT-Rosetta](https://github.com/daniel-carranza/HoTT-Rosetta).
The public content consists of `rosetta-book/`, `latex-book/`, `README.md`, and
`BENCHMARK.md`. Needed auxiliary results are added where they naturally belong,
including earlier sections. They are not kept in separate proposal versions.

## Contributors

This repository has been developed by

* [Yuriy Brun](http://www.cs.umass.edu/~brun/)
* [Daniel Carranza](https://daniel-carranza.github.io/)
* [Arnav Dandu](https://dandu.dev)
* [Kevin Fisher](https://github.com/kfish610)
* [Kiran Gopinathan](https://kirancodes.me)
* [Audra Aurora Izzani](https://github.com/aizzani2)
* [Eyad Loutfi](https://github.com/eloutf)
* [Trey Plante](https://github.com/trey3p)
* [Emily Riehl](https://emilyriehl.github.io/)
* [Egbert Rijke](https://egbertrijke.github.io/)
* [Talia Ringer](https://dependenttyp.es)

as part of ASTRAL: Automated Synthetic Theorem-Proving by Reasonining with Language Models, a team funded by DARPA's [expMath program](https://www.darpa.mil/research/programs/expmath-exponential-mathematics).
