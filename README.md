# HoTT Rosetta

The HoTT Rosetta pairs natural language and formalized mathematics in homotopy type theory, an extension of Martin-Löf's intensional dependent type theory with Voevodsky's univalence axiom with some higher inductive types. 

This repository will ultimately cover the contents of [Egbert Rijke](https://egbertrijke.github.io/)'s book [Introduction to Homotopy Type Theory](https://www.cambridge.org/us/universitypress/subjects/mathematics/logic-categories-and-sets/introduction-homotopy-type-theory) published in November 2025 by Cambridge University Press. The source natural language text comes from the [arXiv version](https://arxiv.org/abs/2212.11082), whose LaTeX source files are included here for convenience. 

The formalizations are in [agda](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html). The code is copied from or derived from the [agda-unimath library](https://unimath.github.io/agda-unimath/).

The main contents of this repository are literate agda files, with agda codeblocks embedded in a markdown file containing natural language text converted from the LaTeX. These codeblocks can be typechecked by agda. This repository compiles independently of any particular agda library. These files are intended to be both human-readable, providing an introduction to homotopy theory both in natural language and in agda, and machine readable, providing training data for autoformalization agents targeting homotopy type theory.

## Conventions

### Organization of the files

- For every chapter, there is a file, which imports all the sections and exercises of that chapter. This file also contains the introduction to that chapter. The file names for these chapter files take the following form:

  ```text
  chapter-1-dependent-type-theory.lagda.md
  ```
  
- Each section and each exercise gets its own file.

### Structure of each file

- Every file starts with a level 1 header `#` followed by the chapter or section number and title. For example, the file `chapter-1-dependent-type-theory.lagda.md` has as its header:

  ```text
  # Chapter 1 Dependent Type Theory
  ```

- Following the title of the file is the module declaration, which is to be written in an `agda` code block, as in:

  ````text
  ```agda
  module chapter-1-dependent-type-theory where
  ```
  ````

- The main body of the text is written in markdown. Mathematical expressions are written in code guards using unicode symbols. Displayed equations are written in `text` code blocks preceeded and succeeded by one blank line, as in:

  ````text
  The univalence axiom implies that equality of types is equivalent to equivalence of types:

  ```text
  (A ＝ B) ≃ (A ≃ B).
  ```

  In other words, the univalence axiom characterizes the identity type of the universe.
  ````
  
### Formatting conventions for text.

- Every sentence starts on a new line.

### Formatting conventions for mathematical expressions in markdown.

### Formatting conventions for formalized mathematics in Agda

## Contributors

This repository has been developed by 

* [Yuriy Brun](http://www.cs.umass.edu/~brun/)
* [Daniel Carranza](https://daniel-carranza.github.io/)
* [Arnav Dandu](https://dandu.dev)
* [Kevin Fisher](https://github.com/kfish610)
* [Kiran Gopinathan](https://kirancodes.me)
* [Audra Aurora Izzani](https://github.com/aizzani2)
* [Trey Plante](https://github.com/trey3p)
* [Emily Riehl](https://emilyriehl.github.io/)
* [Egbert Rijke](https://egbertrijke.github.io/)
* [Talia Ringer](https://dependenttyp.es)

as part of ASTRAL: Automated Synthetic Theorem-Proving by Reasonining with Language Models, a team funded by DARPA's [expMath program](https://www.darpa.mil/research/programs/expmath-exponential-mathematics). 
