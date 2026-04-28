# HoTT Intro Agda Pairing

## Conventions

### Organization of the files

- For every chapter, there is a file, which imports all the sections and exercises of that chapter. This file also contains the introduction to that chapter. The file names for these chapter files take the following form:

  ```text
  chapter-1-dependent-type-theory.lagda
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
