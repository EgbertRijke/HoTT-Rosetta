---
name: hott-rosetta-translation
description: Translate LaTeX sources in book/ into literate Agda Markdown files in src/ for HoTT-Rosetta. Use when creating chapter, section, or exercise .lagda.md files from the book sources, preserving repository naming, module, markdown, and Agda conventions.
---

# HoTT-Rosetta Translation

## Scope

Use this workflow to translate the LaTeX files in `book/` into literate Agda Markdown files in `src/`.
Treat `README.md` as the repository-level source of truth for file organization, file structure, Markdown formatting, and self-contained Agda compilation conventions.

In this repository, a `src/chapter-N-...lagda.md` file corresponds to a globally numbered LaTeX `\section`, not to a LaTeX `\chapter`.
A `src/section-N-M-...lagda.md` file corresponds to a LaTeX `\subsection` inside that `\section`.
A `src/exercise-N-K-...lagda.md` file corresponds to the `K`th `\exitem` in that `\section`'s exercises block.

## New File Preflight

Whenever asked to create a new chapter, section, or exercise file:

1. Pull remote changes to the repository first.
2. Update `skills/hott-rosetta-translation/STATUS.md` from the current repository contents.
3. Check whether the requested file is still listed as missing.
4. If the requested file is no longer missing, stop without creating a duplicate file and instead describe the contents of the existing file to the user.

## Editing Existing Files

Do not edit, cut, reorganize, or delete existing file contents without checking with the user, unless the user has explicitly instructed you to do so.
Adding missing material is usually acceptable when it is needed for the requested translation work, but preserve existing text and Agda code unless the user approves a change.

## Source Order

Read `book/hott-intro.tex`.
Follow the uncommented `\input{chapter-...}` entries, then the uncommented `\input{...}` entries inside those chapter files.
Continue in source order, not alphabetical order.

## Naming

Use lowercase ASCII slugs with words separated by hyphens.

- Chapter file: `src/chapter-N-title-slug.lagda.md`
- Section file: `src/section-N-M-title-slug.lagda.md`
- Exercise file: `src/exercise-N-K-short-topic-slug.lagda.md`

Examples:

- `chapter-3-the-natural-numbers.lagda.md`
- `section-3-2-addition-on-the-natural-numbers.lagda.md`
- `exercise-3-1-multiplication-and-exponentiation.lagda.md`

For exercise slugs, choose a concise mathematical topic slug from the exercise statement, matching existing style.

## File Headers And Modules

Every file starts with a level-1 Markdown heading, then an Agda module declaration.
The heading should include the chapter, section, or exercise number and title.
The module declaration is written in an `agda` code block immediately after the title.

Chapter:

````markdown
# Chapter N Title

```agda
module chapter-N-title-slug where
```
````

Section:

````markdown
# Section N.M Title

```agda
module section-N-M-title-slug where
```
````

Exercise:

````markdown
# Exercise N.K Title

```agda
module exercise-N-K-short-topic-slug where
```
````

The module name must exactly match the file basename.

## Chapter Files

For detailed chapter-file creation instructions, read `references/chapter-files.md`.

A chapter file contains the introductory prose from the corresponding LaTeX `\section` before its first `\subsection`.
Then import every created section and exercise file for that chapter.

Use plain imports:

```agda
open import section-N-1-...
open import exercise-N-1-...
```

Do not import files that do not exist unless the task is to create them in the same change.

## Section Files

A section file contains the translated body of the corresponding LaTeX `\subsection`.
For detailed LaTeX-to-Markdown conversion hints, read `references/latex-to-markdown.md`.

Follow existing Markdown conventions:

- One sentence per line.
- Inline mathematics becomes code spans where practical.
- Display mathematics becomes fenced `text` blocks, preceded and followed by one blank line.
- Definitions, propositions, remarks, examples, and similar theorem environments become Markdown headings such as `## Definition N.M.K` or `### Remark N.M.K`, following nearby files.
- Proofs may use `### Construction` or ordinary prose, matching the source and existing local style.
- Preserve meaningful citations and references in readable prose, e.g. `Chapter 5`, `Proposition 5.6.1`, or source labels when no converted target exists yet.
- Drop LaTeX indexing commands.
- Translate common HoTT notation into the Unicode/plain-text notation already used in `src/`.

Put Agda code blocks close to the mathematical definition or result they formalize.
Prefer definitions already present in earlier repository files over importing large external developments.

## Exercise Files

Exercise files should contain:

```markdown
## Problem statement
```

followed by the translated exercise statement, and then:

```markdown
## Solution
```

with Agda formalization when available or requested.

If the exercise has multiple parts, keep the statement structure clear with Markdown lists or subheadings.

## Agda Conventions

Inspect nearby files before writing code.
Agda code should follow the naming and coding conventions of the agda-unimath library, especially the upstream style guide at `https://github.com/UniMath/agda-unimath/blob/master/docs/CODINGSTYLE.md`.
Before writing an Agda code block, search the agda-unimath library at `https://github.com/UniMath/agda-unimath` for corresponding definitions, theorems, and proofs.
If corresponding agda-unimath code exists, copy it or adapt it as closely as the local self-contained repository context permits, preserving agda-unimath names and structure where possible.
The `.lagda.md` files in this repository must typecheck without depending on agda-unimath.
Do not import agda-unimath modules or any other external library modules in translated files.
Only import files that are present in this repository, such as `universe-levels`.

- Keep imports minimal.
- Reuse earlier chapter/section files where possible.
- Use `universe-levels` when universe declarations are needed.
- Do not introduce postulates unless explicitly requested.
- Keep names consistent with the book notation and existing Agda names.
- Typecheck edited files with `agda <file>` when Agda work is added or changed.

## Validation

Before finishing a created file:

1. Confirm the filename, module name, and heading agree.
2. Confirm the source LaTeX range was fully translated.
3. Confirm all imported modules exist.
4. Run Agda on files containing Agda code when feasible.
5. Update the status document with created and remaining chapter, section, and exercise files.
