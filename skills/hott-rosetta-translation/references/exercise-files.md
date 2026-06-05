# Exercise Files

To create a new exercise file, follow the general naming and file header conventions described in `../SKILL.md`.

Use `../STATUS.md` to identify the corresponding LaTeX source file.
Before doing any work, pull the remote and update `../STATUS.md` to see whether the exercise file is missing.
If the target file exists but appears incomplete, partially translated, or inconsistent with `../STATUS.md`, stop and ask the user how to proceed.

An exercise file corresponds to one `\exitem` in the `exercises` environment of the corresponding LaTeX source file.
The general objective is to copy all of the text in that `\exitem` into the `.lagda.md` exercise file and convert the LaTeX to Markdown following `latex-to-markdown.md`.

The exercise title itself is a level-one header, e.g. `# Exercise 3.1 Multiplication and exponentiation`.
Choose a concise topic title and filename slug from the exercise statement, matching existing files.

## Structure

Use `## Problem statement` for the translated exercise prompt and `## Solution` for the Agda formalization or explanation.
If one `\exitem` contains several tasks, use repeated `## Problem statement` and `## Solution` pairs, following existing files such as `src/exercise-3-1-multiplication-and-exponentiation.lagda.md`.

The first Agda code block must contain the module declaration and any imports.
Only import files that exist in this repository.
Choose imports by inspecting nearby existing exercise and section files and by searching this repository for the definitions needed by the copied code.

## Agda Code

For each solution code block, search the agda-unimath library for the corresponding Agda code and copy it in exactly when it exists.
In parallel, search this repository for existing imports that might help the copied code compile.
After copying the code and adding only repository-local imports, check whether the exercise file typechecks.
If copied agda-unimath code fails to typecheck, do not try to correct or rewrite the code unless the user explicitly asks for that.
Instead, stop and report an error message that diagnoses what went wrong, including the relevant Agda error and any missing local imports or dependencies you found.

In general, do not write new Agda code in exercise files unless no corresponding agda-unimath code exists and the user has asked for a formalization, or the user explicitly asks for handwritten code.
If no corresponding agda-unimath code exists, say so in the final report and keep any user-requested handwritten code minimal and consistent with existing repository style.

## Agda-Unimath Sources

When agda-unimath source code or related definitions are found, add an `## Agda-unimath sources` section at the end of the exercise file.
List the relevant agda-unimath module names and, when useful, the names of copied definitions.

## Validation

Before finishing a new exercise file:

1. Confirm the filename, module name, and level-one header agree.
2. Confirm the full intended `\exitem` was translated.
3. Confirm all imports refer only to files present in this repository.
4. Run `agda src/exercise-N-K-slug.lagda.md`.
5. Update `../STATUS.md` and update the corresponding chapter file import list if the chapter file exists.

Updating the corresponding chapter file with a missing exercise import is an expected addition of missing material, but do not otherwise edit existing chapter text without user approval.
