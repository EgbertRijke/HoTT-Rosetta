# Section Files

To create a new section file, follow the general naming and file header conventions described in `../SKILL.md`.

Use `../STATUS.md` to identify the corresponding LaTeX source file.
Before doing any work, pull the remote and update `../STATUS.md` to see whether the section file is missing.
If it is partially prepared, stop and ask the user how to proceed.

The general objective is to copy all of the text in the appropriate LaTeX `\subsection` into this `.lagda.md` section file.
Convert the LaTeX to Markdown following the instructions in `latex-to-markdown.md`.

The section title itself is a level-one header, e.g. `# Section 3.2 Addition on the natural numbers`.
Definitions, propositions, and any theorem environment should be level-two headers of the form `## Definition 3.2.1`, using the correct chapter number, section number, and reference number.

For any definition, construction, or remark that defines elements or types, include a corresponding Agda code block.
For each Agda code block, search the agda-unimath library for the corresponding Agda code and copy it in exactly.
In parallel, search this repository for existing imports that might help the copied code compile.
After copying the code and adding only repository-local imports, check whether the section file typechecks.
If the copied code fails to typecheck, do not try to correct or rewrite the code.
Instead, stop and report an error message that diagnoses what went wrong, including the relevant Agda error and any missing local imports or dependencies you found.

In general, do not write any Agda code in section files that is not copied verbatim from the agda-unimath library.
