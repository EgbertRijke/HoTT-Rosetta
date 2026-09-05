# Section files

Section files are the project’s primary content and formalization priority.
Each corresponds to one LaTeX `\subsection`; its source ends at the next
`\subsection`, exercises environment, or source-file end.

Preserve the complete natural-language mathematics, order, item numbering,
proofs, references, and displays. Use `# Section N.M Title` and numbered
level-two item headings such as `## Definition N.M.K`. Let the converter emit
the module declaration and stable item markers.

For every definition, result, construction, or proof that needs formalization,
search pinned agda-unimath for exact and analogous code. Add only copied,
provenance-backed code with necessary local adaptations; never invent code.
Keep code beside the prose step it implements while respecting Agda's
sequential dependency scope, and use only repository-local imports. For
relocations and helper groups, read `agda-block-placement.md`.

Do not place an auxiliary result in a section merely because later code needs
it. If it has an earlier mathematical home, place it there. If it has no natural
home in the file, leave its block empty and record both the exercise and its
invisible mathematics in the two required records.

After changing a section, regenerate it, inspect the active output, run
`python3 rosetta.py typecheck-candidate N M` when it contains Agda, and run the
repository validation required by `AGENTS.md`.
