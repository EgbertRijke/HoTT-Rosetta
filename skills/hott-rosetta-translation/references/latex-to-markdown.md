# LaTeX To Markdown

Use this reference for detailed conversion hints when translating `book/*.tex` into literate Agda Markdown files.

Keep the core file structure, naming, and validation rules in `../SKILL.md`.
Record recurring LaTeX-to-Markdown mappings here, especially mappings for project-specific macros and symbols.
If you encounter an unfamiliar LaTeX symbol or macro, ask the user for the intended Markdown translation before proceeding.
After the user answers, record the translation in this file for future use.

## Inline Text

- Cut any `\index{...}` text.
- Remove LaTeX labels such as `\label{...}`.
- For cross references such as `\cref{...}` or `\ref{...}`, ask the user for the intended Markdown wording before proceeding.
- Convert `\emph{...}` to `*...*`.
- Convert `\define{...}` and `\textbf{...}` to `**...**`.

## Mathematics

- Convert `\id{x}{y}` to `` `x = y` ``.
- In general, math symbols and inline mathematical expressions should be written in code guards, as `` `...` ``.
- For displayed mathematics, use fenced `text` blocks with the corresponding Unicode symbols, preceded and followed by one blank line.
- Record LaTeX-to-Markdown and LaTeX-to-Unicode translations in this file for consistency in later translations.

## Symbol Translations

Record recurring translations here as they are confirmed.
