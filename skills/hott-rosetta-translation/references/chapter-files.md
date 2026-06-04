# Chapter Files

To create a new chapter file, follow the general naming and file header conventions described in `../SKILL.md`.

Use `../STATUS.md` to identify the corresponding LaTeX source file.
Then copy the opening text of the LaTeX source file that appears below the opening LaTeX section heading and above the first LaTeX subsection heading.

Delete any `\index{...}` text.
Convert the remaining LaTeX to Markdown.

At the end of the chapter file, add an Agda code block importing any section files and exercise files that already exist and are contained within the chapter.
List all section files first, in numerical order, followed by all exercise files, in numerical order.
The README convention is that every chapter file imports all sections and exercises of that chapter; when some of those files do not exist yet, import only the existing ones and add the rest as they are created.

As new section or exercise files are created, update the corresponding chapter file to import them.
