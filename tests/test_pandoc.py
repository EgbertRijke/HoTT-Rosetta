import shutil
import unittest

from rosetta.pandoc import (
    latex_to_gfm,
    markdown_fragments_to_safe_html,
    markdown_to_safe_html,
    prepare_latex,
)


class PandocBoundaryTests(unittest.TestCase):
    def test_citation_groups_preserve_keys_without_numbering_them(self):
        self.assertEqual(
            prepare_latex(r"Kraus \cite{Kraus}; see \cite {A, B_2}."),
            r"Kraus [citation: \texttt{Kraus}]; see [citation: \texttt{A}, \texttt{B\_2}].",
        )
        self.assertEqual(prepare_latex(r"\citeextra{A}"), r"\citeextra{A}")

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is not installed")
    def test_citation_keys_survive_pandoc_including_groups(self):
        result = latex_to_gfm(r"Kraus \cite{Kraus}; see \cite{A, B_2}.")
        self.assertIn("citation: `Kraus`", result)
        self.assertIn("citation: `A`, `B_2`", result)

    def test_asterisk_tag_and_prose_symbol_survive(self):
        self.assertEqual(
            prepare_latex(r"$f\tag{\textasteriskcentered}$; (\textasteriskcentered{})."),
            r"$f\tag{*}$; (*).",
        )
        self.assertEqual(prepare_latex(r"\textasteriskcenteredextra"),
                         r"\textasteriskcenteredextra")

    def test_define_macro_is_preserved_as_bold_text(self):
        self.assertEqual(
            prepare_latex(r"the \define{addition operation}"),
            r"the \textbf{addition operation}",
        )

    def test_align_intertext_becomes_prose_between_displays(self):
        source = r"""\begin{align*}
a & = b
\intertext{Text with \define{nested content}.}
c & = d
\end{align*}"""
        prepared = prepare_latex(source)
        self.assertEqual(prepared.count(r"\begin{align*}"), 2)
        self.assertIn(r"Text with \textbf{nested content}.", prepared)
        self.assertNotIn(r"\intertext", prepared)

    def test_samepage_layout_environment_is_transparent(self):
        self.assertEqual(
            prepare_latex(
                r"\begin{samepage}%\begin{align*}a=b\end{align*}\end{samepage}%"
            ),
            r"\begin{align*}a=b\end{align*}",
        )

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is not installed")
    def test_define_content_survives_pandoc(self):
        result = latex_to_gfm(r"the \define{addition operation}")
        self.assertIn("**addition operation**", result)

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is not installed")
    def test_markdown_preview_formats_content_without_running_raw_html(self):
        result = markdown_to_safe_html(
            "## Definition\n\n**Bold** and `code`.\n\n<script>alert(1)</script>"
        )
        self.assertIn("<h2", result)
        self.assertIn("<strong>Bold</strong>", result)
        self.assertNotIn("<script>", result)

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is not installed")
    def test_multiple_markdown_previews_are_rendered_independently(self):
        results = markdown_fragments_to_safe_html(["**First**", "## Second"])
        self.assertEqual(len(results), 2)
        self.assertIn("<strong>First</strong>", results[0])
        self.assertNotIn("Second", results[0])
        self.assertIn("<h2", results[1])


if __name__ == "__main__":
    unittest.main()
