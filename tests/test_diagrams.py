import unittest

from rosetta.diagrams import render_tikzcd
from rosetta.math_text import normalize_math, normalize_markdown_math


class DiagramTests(unittest.TestCase):
    def test_spacing_options_are_not_mathematical_nodes(self):
        source = r"""\begin{tikzcd}
A \arrow[r,"f"] &[4em] B \arrow[r,"g"] &[2.5em] C \\
[1ex] &[-2em] D &[-2em]
\end{tikzcd}"""
        draft = render_tikzcd(source, normalize_math)
        self.assertIn("A --f--> B", draft.art)
        self.assertIn("B --g--> C", draft.art)
        self.assertIn("[D]", draft.art)
        for option in ("4em", "2.5em", "-2em", "1ex"):
            self.assertNotIn(option, draft.art)

    def test_bracketed_mathematics_is_preserved(self):
        source = r"""\begin{tikzcd}
A \arrow[r,"f"] & {[0,1]}
\end{tikzcd}"""
        draft = render_tikzcd(source, normalize_math)
        self.assertIn("A --f--> [0,1]", draft.art)

    def test_square_matrix_and_arrows_are_preserved(self):
        source = r"""\begin{tikzcd}
A \arrow[r,"f"] \arrow[d,swap,"g"] & B \arrow[d,"h"] \\
C \arrow[r,swap,"k"] & D
\end{tikzcd}"""
        draft = render_tikzcd(source, normalize_math)
        self.assertEqual(draft.description, "square-shaped diagram")
        self.assertIn("[A]", draft.art)
        self.assertIn("[D]", draft.art)
        self.assertIn("A --f--> B", draft.art)
        self.assertIn("A --g--> C", draft.art)
        self.assertEqual(len(draft.arrows), 4)

    def test_triangle_shape_is_described(self):
        source = r"""\begin{tikzcd}
& B \arrow[dl,"f"] \arrow[dr,"g"] \\
A & & C
\end{tikzcd}"""
        draft = render_tikzcd(source, normalize_math)
        self.assertEqual(draft.description, "triangle-shaped diagram")

    def test_compact_triangle_shape_is_described(self):
        source = r"""\begin{tikzcd}
A \arrow[d,"f"] \arrow[dr,"g"] \\
B \arrow[r,"h"] & C.
\end{tikzcd}"""
        draft = render_tikzcd(source, normalize_math)
        self.assertEqual(draft.description, "triangle-shaped diagram")
        self.assertIn("[C]", draft.art)

    def test_markdown_has_review_marker_and_caption(self):
        markdown = r"""``` math
\begin{tikzcd}
A \arrow[r,"f"] & B
\end{tikzcd}
```"""
        result = normalize_markdown_math(markdown)
        self.assertIn("<!-- rosetta-diagram:", result)
        self.assertIn("review: pending", result)
        self.assertIn("*Linear diagram (automatic draft).*", result)
        self.assertNotIn(r"\begin{tikzcd}", result)


if __name__ == "__main__":
    unittest.main()
