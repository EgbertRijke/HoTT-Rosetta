import unittest
from pathlib import Path

from rosetta.latex import inventory
from rosetta.render import _structure_theorem_divs, render_section


ROOT = Path(__file__).resolve().parent.parent


class RenderTests(unittest.TestCase):
    def test_theorem_div_gets_expected_heading(self):
        class Item:
            kind = "Definition"
            number = "3.2.1"
            stable_id = "definition-3.2.1"
            label = None

        result = _structure_theorem_divs(
            '<div class="defn">\nBody.\n</div>\n', [Item()]
        )
        self.assertEqual(
            result,
            "## Definition 3.2.1\n\n"
            "<!-- rosetta-item: definition-3.2.1 -->\n\nBody.\n\n"
            "<!-- rosetta-item-end: definition-3.2.1 -->\n",
        )

    def test_chapter_3_section_2_preserves_structure(self):
        section = inventory(ROOT / "book")[2]
        result = render_section(section.path, 3, 2)
        self.assertIn("# Section 3.2 Addition on the natural numbers", result)
        self.assertIn("## Definition 3.2.1", result)
        self.assertIn("## Remark 3.2.2", result)
        self.assertIn("**addition operation**", result)
        self.assertIn("rosetta-proof-tree:", result)
        self.assertIn("Proof tree (automatic faithful draft)", result)

    def test_construction_environment_gets_heading(self):
        result = _structure_theorem_divs(
            '<div class="constr">\nBody.\n</div>\n', []
        )
        self.assertEqual(result, "### Construction\n\nBody.\n")


if __name__ == "__main__":
    unittest.main()
