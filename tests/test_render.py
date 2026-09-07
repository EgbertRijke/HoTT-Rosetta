import unittest
from pathlib import Path

from rosetta.latex import inventory
from rosetta.render import _structure_theorem_divs, render_section


ROOT = Path(__file__).resolve().parent.parent


class RenderTests(unittest.TestCase):
    def test_truncation_universe_rules_preserve_nested_conclusions(self):
        result = render_section(ROOT / "book" / "propositional-truncation.tex", 14, 2)
        self.assertIn("Γ⊢ ‖A‖ type", result)
        self.assertIn("X:𝒰⊢ ‖X‖̌:𝒰", result)
        self.assertIn("X:𝒰⊢ T(‖X‖̌)≐‖T(X)‖ type", result)
        self.assertEqual(result.count("rosetta-proof-tree:"), 3)
        self.assertNotIn(r"\brckcheck", result)
        self.assertNotIn("$Γ", result)

    def test_strong_induction_keeps_asterisk_reference_and_both_case_displays(self):
        result = render_section(ROOT / "book" / "funext.tex", 13, 5)
        self.assertIn("mentioned in (\\*).", result)
        self.assertIn("f : (m≤ n+1)→ (m≤ n)+(m=n+1)(*)", result)
        self.assertEqual(result.count("cases {"), 2)
        for branch in ("H(m,q) if x≐inl(q)", "p_S(n,H) if x≐inr(refl).",
                       "s̃(n,m,p) if m≤ n", "p_S(n,s̃(n)) if m=n+1."):
            self.assertIn(branch, result)
        self.assertNotIn(r"\begin{cases}", result)
        self.assertNotIn(r"\end{cases}", result)

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

    def test_function_extensionality_keeps_labelled_maps_and_the_axiom_rule(self):
        result = render_section(ROOT / "book" / "funext.tex", 13, 1)
        self.assertIn("⟶[i] (Π(x:A) Σ(b:B(x)) f(x)=b)", result)
        self.assertIn("⟶[r] (Σ(g:Π(x:A) B(x)) f~ g)", result)
        self.assertIn("Γ,x:A⊢ B(x) type", result)
        self.assertIn("Γ⊢funext:is-equiv(htpy-eq_{f,g})", result)
        self.assertIn("<!-- rosetta-proof-tree: 828a985f9fa9; review: pending -->", result)
        self.assertNotIn(r"\stackrel", result)
        self.assertNotIn(r"\longrightarrow", result)
        self.assertNotIn(r"\type", result)

    def test_construction_environment_gets_heading(self):
        result = _structure_theorem_divs(
            '<div class="constr">\nBody.\n</div>\n', []
        )
        self.assertEqual(result, "### Construction\n\nBody.\n")


if __name__ == "__main__":
    unittest.main()
