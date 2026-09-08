import unittest
from pathlib import Path

from rosetta.latex import exercise_bodies, inventory, section_introduction, subsection_body
from rosetta.render import _structure_theorem_divs, render_fragment, render_section


ROOT = Path(__file__).resolve().parent.parent


class RenderTests(unittest.TestCase):
    def test_active_citation_keys_survive_in_all_document_kinds(self):
        import re

        kinds = set()
        citation_count = 0
        for chapter in inventory(ROOT / "book"):
            fragments = [("chapter", section_introduction(chapter.path))]
            fragments.extend(
                ("section", subsection_body(chapter.path, number)[1])
                for number in range(1, len(chapter.subsections) + 1)
            )
            fragments.extend(("exercise", body) for body in exercise_bodies(chapter.path))
            for kind, source in fragments:
                keys = re.findall(r"\\cite\s*\{([^{}]+)\}", source)
                if not keys:
                    continue
                kinds.add(kind)
                rendered = render_fragment(chapter.path, source)
                for group in keys:
                    expected = "citation: " + ", ".join(
                        f"`{key.strip()}`" for key in group.split(",")
                    )
                    self.assertIn(expected, rendered)
                    citation_count += 1
        self.assertEqual(kinds, {"chapter", "section", "exercise"})
        self.assertGreaterEqual(citation_count, 14)

    def test_mapping_truncations_keeps_citation_delimiters_and_diagram_ids(self):
        result = render_section(ROOT / "book" / "propositional-truncation.tex", 14, 4)
        self.assertIn("citation: `Kraus`", result)
        self.assertIn("h:‖A‖→Σ(b:B) ‖Σ(x:A) f(x)=b‖", result)
        self.assertNotIn(r"\|", result)
        for marker in ("e3422d10b67e", "44459fe1a1c2", "7e7385271393"):
            self.assertIn(f"rosetta-diagram: {marker};", result)
        finite = render_section(ROOT / "book" / "finite-types.tex", 16, 3)
        self.assertIn("`‖Π(x:A) B(x)‖`", finite)
        self.assertNotIn(r"\|", finite)

    def test_propositional_logic_table_preserves_all_eight_interpretations(self):
        result = render_section(ROOT / "book" / "propositional-truncation.tex", 14, 3)
        rows = [line for line in result.splitlines() if line.startswith("| `")]
        import re
        self.assertEqual([re.findall(r"`([^`]+)`", row) for row in rows], [
            ["⊤", "unit"], ["⊥", "empty"], ["P⇒ Q", "P→ Q"],
            ["P∧ Q", "P× Q"], ["P∨ Q", "‖P+Q‖"], ["P⇔ Q", "P↔ Q"],
            ["∃_{(x:A)}P(x)", "‖Σ(x:A) P(x)‖"],
            ["∀_{(x:A)}P(x)", "Π(x:A) P(x)"],
        ])
        self.assertIn("Exercise 13.8", result)
        self.assertIn("Theorem 13.3.1", result)
        self.assertEqual(result.count("rosetta-diagram:"), 2)

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
