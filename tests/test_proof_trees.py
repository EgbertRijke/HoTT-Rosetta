import unittest

from rosetta.proof_trees import render_proof_tree, render_proof_tree_markdown


class ProofTreeTests(unittest.TestCase):
    def test_binary_tree_preserves_premises_and_conclusion(self):
        draft = render_proof_tree(
            r"\AxiomC{$a:A$}\AxiomC{$f:A\to B$}\BinaryInfC{$f(a):B$}"
        )
        self.assertIn("a:A", draft.art)
        self.assertIn("f:A→ B", draft.art)
        self.assertIn("f(a):B", draft.art)
        self.assertIn("─", draft.art)

    def test_review_marker_is_stable(self):
        rendered = render_proof_tree_markdown(r"\AxiomC{$A$}\UnaryInfC{$B$}")
        self.assertIn("rosetta-proof-tree:", rendered)
        self.assertIn("review: pending", rendered)

    def test_nested_universe_computation_conclusion_is_preserved(self):
        draft = render_proof_tree(
            r"\AxiomC{}\UnaryInfC{$X:\UU\vdash "
            r"\mathcal{T}(\brckcheck{X})\jdeq\brck{\mathcal{T}(X)}~\type$}"
        )
        self.assertIn("X:𝒰⊢ T(‖X‖̌)≐‖T(X)‖ type", draft.art)
        self.assertNotIn("$", draft.art)

    def test_external_punctuation_and_escaped_braces(self):
        draft = render_proof_tree(
            r"\AxiomC{$\{x\}$}\UnaryInfC{$\brck{\mathcal{T}(X)}$.}"
        )
        self.assertIn("{x}", draft.art)
        self.assertIn("‖T(X)‖", draft.art)
        self.assertNotIn("$", draft.art)

    def test_incomplete_rule_argument_is_rejected_not_silently_dropped(self):
        for body in (r"\AxiomC{$A$}\UnaryInfC", r"\AxiomC{$A$}\UnaryInfC{$B$"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                render_proof_tree(body)


if __name__ == "__main__":
    unittest.main()
