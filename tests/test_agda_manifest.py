import json
import tempfile
import unittest
from pathlib import Path

from rosetta.agda_manifest import (
    AgdaBlock,
    inject_agda_blocks,
    load_manifest,
    source_digest,
    verify_block_source,
)


class AgdaManifestTests(unittest.TestCase):
    def test_repository_manifest_is_valid(self):
        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        self.assertTrue(blocks)
        self.assertEqual(len(blocks), len({block.block_id for block in blocks}))

    def test_manifest_includes_local_blocks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            block = {
                "block_id": "included", "provenance_kind": "exact",
                "item_id": "definition-1.1.1", "destination": "example",
                "source_file": "example", "source_commit": "abc",
                "source_start_line": 1, "source_end_line": 1,
                "source_sha256": "abc", "code": "example", "order": 0,
                "imports": [],
            }
            (root / "included.json").write_text(json.dumps({"format_version": 1, "blocks": [block]}))
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"format_version": 1, "blocks": [], "includes": ["included.json"]}))
            self.assertEqual([item.block_id for item in load_manifest(manifest)], ["included"])

    def test_manifest_include_cycles_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "a.json").write_text(json.dumps({"format_version": 1, "blocks": [], "includes": ["b.json"]}))
            (root / "b.json").write_text(json.dumps({"format_version": 1, "blocks": [], "includes": ["a.json"]}))
            with self.assertRaisesRegex(ValueError, "cycle"):
                load_manifest(root / "a.json")

    def test_chapters_three_through_six_ready_blocks_are_generated(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [
            block for block in blocks
            if block.destination.startswith(
                tuple(f"{kind}-{chapter}-" for chapter in range(3, 7) for kind in ("section", "exercise"))
            )
        ]
        directory = rosetta_directory(root)
        for block in selected:
            document = (directory / block.destination).read_text()
            marker = f"<!-- rosetta-agda-block: {block.block_id} -->"
            self.assertEqual(
                marker in document,
                block.conversion_status in {"ready", "exercise"},
            )

    def test_chapter_seven_ready_blocks_are_generated(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [
            block for block in blocks
            if block.destination.startswith(("section-7-", "exercise-7-"))
        ]
        directory = rosetta_directory(root)
        for block in selected:
            document = (directory / block.destination).read_text()
            marker = f"<!-- rosetta-agda-block: {block.block_id} -->"
            self.assertEqual(
                marker in document,
                block.conversion_status in {"ready", "exercise"},
            )

    def test_duplicate_ids_are_rejected(self):
        block = {
            "block_id": "addition",
            "provenance_kind": "exact",
            "item_id": "definition-3.2.1",
            "destination": "section-3-2-example",
            "source_file": "example.lagda.md",
            "source_commit": "abc",
            "source_start_line": 1,
            "source_end_line": 1,
            "source_sha256": "abc",
            "code": "example : Set",
            "order": 1,
            "imports": [],
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            path.write_text(json.dumps({"format_version": 1, "blocks": [block, block]}))
            with self.assertRaisesRegex(ValueError, "duplicate"):
                load_manifest(path)

    def test_source_hash_uses_inclusive_lines(self):
        self.assertEqual(
            source_digest(["one\n", "two\n", "three\n"], 2, 2),
            "27dd8ed44a83ff94d557f9fd0412ed5a8cbca69ea04922d88c01184a07300a5a",
        )

    def test_repository_block_matches_upstream_exactly(self):
        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        self.assertEqual(
            [
                error
                for block in blocks
                for error in verify_block_source(
                    block, root / "external" / "agda-unimath"
                )
            ],
            [],
        )

    def test_family_equivalence_blocks_stay_in_their_numbered_items(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [
            block for block in blocks
            if block.destination.startswith("section-11-1-")
            or block.block_id in {
                "definition-9.2.1-retract-data",
                "corollary-9.2.8-inverse-equivalence",
            }
        ]
        self.assertEqual(len(selected), 14)
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)

    def test_fundamental_theorem_blocks_stay_in_their_numbered_items(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [
            block for block in blocks
            if block.destination.startswith("section-11-2-")
        ]
        self.assertEqual(len(selected), 7)
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)

    def test_natural_number_equality_proof_stays_in_its_theorem(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        block = next(
            block for block in load_manifest(root / "data" / "agda-blocks.json")
            if block.block_id == "theorem-11.3.1-equality-natural-numbers"
        )
        document = (rosetta_directory(root) / block.destination).read_text()
        start = document.index("<!-- rosetta-item: theorem-11.3.1;")
        end = document.index("<!-- rosetta-item-end: theorem-11.3.1 -->")
        declarations = [
            document.index(name + " :") for name in
            ("map-total-Eq-ℕ", "is-torsorial-Eq-ℕ", "is-equiv-Eq-eq-ℕ")
        ]
        self.assertEqual(declarations, sorted(declarations))
        self.assertLess(start, declarations[0])
        self.assertLess(declarations[-1], end)

    def test_embedding_blocks_stay_in_their_numbered_items(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        selected = [
            block for block in load_manifest(root / "data" / "agda-blocks.json")
            if block.destination.startswith("section-11-4-")
        ]
        self.assertEqual(len(selected), 4)
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)

    def test_coproduct_identity_proof_follows_its_delayed_proof(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        selected = [
            block for block in load_manifest(root / "data" / "agda-blocks.json")
            if block.destination.startswith("section-11-5-")
        ]
        self.assertEqual(len(selected), 8)
        for block in selected:
            document = (rosetta_directory(root) / block.destination).read_text()
            position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
            if block.item_id == "theorem-11.5.1":
                proof = document.index("<!-- rosetta-item: subheading-11.5-proof-2 -->")
                contraction = document.index("  is-torsorial-Eq-coproduct :")
                self.assertLess(contraction, proof)
                self.assertLess(proof, position)
                self.assertLess(document.index(block.after_text), position)
                for case in ("inl-inl", "inl-inr", "inr-inl", "inr-inr"):
                    self.assertGreater(document.index(f"    compute-eq-coproduct-{case} :"), position)
            else:
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        self.assertFalse(document.endswith("\n\n"))

    def test_structure_identity_conditions_stay_in_their_numbered_items(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        selected = [
            block for block in load_manifest(root / "data" / "agda-blocks.json")
            if block.destination.startswith("section-11-6-")
        ]
        self.assertEqual(len(selected), 10)
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        declarations = [
            document.index(name + " :") for name in (
                "is-dependent-identity-system",
                "  interchange-Σ-Σ",
                "  equiv-total-Eq-structure",
                "  is-torsorial-Eq-structure",
                "  is-torsorial-Eq-structure'",
                "  dependent-equiv-from-contr",
                "  dependent-contr-from-equiv",
                "  structure-equiv-from-contr",
                "  structure-contr-from-equiv",
                "  dependent-contr-from-identity-system",
                "  structure-contr-from-identity-system",
                "  dependent-identity-system-from-contr",
                "  structure-identity-system-from-contr",
                "    structure-identity-principle",
            )
        ]
        self.assertEqual(declarations, sorted(declarations))
        example = selected[-1]
        self.assertEqual(example.item_id, "example-11.6.3")
        if example.conversion_status == "exercise":
            self.assertNotIn("  equiv-fiber-ap-eq-fiber :", document)
        else:
            self.assertIn("  equiv-fiber-ap-eq-fiber :", document)

    def test_proposition_blocks_cover_the_four_conditions_in_order(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [block for block in blocks if block.destination.startswith("section-12-1-")]
        self.assertEqual(len(selected), 10)
        self.assertEqual(
            {block.item_id for block in selected},
            {"definition-12.1.1", "example-12.1.2", "proposition-12.1.3", "proposition-12.1.4"},
        )
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        declarations = [document.index(name + " :") for name in (
            "is-prop", "Prop", "  is-prop-unit", "  is-prop-empty",
            "  all-elements-equal", "  is-proof-irrelevant",
            "  is-subterminal", "    is-emb-is-emb",
            "    is-subterminal-is-proof-irrelevant", "    is-prop-is-subterminal",
            "    is-equiv-has-converse-is-prop", "  equiv-iff'", "iff-equiv",
        )]
        self.assertEqual(declarations, sorted(declarations))
        self.assertNotIn("postulate", document)
        self.assertNotIn("open import foundation", document)
        self.assertNotIn("section-13-", document)
        exercise = next(block for block in blocks if block.block_id == "exercise-10-1-contractible-identities")
        self.assertEqual(exercise.item_id, "exercise-10-1")
        self.assertFalse(any(imported.startswith("section-12-") for imported in exercise.imports))

    def test_subtype_blocks_cover_both_criteria_and_keep_projection_fibers_earlier(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [block for block in blocks if block.destination.startswith("section-12-2-")]
        self.assertEqual(len(selected), 8)
        self.assertEqual(
            {block.item_id for block in selected},
            {"definition-12.2.1", "lemma-12.2.2", "theorem-12.2.3", "corollary-12.2.4"},
        )
        document = (rosetta_directory(root) / selected[0].destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        names = (
            "  is-subtype", "subtype", "    is-prop-equiv", "    is-prop-equiv'",
            "  is-prop-map", "    is-prop-map-inclusion-subtype",
            "    is-emb-inclusion-subtype", "  equiv-ap-inclusion-subtype",
            "    is-subtype-is-emb-pr1", "  is-emb-pr1-is-subtype",
        )
        positions = [document.index(name + " :") for name in names]
        self.assertEqual(positions, sorted(positions))
        theorem = next(block for block in selected if block.block_id ==
                       "theorem-12.2.3-embeddings-propositional-fibers")
        for name in ("is-emb-is-prop-map", "is-prop-map-is-emb"):
            self.assertIn(name + " :", theorem.code)
            if theorem.conversion_status == "exercise":
                self.assertNotIn(name + " :", document)
            else:
                self.assertIn(name + " :", document)
        self.assertNotIn("postulate", document)
        self.assertNotIn("open import foundation", document)
        self.assertNotIn("section-13-", document)
        exercise = next(block for block in blocks if block.block_id ==
                        "exercise-10-7-projection-fiber-equivalence")
        self.assertEqual(exercise.item_id, "exercise-10-7")
        self.assertIn("equiv-fiber-pr1 :", exercise.code)
        self.assertFalse(any(imported.startswith("section-12-") for imported in exercise.imports))
        self.assertNotIn("equiv-fiber-pr1 :", document)

    def test_set_blocks_cover_all_items_and_the_arbitrary_map_assertion(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [block for block in blocks if block.destination.startswith("section-12-3-")]
        self.assertEqual(len(selected), 10)
        self.assertEqual(
            {block.item_id for block in selected},
            {"definition-12.3.1", "example-12.3.2", "proposition-12.3.3",
             "theorem-12.3.4", "theorem-12.3.5"},
        )
        document = (rosetta_directory(root) / selected[0].destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        names = (
            "is-set", "  is-prop-Eq-ℕ", "  is-set-ℕ", "instance-axiom-K",
            "    is-set-axiom-K'", "    is-set-axiom-K", "    axiom-K-is-set",
            "    is-equiv-prop-in-id", "    is-set-prop-in-id", "    is-equiv-id-in-prop",
            "  Eq-has-decidable-equality'", "  refl-Eq-has-decidable-equality",
            "  eq-Eq-has-decidable-equality", "    is-set-has-decidable-equality",
        )
        positions = [document.index(name + " :") for name in names]
        self.assertEqual(positions, sorted(positions))
        example = next(block for block in selected if block.block_id ==
                       "example-12.3.2-natural-numbers-are-a-set")
        self.assertIn("is-prop-is-equiv (is-equiv-Eq-eq-ℕ", example.code)
        self.assertNotIn("is-set-prop-in-id", example.code)
        arbitrary = next(block for block in selected if block.block_id ==
                         "theorem-12.3.4-arbitrary-identity-maps")
        self.assertIn("(f : (x y : A) → x ＝ y → R x y)", arbitrary.code)
        self.assertIn("is-equiv (f x y)", arbitrary.code)
        self.assertIn("( f x)", arbitrary.code)
        based = next(block for block in selected if block.block_id ==
                     "theorem-12.3.4-propositional-identity-relation")
        if based.conversion_status == "exercise":
            self.assertNotIn("is-equiv-prop-in-based-id :", document)
        else:
            self.assertIn("is-equiv-prop-in-based-id :", document)
        self.assertNotIn("postulate", document)
        self.assertNotIn("open import foundation", document)
        self.assertNotIn("section-13-", document)

    def test_general_truncation_blocks_cover_items_and_delay_lift_transfer(self):
        import re
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [b for b in blocks if b.destination.startswith("section-12-4-")]
        self.assertEqual(len(selected), 17)
        self.assertEqual(
            {b.item_id for b in selected},
            {"section-12.4", "definition-12.4.1", "remark-12.4.2",
             "proposition-12.4.3", "corollary-12.4.4", "proposition-12.4.5",
             "corollary-12.4.6", "theorem-12.4.7"},
        )
        document = (rosetta_directory(root) / selected[0].destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = (document.index("## Definition 12.4.1")
                       if block.item_id == "section-12.4" else
                       document.index(f"<!-- rosetta-item-end: {block.item_id} -->"))
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        names = ("truncation-level-ℕ", "is-trunc", "is-proper-succ-trunc",
                 "Truncated-Type", "  is-trunc-map", "compute-raise",
                 "  is-trunc-succ-is-trunc", "  is-trunc-Id",
                 "  is-trunc-retract-of", "  is-trunc-is-equiv",
                 "  is-trunc-equiv'", "  is-trunc-raise",
                 "  is-trunc-is-trunc-raise", "  is-trunc-is-emb")
        positions = [document.index(name + " :") for name in names]
        self.assertEqual(positions, sorted(positions))
        self.assertIn("Σ (is-trunc (succ-𝕋 k) A) (λ _ → is-empty (is-trunc k A))", document)
        self.assertIn("Agda universe representation: equivalent lifted types", document)
        self.assertIn("Remark 12.4.2 revisited", document)
        theorem = next(b for b in selected if b.item_id == "theorem-12.4.7")
        self.assertIn("is-trunc-map-succ-is-trunc-map-ap :", theorem.code)
        self.assertIn("is-trunc-map-ap-is-trunc-map-succ :", theorem.code)
        self.assertIn("equiv-fiber-ap-eq-fiber", theorem.code)
        self.assertIn("is-equiv-eq-fiber-fiber-ap", theorem.code)
        if theorem.conversion_status == "exercise":
            self.assertNotIn("is-trunc-map-succ-is-trunc-map-ap :", document)
        else:
            self.assertIn("is-trunc-map-ap-is-trunc-map-succ :", document)
        self.assertNotIn("postulate", document)
        self.assertNotIn("open import foundation", document)
        self.assertNotIn("section-13-", document)

        prose = document
        for block in selected:
            if block.display_heading:
                prose = prose.replace("### " + block.display_heading, "")
        prose = re.sub(r"^```agda\n.*?^```\s*", "", prose, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        expected = render_section(root / "book" / "hierarchy.tex", 12, 4)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(expected))

    def test_identity_retract_exercise_does_not_import_its_truncation_consumer(self):
        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [b for b in blocks if b.destination.startswith("exercise-12-8-")]
        self.assertEqual(len(selected), 2)
        self.assertIn("retraction-ap :", selected[0].code)
        self.assertIn("retract-eq :", selected[1].code)
        for block in selected:
            self.assertFalse(any(i.startswith("section-12-") for i in block.imports))
            self.assertNotIn("is-trunc", block.code)

    def test_function_extensionality_proofs_precede_the_explicit_assumption(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 13, 1)
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [b for b in blocks if b.destination == destination]
        self.assertEqual(len(selected), 20)
        self.assertEqual(
            {b.item_id for b in selected},
            {"proposition-13.1.1", "theorem-13.1.2", "axiom-13.1.3",
             "theorem-13.1.5", "corollary-13.1.6", "remark-13.1.7"},
        )
        document = (rosetta_directory(root) / destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
        before_axiom = document[:document.index("## Axiom 13.1.3")]
        self.assertNotIn("postulate", before_axiom)
        self.assertNotRegex(before_axiom, r"(?m)^\s*funext\s*:")
        self.assertNotRegex(before_axiom, r"(?m)^\s*eq-htpy\s*:")
        self.assertIn("fundamental-theorem-id H (λ g → htpy-eq", before_axiom)
        self.assertIn("fundamental-theorem-id' (λ g → htpy-eq", before_axiom)
        self.assertIn("is-identity-system-is-contr f refl-htpy", before_axiom)
        self.assertIn("is-torsorial-is-identity-system f refl-htpy", before_axiom)
        self.assertIn("weak-funext-funext funext A B", before_axiom)
        self.assertIn("funext-weak-funext weak-funext", before_axiom)
        self.assertIn("( weak-funext A", before_axiom)
        self.assertNotIn("( is-torsorial-htpy f)", before_axiom)
        axiom = next(b for b in selected if b.block_id ==
                     "axiom-13.1.3-assumed-coherent-function-extensionality")
        self.assertEqual(document.count("  postulate"), 1)
        for name in ("eq-htpy", "is-section-eq-htpy", "is-retraction-eq-htpy'", "coh-eq-htpy'"):
            self.assertIn("    " + name + " :", axiom.code)
        names = ("funext", "  equiv-funext", "  is-contr-Π", "  is-trunc-Π",
                 "  is-prop-Π", "  is-trunc-function-type", "  is-prop-function-type", "is-prop-neg")
        positions = [re.search(r"(?m)^" + re.escape(name) + " :", document).start()
                     for name in names]
        self.assertEqual(positions, sorted(positions))
        self.assertNotIn("open import foundation", document)
        self.assertNotIn("open import section-14-", document)
        self.assertIn("Γ⊢funext:is-equiv(htpy-eq_{f,g})", document)
        prose = document
        for block in selected:
            if block.display_heading:
                prose = prose.replace("### " + block.display_heading, "")
        prose = re.sub(r"^```agda\n.*?^```\s*", "", prose, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        expected = render_section(root / "book" / "funext.tex", 13, 1)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(expected))

    def test_dependent_choice_accounts_for_the_intervening_equivalence_and_identity_system(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 13, 2)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 7)
        self.assertEqual({b.item_id for b in selected},
                         {"theorem-13.2.1", "corollary-13.2.2", "corollary-13.2.3",
                          "theorem-13.2.4", "section-13.2"})
        document = (rosetta_directory(root) / destination).read_text()
        for block in selected:
            if block.item_id == "section-13.2":
                self.assertIn("Π(b:B) fib(f, b)", block.after_text)
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(document.index("<!-- rosetta-item-end: corollary-13.2.2 -->"), position)
                self.assertLess(position, document.index("## Corollary 13.2.3"))
                continue
            with self.subTest(block=block.block_id):
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(document.index(f"<!-- rosetta-item: {block.item_id}"), position)
                self.assertLess(position, document.index(f"<!-- rosetta-item-end: {block.item_id} -->"))
        for name in ("map-distributive-Π-Σ", "map-inv-distributive-Π-Σ",
                     "is-section-map-inv-distributive-Π-Σ", "is-retraction-map-inv-distributive-Π-Σ",
                     "distributive-Π-Σ", "inv-distributive-Π-Σ", "equiv-mapping-into-Σ",
                     "equiv-Π-fiber-section", "equiv-Π-section-pr1", "is-torsorial-Eq-Π",
                     "is-identity-system-Π"):
            self.assertRegex(document, r"(?m)^\s*" + re.escape(name) + r" :")
        self.assertIn("is-identity-system-is-contr f e", document)
        self.assertIn("is-torsorial-is-identity-system (f x) (e x) (H x)", document)
        self.assertIn("( equiv-right-swap-Σ) ∘e", document)
        self.assertIn("( equiv-Σ-equiv-base", document)
        self.assertIn("( left-unit-law-Σ-is-contr", document)
        self.assertIn("open import exercise-9-4-three-for-two-equivalences", document)
        self.assertIn("Agda record-Σ presentation (judgmental η)", document)
        self.assertIn("However, it is *not* the case", document)
        self.assertIn("Therefore we obtain the required homotopy by function extensionality", document)
        self.assertNotIn("postulate", document)
        self.assertNotIn("open import foundation", document)
        prose = document
        for block in selected:
            if block.display_heading:
                prose = prose.replace("### " + block.display_heading, "")
        prose = re.sub(r"^```agda\n.*?^```\s*", "", prose, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        expected = render_section(root / "book" / "funext.tex", 13, 2)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(expected))

    def test_only_the_needed_sigma_swap_exercise_part_is_curated(self):
        from rosetta.file_registry import registered_filename

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "exercise", 9, 5)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 1)
        block = selected[0]
        self.assertEqual(block.display_heading, "Part (b): swapping dependent families")
        for name in ("map-right-swap-Σ", "map-inv-right-swap-Σ",
                     "is-section-map-inv-right-swap-Σ", "is-retraction-map-inv-right-swap-Σ",
                     "is-equiv-map-right-swap-Σ", "equiv-right-swap-Σ"):
            self.assertIn(name + " :", block.code)
        self.assertNotIn("left-swap", block.code)
        self.assertFalse(any(i.startswith("section-13-") for i in block.imports))
        gaps = json.loads((root / "data" / "agda-gaps.json").read_text())["items"]
        self.assertTrue(any(g["item_id"] == "exercise-9-5-a" for g in gaps))
        self.assertTrue(any(g["item_id"] == "theorem-13.2.1-judgmental-sigma-eta" for g in gaps))

    def test_universal_properties_keep_induction_proofs_and_ordinary_specializations(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 13, 3)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 5)
        self.assertEqual({b.item_id for b in selected},
                         {"theorem-13.3.1", "corollary-13.3.2", "theorem-13.3.3"})
        document = (rosetta_directory(root) / destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(document.index(f"<!-- rosetta-item: {block.item_id}"), position)
                self.assertLess(position, document.index(f"<!-- rosetta-item-end: {block.item_id} -->"))
        sigma = next(b for b in selected if b.block_id ==
                     "theorem-13.3.1-dependent-universal-property-sigma")
        self.assertIn("pr1 (pr1 is-equiv-ev-pair) = ind-Σ", sigma.code)
        self.assertIn("pr2 (pr1 is-equiv-ev-pair) = refl-htpy", sigma.code)
        self.assertIn("pr1 (pr2 is-equiv-ev-pair) = ind-Σ", sigma.code)
        self.assertIn("eq-htpy (ind-Σ (λ x y → refl))", sigma.code)
        identity = next(b for b in selected if b.block_id ==
                        "theorem-13.3.3-dependent-universal-property-identity")
        self.assertEqual(identity.code.count("eq-htpy"), 2)
        self.assertIn("is-retraction-ev-refl = refl-htpy", identity.code)
        self.assertIn("( λ x' p' → ind-Id a _ (f a refl) x' p' ＝ f x' p')", identity.code)
        self.assertIn("is-equiv-is-invertible (ind-Id a B)", identity.code)
        for name in ("is-equiv-ev-pair-nondependent", "equiv-ev-pair-nondependent",
                     "is-equiv-ev-product", "equiv-ev-product",
                     "is-equiv-ev-refl-nondependent", "equiv-ev-refl-nondependent"):
            self.assertRegex(document, r"(?m)^\s*" + re.escape(name) + r" :")
        self.assertLess(document.index("  equiv-ev-pair :"),
                        document.index("  equiv-ev-pair-nondependent :"))
        self.assertLess(document.index("  equiv-ev-refl :"),
                        document.index("  equiv-ev-refl-nondependent :"))
        self.assertIn("(A × B → X) ≃ (A → B → X)", document)
        self.assertIn("open import section-4-6-dependent-pair-types", document)
        self.assertNotRegex(document, r"(?m)^\s*ev-pair :")
        self.assertNotIn("is-equiv-ind-Σ", document)
        self.assertNotIn("postulate", document)
        self.assertNotIn("univalence", document)
        self.assertNotIn("open import foundation", document)
        prose = document
        for block in selected:
            if block.display_heading:
                prose = prose.replace("### " + block.display_heading, "")
        prose = re.sub(r"^```agda\n.*?^```\s*", "", prose, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        expected = render_section(root / "book" / "funext.tex", 13, 3)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(expected))

    def test_precomposition_characterization_keeps_all_conditions_and_full_converse(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 13, 4)
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        selected = [b for b in blocks if b.destination == destination]
        self.assertEqual(len(selected), 11)
        self.assertEqual({b.item_id for b in selected}, {"theorem-13.4.1"})
        self.assertEqual([b.order for b in selected], list(range(11)))
        self.assertTrue(all(b.conversion_status == "ready" for b in selected))
        document = (rosetta_directory(root) / destination).read_text()
        for block in selected:
            with self.subTest(block=block.block_id):
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(document.index("<!-- rosetta-item: theorem-13.4.1"), position)
                self.assertLess(position, document.index("<!-- rosetta-item-end: theorem-13.4.1 -->"))
        code = "\n".join(b.code for b in selected)
        for name in ("precomp-Π", "precomp", "dependent-universal-property-equiv",
                     "universal-property-equiv", "is-equiv-precomp-Π-is-equiv",
                     "is-equiv-precomp-is-equiv-precomp-Π", "is-equiv-precomp-is-equiv",
                     "is-equiv-is-equiv-precomp", "is-equiv-is-equiv-precomp-Π",
                     "equiv-precomp-Π", "equiv-precomp"):
            self.assertRegex(code, r"(?m)^\s*" + re.escape(name) + r" :")
        self.assertIn("{l : Level} (C : B → Type l) → is-equiv (precomp-Π f C)", code)
        self.assertIn("{l : Level} (X : Type l) → is-equiv (precomp f X)", code)
        self.assertIn("is-equiv-precomp-is-equiv-precomp-Π f H C = H (λ _ → C)", code)
        coherent = next(b for b in selected if b.block_id.endswith("-coherent-proof"))
        self.assertIn("( λ s y → tr C (is-section-g y) (s (g y)))", coherent.code)
        self.assertIn("( ap (λ t → tr C t (s (g (f x)))) (coh x))", coherent.code)
        self.assertIn("tr-ap f (λ _ → id) (is-retraction-g x) (s (g (f x)))", coherent.code)
        self.assertIn("( apd s (is-retraction-g x))", coherent.code)
        self.assertIn("eq-htpy (λ y → apd s (is-section-g y))", coherent.code)
        self.assertIn("is-coherently-invertible-is-invertible\n          ( is-invertible-is-equiv H)", code)
        converse = next(b for b in selected if b.block_id.endswith("-equivalence-from-ordinary"))
        for name in ("map-inv-is-equiv-precomp", "is-section-map-inv-is-equiv-precomp",
                     "is-retraction-map-inv-is-equiv-precomp"):
            self.assertIn(name + " :", converse.code)
            self.assertIn("( " + name + ")", converse.code)
        self.assertIn("pr1 (center (is-contr-map-is-equiv (H A) id))", converse.code)
        self.assertIn("htpy-eq (pr2 (center (is-contr-map-is-equiv (H A) id)))", converse.code)
        self.assertIn("eq-is-contr'\n          ( is-contr-map-is-equiv (H B) f)", converse.code)
        self.assertIn("( λ g → f ∘ g)", converse.code)
        self.assertIn("( id , refl)", converse.code)
        self.assertIn("(H : universal-property-equiv f)", converse.code)
        transport = next(b for b in blocks if b.block_id == "section-9.3-transport-action")
        self.assertIn("tr-ap f g refl z = refl", transport.code)
        self.assertIn("open import " + transport.destination.removesuffix(".lagda.md"), document)
        for forbidden in ("substitution-law-tr", "path-split", "structured-type", "postulate"):
            self.assertNotIn(forbidden, code)
        self.assertNotRegex(code, r"(?m)^\s*tr-ap :")
        self.assertNotIn("open import foundation", document)
        prose = re.sub(r"^```agda\n.*?^```\s*", "", document, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(render_section(root / "book" / "funext.tex", 13, 4)))

    def test_strong_induction_preserves_lemmas_delayed_proof_and_computation_rules(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 13, 5)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 12)
        self.assertEqual({b.item_id for b in selected},
                         {"section-13.5", "theorem-13.5.1", "lemma-13.5.2", "lemma-13.5.3"})
        document = (rosetta_directory(root) / destination).read_text()
        code = "\n".join(b.code for b in selected)
        for name in ("□-≤-ℕ", "zero-strong-ind-ℕ", "eq-zero-strong-ind-ℕ",
                     "is-prop-leq-ℕ", "is-prop-leq-succ-cases", "equiv-leq-succ-cases",
                     "eq-cases-leq-succ", "cases-succ-strong-ind-ℕ", "succ-strong-ind-ℕ",
                     "htpy-succ-strong-ind-ℕ", "eq-succ-strong-ind-ℕ",
                     "induction-strong-ind-ℕ", "ε-□-≤-ℕ", "strong-ind-ℕ",
                     "compute-zero-strong-ind-ℕ", "compute-succ-strong-ind-ℕ",
                     "total-strong-ind-ℕ"):
            self.assertRegex(code, r"(?m)^\s*" + re.escape(name) + r" :")
        self.assertIn("zero-strong-ind-ℕ P p0 zero-ℕ t = p0", code)
        self.assertIn("(decide-leq-succ-ℕ m k p)", code)
        self.assertIn("contradiction-leq-ℕ k k (refl-leq-ℕ k)", code)
        self.assertIn("( is-set-ℕ m (succ-ℕ n))", code)
        self.assertIn("( preserves-leq-succ-ℕ m n)", code)
        self.assertIn("( leq-eq-ℕ m (succ-ℕ n))", code)
        self.assertIn("compute-zero-strong-ind-ℕ P p0 pS = refl", code)
        self.assertIn("strong-ind-ℕ P p0 pS (succ-ℕ n) ＝ pS n (λ m p → strong-ind-ℕ P p0 pS m)", code)
        self.assertIn("( eq-htpy (eq-htpy ∘ eq-compute-succ-strong-ind-ℕ P p0 pS n))", code)
        self.assertIn("( eq-cases-leq-succ (succ-ℕ n) n (refl-leq-ℕ n) (inr refl))", code)
        self.assertIn("pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-zero-strong-ind-ℕ P p0 pS", code)
        self.assertIn("pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-succ-strong-ind-ℕ P p0 pS", code)
        for forbidden in ("postulate", "cases-leq-succ-reflexive-leq-ℕ", "neg-succ-leq-ℕ :",
                          "decide-leq-succ-ℕ :", "cases-leq-succ-ℕ :"):
            self.assertNotIn(forbidden, code)
        self.assertNotIn("open import foundation", document)
        sequence = ["P̃(n)≔", "□-≤-ℕ :", "zero-strong-ind-ℕ :", "is-prop-leq-ℕ :",
                    "equiv-leq-succ-cases :", "succ-strong-ind-ℕ :",
                    "We are now ready to finish the proof of Theorem 13.5.1.",
                    "induction-strong-ind-ℕ :", "ε-□-≤-ℕ :", "strong-ind-ℕ :"]
        positions = []
        for entry in sequence:
            positions.append(re.search(r"(?m)^\s*" + re.escape(entry), document).start() if entry.endswith(" :")
                             else document.index(entry))
        self.assertEqual(positions, sorted(positions))
        final = next(b for b in selected if b.block_id.endswith("-and-computations"))
        self.assertLess(document.index(final.after_text), document.index("\nstrong-ind-ℕ :"))
        site = next(b for b in selected if b.block_id.endswith("-case-evaluation-identifications"))
        self.assertIn("equiv-inv-concat", site.code)
        self.assertIn("( eq-cases-leq-succ m n p x)", site.code)
        marker = f"<!-- rosetta-agda-block: {site.block_id} -->"
        if site.conversion_status == "exercise":
            self.assertRegex(document, re.escape(marker) + r"\s*```agda\s*```")
            self.assertNotIn("equiv-identifications-succ-strong-ind-ℕ :", document)
        else:
            self.assertIn("equiv-identifications-succ-strong-ind-ℕ :", document)
            self.assertIn("open import exercise-9-1-groupoid-operations-equivalences", document)
        prose = re.sub(r"^```agda\n.*?^```\s*", "", document, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(render_section(root / "book" / "funext.tex", 13, 5)))

    def test_propositional_truncation_specification_preserves_all_five_items(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.latex import inventory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        sources = inventory(root / "book")
        self.assertEqual(sources[13].path.name, "propositional-truncation.tex")
        self.assertEqual(sources[16].path.name, "univalence.tex")
        destination = registered_filename(root, "section", 14, 1)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 13)
        self.assertEqual({b.item_id for b in selected}, {
            "definition-14.1.1", "remark-14.1.2", "remark-14.1.3",
            "proposition-14.1.4", "remark-14.1.5"})
        document = (rosetta_directory(root) / destination).read_text()
        code = "\n".join(b.code for b in selected)
        for b in selected:
            position = document.index("<!-- rosetta-agda-block: " + b.block_id + " -->")
            self.assertLess(document.index("<!-- rosetta-item: " + b.item_id), position)
            self.assertLess(position, document.index("<!-- rosetta-item-end: " + b.item_id + " -->"))
        for name in ("precomp-Prop", "is-propositional-truncation",
                     "universal-property-propositional-truncation",
                     "universal-property-is-propositional-truncation",
                     "is-propositional-truncation-universal-property",
                     "map-is-propositional-truncation", "eq-is-propositional-truncation",
                     "extension-property-propositional-truncation",
                     "is-propositional-truncation-extension-property",
                     "extension-property-is-propositional-truncation",
                     "is-prop-equiv-is-prop", "equiv-is-propositional-truncation",
                     "is-ptruncation-is-ptruncation-is-equiv",
                     "is-ptruncation-is-equiv-is-ptruncation",
                     "is-prop-double-negation", "is-equiv-precomp-double-negation",
                     "equiv-precomp-double-negation"):
            self.assertRegex(code, r"(?m)^\s*" + re.escape(name) + " :")
        self.assertIn("(λ h → h ∘ f ＝ g)", code)
        self.assertNotIn("h ∘ f ~ g", code)
        self.assertIn("is-contr-map-is-equiv (H Q)", code)
        self.assertIn("is-equiv-is-contr-map (H Q)", code)
        self.assertIn("( map-is-propositional-truncation P f H P' f')", code)
        self.assertIn("( map-is-propositional-truncation P' f' K P f)", code)
        self.assertIn("( double-negation-kleisli-map)", code)
        for forbidden in ("postulate", "univalence", "unit-trunc-Prop",
                          "is-property-is-equiv", "is-prop-Σ :",
                          "double-negation-kleisli-map :"):
            self.assertNotIn(forbidden, code)
        self.assertNotIn("open import foundation", document)
        prose = re.sub(r"^```agda\n.*?^```\s*", "", document, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(render_section(sources[13].path, 14, 1)))

    def test_higher_inductive_truncations_preserve_assumptions_and_all_items(self):
        import re
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory
        from rosetta.render import render_section

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "section", 14, 2)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 18)
        self.assertEqual({b.item_id for b in selected}, {
            "section-14.2", "lemma-14.2.1", "definition-14.2.2",
            "remark-14.2.3", "theorem-14.2.4", "proposition-14.2.5"})
        document = (rosetta_directory(root) / destination).read_text()
        code = "\n".join(b.code for b in selected)
        assumptions = [b for b in selected if "postulate" in b.code]
        self.assertEqual(len(assumptions), 4)
        self.assertTrue(all(b.display_heading.startswith("Assumed") for b in assumptions))
        for b in assumptions:
            self.assertLess(document.index("<!-- rosetta-agda-block: " + b.block_id),
                            document.index("<!-- rosetta-item: theorem-14.2.4"))
        for b in selected:
            marker = "<!-- rosetta-agda-block: " + b.block_id + " -->"
            position = document.index(marker)
            if b.after_text:
                self.assertLess(document.index(b.after_text), position)
            else:
                self.assertLess(document.index("<!-- rosetta-item: " + b.item_id), position)
                self.assertLess(position, document.index("<!-- rosetta-item-end: " + b.item_id + " -->"))
        for name in ("type-trunc-Prop", "unit-trunc-Prop", "all-elements-equal-type-trunc-Prop",
                     "is-prop-type-trunc-Prop", "trunc-Prop",
                     "case-paths-induction-principle-propositional-truncation",
                     "induction-principle-propositional-truncation", "induction-trunc-Prop",
                     "ind-trunc-Prop'", "compute-ind-trunc-Prop'",
                     "is-prop-case-paths-induction-principle-propositional-truncation",
                     "case-paths-induction-principle-propositional-truncation-is-prop",
                     "ind-trunc-Prop", "compute-ind-trunc-Prop", "rec-trunc-Prop",
                     "is-propositional-truncation-trunc-Prop", "universal-property-trunc-Prop",
                     "map-trunc-Prop", "htpy-uniqueness-map-trunc-Prop",
                     "id-map-trunc-Prop", "preserves-comp-map-trunc-Prop"):
            self.assertRegex(code, r"(?m)^\s*" + re.escape(name) + " :")
        self.assertIn("is-prop-all-elements-equal all-elements-equal-type-trunc-Prop", code)
        self.assertIn("ind-trunc-Prop' P f H = pr1 (induction-trunc-Prop P f H)", code)
        self.assertIn("compute-ind-trunc-Prop' P f H = pr2 (induction-trunc-Prop P f H)", code)
        self.assertIn("Σ ((p : type-Prop P) → B p) (λ h → (x : A) → h (f x) ＝ g x)", code)
        self.assertIn("is-prop-is-proof-irrelevant (λ x → pair (tr B (α p p) x) (β p p x))", code)
        self.assertIn("( λ Q → ind-trunc-Prop (λ x → Q))", code)
        self.assertIn("( equiv-tot (λ _ → equiv-funext))", code)
        self.assertIn("htpy-eq (ap pr1 (contraction (unique-map-trunc-Prop f) (pair h H)))", code)
        self.assertIn("htpy-uniqueness-map-trunc-Prop id id refl-htpy", code)
        self.assertIn("( ( (map-trunc-Prop g) ·l (htpy-map-trunc-Prop f)) ∙h", code)
        self.assertIn("( ( htpy-map-trunc-Prop g) ·r f))", code)
        for forbidden in ("type-trunc :", "is-truncation-trunc", "function-dependent-universal-property-trunc",
                          "univalence", "{-# REWRITE", "{-# OPTIONS"):
            self.assertNotIn(forbidden, code)
        site = next(b for b in selected if b.block_id == "remark-14.2.3-transport-identifications")
        self.assertIn("is-equiv-tr P (all-elements-equal-type-trunc-Prop x y)", site.code)
        marker = "<!-- rosetta-agda-block: " + site.block_id + " -->"
        if site.conversion_status == "exercise":
            self.assertRegex(document, re.escape(marker) + r"\s*```agda\s*```")
            self.assertNotIn("equiv-identifications-tr-trunc-Prop :", document)
        else:
            self.assertIn("equiv-identifications-tr-trunc-Prop :", document)
        self.assertNotIn("open import foundation", document)
        prose = re.sub(r"^```agda\n.*?^```\s*", "", document, flags=re.M | re.S)
        prose = re.sub(r"<!-- rosetta-agda-block:.*?-->", "", prose)
        for b in selected:
            if b.display_heading:
                prose = prose.replace("### " + b.display_heading, "")
        normalize = lambda value: re.sub(r"\s+", " ", value).strip()
        self.assertEqual(normalize(prose), normalize(render_section(root / "book" / "propositional-truncation.tex", 14, 2)))
        self.assertEqual(document.count("rosetta-proof-tree:"), 3)
        self.assertIn("T(‖X‖̌)≐‖T(X)‖ type", document)

    def test_needed_propositional_sums_stay_at_exercise_12_6(self):
        from rosetta.file_registry import registered_filename

        root = Path(__file__).resolve().parent.parent
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == registered_filename(root, "exercise", 12, 6)]
        self.assertEqual(len(selected), 2)
        self.assertTrue(all(b.item_id == "exercise-12-6" for b in selected))
        sigma, product = sorted(selected, key=lambda b: b.order)
        self.assertIn("Part (a)", sigma.display_heading)
        self.assertIn("is-trunc-is-emb neg-two-𝕋 pr1 (is-emb-pr1-is-subtype K) H", sigma.code)
        self.assertIn("is-prop-product H K = is-prop-Σ H (λ x → K)", product.code)
        self.assertFalse(any(module.startswith("section-14-") for b in selected for module in b.imports))

    def test_needed_coproduct_proposition_result_stays_at_exercise_12_4_c(self):
        from rosetta.file_registry import registered_filename

        root = Path(__file__).resolve().parent.parent
        destination = registered_filename(root, "exercise", 12, 4)
        selected = [b for b in load_manifest(root / "data" / "agda-blocks.json")
                    if b.destination == destination]
        self.assertEqual(len(selected), 1)
        block = selected[0]
        self.assertIn("Part (c)", block.display_heading)
        self.assertIn("all-elements-equal-coproduct", block.code)
        self.assertIn("is-prop-coproduct :", block.code)
        self.assertNotIn("section-13-", " ".join(block.imports))
        gaps = json.loads((root / "data" / "agda-gaps.json").read_text())["items"]
        self.assertTrue(any(g["item_id"] == "exercise-12-4-remaining-parts" for g in gaps))

    def test_adapted_block_verifies_source_without_claiming_exact_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "upstream" / "example.lagda.md"
            source.parent.mkdir()
            source.write_text("upstream code\n")
            block = AgdaBlock(
                block_id="adapted-example",
                provenance_kind="adapted",
                item_id="definition-1.1.1",
                destination="section-1-1-example.lagda.md",
                source_file="upstream/example.lagda.md",
                source_commit="abc",
                source_start_line=1,
                source_end_line=1,
                source_sha256=source_digest(["upstream code\n"], 1, 1),
                code="local adapted code",
                order=1,
                imports=[],
            )
            self.assertEqual(verify_block_source(block, root), [])

    def test_block_insertion_uses_item_anchor(self):
        block = AgdaBlock(
            block_id="example-code",
            provenance_kind="exact",
            item_id="definition-3.2.1",
            destination="section-3-2-example.lagda.md",
            source_file="example",
            source_commit="abc",
            source_start_line=1,
            source_end_line=1,
            source_sha256="abc",
            code="answer = 42",
            order=1,
            imports=[],
        )
        document = (
            "## Definition 3.2.1\n\n"
            "<!-- rosetta-item: definition-3.2.1 -->\n\nText.\n\n"
            "<!-- rosetta-item-end: definition-3.2.1 -->\n\n"
            "Transition to the remark.\n\n"
            "## Remark 3.2.2\n"
        )
        result = inject_agda_blocks(
            document, "section-3-2-example.lagda.md", [block]
        )
        self.assertLess(result.index("answer = 42"), result.index("## Remark"))
        self.assertLess(result.index("answer = 42"), result.index("Transition"))

    def test_block_insertion_uses_narrative_anchor(self):
        block = AgdaBlock(
            block_id="second-clause", provenance_kind="exact",
            item_id="definition-3.2.1", destination="example.lagda.md",
            source_file="example", source_commit="abc", source_start_line=1,
            source_end_line=1, source_sha256="abc", code="second = 2", order=1,
            imports=[], after_text="Second clause.",
        )
        document = (
            "<!-- rosetta-item: definition-3.2.1 -->\n\n"
            "First clause.\n\nSecond clause.\n\n"
            "<!-- rosetta-item-end: definition-3.2.1 -->\n"
        )
        result = inject_agda_blocks(document, "example.lagda.md", [block])
        self.assertGreater(result.index("second = 2"), result.index("Second clause."))
        self.assertLess(result.index("second = 2"), result.index("rosetta-item-end"))

    def test_block_insertion_can_add_a_display_heading(self):
        block = AgdaBlock(
            block_id="prerequisite", provenance_kind="exact",
            item_id="section-8.5", destination="example.lagda.md",
            source_file="example", source_commit="abc", source_start_line=1,
            source_end_line=1, source_sha256="abc", code="helper = 1", order=1,
            imports=[], display_heading="Agda prerequisites",
        )
        document = "<!-- rosetta-item: section-8.5 -->\n\nText.\n\n## Definition\n"
        result = inject_agda_blocks(document, "example.lagda.md", [block])
        self.assertIn("### Agda prerequisites\n\n<!-- rosetta-agda-block:", result)

    def test_training_exercise_inserts_an_empty_block(self):
        block = AgdaBlock(
            block_id="training-exercise", provenance_kind="adapted",
            item_id="lemma-10.4.5", destination="example.lagda.md",
            source_file="example", source_commit="abc", source_start_line=1,
            source_end_line=1, source_sha256="abc", code="solution = answer",
            order=1, imports=["unused"], conversion_status="exercise",
            conversion_note="Reserved as a training exercise.",
        )
        document = (
            "<!-- rosetta-item: lemma-10.4.5 -->\n\nText.\n\n"
            "<!-- rosetta-item-end: lemma-10.4.5 -->\n"
        )
        result = inject_agda_blocks(document, "example.lagda.md", [block])
        self.assertIn("```agda\n\n```", result)
        self.assertNotIn("solution = answer", result)

    def test_block_insertion_uses_unnumbered_heading_anchor(self):
        block = AgdaBlock(
            block_id="natural-numbers",
            provenance_kind="adapted",
            item_id="subheading-3.1-the-introduction-rules-of-natural-numbers",
            destination="section-3-1-example.lagda.md",
            source_file="example",
            source_commit="abc",
            source_start_line=1,
            source_end_line=1,
            source_sha256="abc",
            code="data ℕ : Set where",
            order=1,
            imports=[],
        )
        document = (
            "### The introduction rules of `ℕ`\n\n"
            "<!-- rosetta-item: "
            "subheading-3.1-the-introduction-rules-of-natural-numbers -->\n\n"
            "Text.\n\n## Remark 3.1.1\n"
        )
        result = inject_agda_blocks(document, "section-3-1-example.lagda.md", [block])
        self.assertLess(result.index("data ℕ"), result.index("## Remark"))
