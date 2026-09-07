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
    def test_proposed_evaluation_has_its_natural_home(self):
        from rosetta.file_registry import registered_filename
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        document = (rosetta_directory(root) / registered_filename(root, "section", 2, 2)).read_text()
        self.assertLess(document.index("rosetta-item: remark-2.2.2"), document.index("ev-point :"))
        self.assertLess(document.index("ev-point :"), document.index("rosetta-item-end: remark-2.2.2"))
        self.assertLess(document.index("rosetta-item-end: remark-2.2.2"), document.index("Now we can use these rules"))

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
        self.assertEqual(len(selected), 17)
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
        self.assertEqual(len(selected), 8)
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

    def test_proposed_fiber_orientation_has_its_natural_home(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        block = next(
            block for block in load_manifest(root / "data" / "agda-blocks.json")
            if block.block_id == "definition-10.3.1-fiber-orientation-equivalence"
        )
        document = (rosetta_directory(root) / block.destination).read_text()
        start = document.index("<!-- rosetta-item: definition-10.3.1 -->")
        end = document.index("<!-- rosetta-item-end: definition-10.3.1 -->")
        original = document.index("fiber' :")
        position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
        self.assertLess(start, original)
        self.assertLess(original, position)
        self.assertLess(position, end)
        self.assertLess(end, document.index("In other words, the fiber"))

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
        self.assertEqual(len(selected), 11)
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

    def test_proposed_fiber_identity_auxiliaries_have_natural_homes(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = {block.block_id: block for block in load_manifest(root / "data" / "agda-blocks.json")}
        involution = blocks["definition-5.2.5-inversion-involution"]
        self.assertEqual(involution.item_id, "definition-5.2.5")
        document = (rosetta_directory(root) / involution.destination).read_text()
        marker = document.index("<!-- rosetta-agda-block: definition-5.2.5-inversion-involution -->")
        self.assertLess(document.index("  right-inv :"), marker)
        self.assertLess(marker, document.index("<!-- rosetta-item-end: definition-5.2.5 -->"))
        for identifier in (
            "exercise-9-1-inverse-concatenation",
            "exercise-9-1-concatenation-inverse-laws",
            "exercise-9-1-inversion-and-concatenation-equivalences",
        ):
            self.assertEqual(blocks[identifier].item_id, "exercise-9-1")
        example = blocks["example-11.6.3-identities-in-fibers"]
        self.assertEqual(example.conversion_status, "ready")
        self.assertNotIn("  inv-inv :", example.code)
        self.assertNotIn("    is-equiv-inv :", example.code)

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

    def test_proposed_relation_auxiliaries_stay_at_their_chapter_eleven_homes(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = load_manifest(root / "data" / "agda-blocks.json")
        names = (
            "definition-11.1.1-total-map-homotopies",
            "definition-11.1.1-total-map-identity",
            "definition-11.1.1-total-map-composition",
            "theorem-11.2.2-retract-fundamental-theorem",
        )
        selected = [next(block for block in blocks if block.block_id == name) for name in names]
        for block in selected:
            with self.subTest(block=block.block_id):
                document = (rosetta_directory(root) / block.destination).read_text()
                start = document.index(f"<!-- rosetta-item: {block.item_id}")
                end = document.index(f"<!-- rosetta-item-end: {block.item_id} -->")
                position = document.index(f"<!-- rosetta-agda-block: {block.block_id} -->")
                self.assertLess(start, position)
                self.assertLess(position, end)
                self.assertNotIn("section-12-", document)
        total = (rosetta_directory(root) / selected[0].destination).read_text()
        positions = [total.index(name + " :") for name in
                     ("  tot", "tot-htpy", "tot-id", "preserves-comp-tot")]
        self.assertEqual(positions, sorted(positions))
        self.assertIn("id {A = Σ A B}", selected[1].code)
        theorem = (rosetta_directory(root) / selected[-1].destination).read_text()
        self.assertLess(theorem.index("fundamental-theorem-id-J' :"),
                        theorem.index("fundamental-theorem-id-retraction :"))
        later = next(block for block in blocks if block.block_id ==
                     "theorem-12.3.4-propositional-identity-relation")
        self.assertEqual(later.conversion_status, "ready")
        self.assertNotIn("fundamental-theorem-id-retraction :", later.code)

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

    def test_proposed_truncated_map_auxiliaries_precede_their_later_consumer(self):
        from rosetta.layout import rosetta_directory

        root = Path(__file__).resolve().parent.parent
        blocks = {b.block_id: b for b in load_manifest(root / "data" / "agda-blocks.json")}
        transport = blocks["exercise-9-1-transport-equivalences"]
        self.assertEqual(transport.item_id, "exercise-9-1")
        self.assertIn("is-equiv-tr :", transport.code)
        self.assertIn("is-section-inv-tr :", transport.code)
        self.assertIn("is-retraction-inv-tr :", transport.code)
        self.assertIn("( tr B (inv p))", transport.code)
        self.assertFalse(any(i.startswith("section-12-") for i in transport.imports))
        fiber = blocks["example-11.6.3-fiber-of-action-specialization"]
        self.assertEqual(fiber.item_id, "example-11.6.3")
        self.assertIn("is-equiv-tr (fiber (ap f)) right-unit", fiber.code)
        document = (rosetta_directory(root) / fiber.destination).read_text()
        self.assertLess(document.index("  equiv-fiber-ap-eq-fiber :"),
                        document.index("  eq-fiber-fiber-ap :"))
        self.assertLess(document.index("  eq-fiber-fiber-ap :"),
                        document.index("<!-- rosetta-item-end: example-11.6.3 -->"))
        self.assertNotIn("section-12-", document)
        theorem = blocks["theorem-12.4.7-truncated-action-on-identities"]
        self.assertEqual(theorem.conversion_status, "ready")
        self.assertNotIn("is-equiv-tr :", theorem.code)
        self.assertNotIn("eq-fiber-fiber-ap :", theorem.code)

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
