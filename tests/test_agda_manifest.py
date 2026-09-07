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
