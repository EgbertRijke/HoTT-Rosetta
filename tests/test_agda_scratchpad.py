import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from rosetta.agda_scratchpad import (
    discard_scratchpad,
    load_scratchpad,
    promotion_scratchpad,
    run_scratchpad_typecheck,
    save_scratchpad,
)


class AgdaScratchpadTests(unittest.TestCase):
    def _root(self, directory: str) -> tuple[Path, Path]:
        root = Path(directory)
        (root / "data").mkdir()
        source = root / "external" / "agda-unimath" / "src" / "example.lagda.md"
        source.parent.mkdir(parents=True)
        source.write_text("original : Set\noriginal = Set\n")
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        manifest = root / "data" / "agda-blocks.json"
        manifest.write_text(json.dumps({
            "format_version": 1,
            "blocks": [{
                "block_id": "example-block",
                "provenance_kind": "exact",
                "item_id": "definition-1.1.1",
                "destination": "section-1-1-example.lagda.md",
                "source_file": "src/example.lagda.md",
                "source_commit": "abc",
                "source_start_line": 1,
                "source_end_line": 2,
                "source_sha256": digest,
                "order": 0,
                "imports": [],
                "code": "original : Set\noriginal = Set",
            }],
        }, indent=2) + "\n")
        return root, manifest

    def test_save_is_temporary_and_does_not_edit_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root, manifest = self._root(directory)
            original = manifest.read_text()
            draft = save_scratchpad(root, "example-block", "draft : Set")
            self.assertEqual(draft.status, "not-checked")
            self.assertEqual(manifest.read_text(), original)
            self.assertIn("_build/rosetta-review", str(
                root / "_build" / "rosetta-review" / "agda-scratchpads.json"
            ))

    def test_typecheck_uses_overlay_and_promotion_requires_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root, manifest = self._root(directory)
            original = manifest.read_text()
            save_scratchpad(
                root, "example-block", "draft : Set", "Testing a local change."
            )
            with patch(
                "rosetta.agda_scratchpad.candidate_for_destination",
                return_value=("section-1-1-example.lagda.md", "module example where"),
            ) as candidate, patch(
                "rosetta.agda_scratchpad.typecheck_candidate",
                return_value=(0, "Checking draft", root / "candidate.lagda.md"),
            ):
                checked = run_scratchpad_typecheck(root, "example-block")
            self.assertEqual(checked.status, "passed")
            overlay = candidate.call_args.kwargs["blocks"]
            self.assertEqual(
                [block.code for block in overlay if block.block_id == "example-block"],
                ["draft : Set"],
            )
            self.assertEqual(promotion_scratchpad(root, "example-block"), checked)
            self.assertEqual(manifest.read_text(), original)

    def test_blocked_draft_is_included_in_the_checked_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root, manifest = self._root(directory)
            value = json.loads(manifest.read_text())
            value["blocks"][0].update(conversion_status="blocked", conversion_note="Missing scope.")
            manifest.write_text(json.dumps(value))
            original = manifest.read_text()
            save_scratchpad(root, "example-block", "invalid draft")
            with patch(
                "rosetta.agda_scratchpad.candidate_for_destination",
                return_value=("section-1-1-example.lagda.md", "invalid draft"),
            ) as candidate, patch(
                "rosetta.agda_scratchpad.typecheck_candidate",
                return_value=(1, "Invalid code", root / "candidate.lagda.md"),
            ):
                checked = run_scratchpad_typecheck(root, "example-block")
            self.assertEqual(candidate.call_args.kwargs["blocks"][0].conversion_status, "ready")
            self.assertEqual(checked.status, "failed")
            self.assertEqual(manifest.read_text(), original)
            with self.assertRaisesRegex(ValueError, "must pass Agda"):
                promotion_scratchpad(root, "example-block")

    def test_failed_or_stale_draft_cannot_be_promoted(self):
        with tempfile.TemporaryDirectory() as directory:
            root, manifest = self._root(directory)
            save_scratchpad(root, "example-block", "bad")
            with self.assertRaisesRegex(ValueError, "must pass Agda"):
                promotion_scratchpad(root, "example-block")
            manifest.write_text(manifest.read_text() + "\n")
            draft = load_scratchpad(root, "example-block")
            self.assertIsNotNone(draft)
            discard_scratchpad(root, "example-block")
            self.assertIsNone(load_scratchpad(root, "example-block"))


if __name__ == "__main__":
    unittest.main()
