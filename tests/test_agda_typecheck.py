import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from rosetta.agda_manifest import AgdaBlock
from rosetta.agda_typecheck import (
    deferred_exercises,
    run_typecheck,
    typecheck_result,
)


class AgdaTypecheckTests(unittest.TestCase):
    @staticmethod
    def _block(block_id, destination, status="ready", imports=None):
        return AgdaBlock(
            block_id=block_id,
            provenance_kind="handwritten",
            item_id=block_id,
            destination=destination,
            source_file="",
            source_commit="",
            source_start_line=0,
            source_end_line=0,
            source_sha256="",
            code="example = 1",
            order=0,
            imports=imports or [],
            source_note="Test fixture.",
            conversion_status=status,
            conversion_note="Unfinished exercise." if status == "exercise" else "",
        )

    def test_deferred_exercises_follow_imports(self):
        exercise = self._block(
            "lemma-10.4.5", "section-10-4-example.lagda.md", "exercise"
        )
        consumer = self._block(
            "later-result",
            "section-10-5-example.lagda.md",
            imports=["section-10-4-example"],
        )
        self.assertEqual(
            deferred_exercises(
                [exercise, consumer], "section-10-5-example.lagda.md"
            ),
            [exercise],
        )

    def test_deferred_check_does_not_invoke_agda(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            exercise = self._block(
                "lemma-10.4.5", "section-10-4-example.lagda.md", "exercise"
            )
            with patch(
                "rosetta.agda_typecheck.candidate_for_destination",
                return_value=("section-10-4-example.lagda.md", "candidate"),
            ), patch(
                "rosetta.agda_typecheck.load_manifest", return_value=[exercise]
            ), patch(
                "rosetta.agda_typecheck.typecheck_fingerprint", return_value="exercise"
            ), patch(
                "rosetta.agda_typecheck.typecheck_candidate"
            ) as invoke_agda:
                result = run_typecheck(root, "section-10-4-example.lagda.md")
            self.assertEqual(result["status"], "deferred")
            self.assertIn("Agda was not run", result["message"])
            invoke_agda.assert_not_called()

    def test_force_runs_agda_for_deferred_check(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            exercise = self._block(
                "lemma-10.4.5", "section-10-4-example.lagda.md", "exercise"
            )
            staged = root / "candidate.lagda.md"
            with patch(
                "rosetta.agda_typecheck.candidate_for_destination",
                return_value=("section-10-4-example.lagda.md", "candidate"),
            ), patch(
                "rosetta.agda_typecheck.load_manifest", return_value=[exercise]
            ), patch(
                "rosetta.agda_typecheck.typecheck_fingerprint", return_value="exercise"
            ), patch(
                "rosetta.agda_typecheck.typecheck_candidate",
                return_value=(1, "missing proof", staged),
            ) as invoke_agda:
                result = run_typecheck(
                    root, "section-10-4-example.lagda.md", force=True
                )
            self.assertEqual(result["status"], "failed")
            invoke_agda.assert_called_once()

    def test_result_is_cached_and_becomes_unchecked_after_change(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            staged = root / "_build" / "rosetta-typecheck" / "candidate-example.lagda.md"
            with patch(
                "rosetta.agda_typecheck.candidate_for_destination",
                return_value=("example.lagda.md", "first candidate"),
            ), patch(
                "rosetta.agda_typecheck.load_manifest", return_value=[]
            ), patch(
                "rosetta.agda_typecheck.typecheck_fingerprint", return_value="first"
            ), patch(
                "rosetta.agda_typecheck.typecheck_candidate",
                return_value=(0, "", staged),
            ):
                checked = run_typecheck(root, "section-1-1-example.lagda.md")
                self.assertEqual(checked["status"], "passed")
                self.assertEqual(
                    typecheck_result(root, "section-1-1-example.lagda.md")["status"],
                    "passed",
                )

            with patch(
                "rosetta.agda_typecheck.candidate_for_destination",
                return_value=("example.lagda.md", "changed candidate"),
            ), patch(
                "rosetta.agda_typecheck.load_manifest", return_value=[]
            ), patch(
                "rosetta.agda_typecheck.typecheck_fingerprint", return_value="changed"
            ):
                self.assertEqual(
                    typecheck_result(root, "section-1-1-example.lagda.md")["status"],
                    "not-checked",
                )

    def test_failure_message_is_saved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            staged = root / "_build" / "rosetta-typecheck" / "candidate-example.lagda.md"
            with patch(
                "rosetta.agda_typecheck.candidate_for_destination",
                return_value=("example.lagda.md", "candidate"),
            ), patch(
                "rosetta.agda_typecheck.load_manifest", return_value=[]
            ), patch(
                "rosetta.agda_typecheck.typecheck_fingerprint", return_value="candidate"
            ), patch(
                "rosetta.agda_typecheck.typecheck_candidate",
                return_value=(1, "proof does not have the required type", staged),
            ):
                result = run_typecheck(root, "section-1-1-example.lagda.md")
            self.assertEqual(result["status"], "failed")
            self.assertIn("required type", result["message"])
