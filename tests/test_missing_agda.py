import unittest
from pathlib import Path

from rosetta.missing_agda import (
    discover_missing_agda,
    load_agda_coverage,
    load_explicit_agda_gaps,
)
from rosetta.review_web import render_missing_agda


class MissingAgdaTests(unittest.TestCase):
    def test_repository_missing_items_exclude_confirmed_complete_files(self):
        root = Path(__file__).resolve().parent.parent
        complete = load_agda_coverage(root)
        items = discover_missing_agda(root)
        explicit = load_explicit_agda_gaps(root)
        self.assertTrue(items)
        self.assertTrue(complete)
        self.assertFalse(any(item.destination in complete for item in items))
        self.assertFalse(any(item.number.startswith(("7.4.", "7.5.")) for item in items))
        self.assertTrue(any(item.number.startswith("8.") for item in items))
        self.assertTrue(
            {item.item_id for item in explicit}.issubset(
                {item.item_id for item in items}
            )
        )
        self.assertTrue(any(item.item_id == "exercise-7-9-b" for item in items))
        self.assertFalse(any(item.number.startswith(("1.", "2.", "3.", "4.", "5.", "6.")) for item in items))
        self.assertFalse(any(item.number.startswith(("7.1.", "7.2.", "7.3.")) for item in items))
        self.assertTrue(all(item.statement for item in items))
        page = render_missing_agda(items[:1])
        self.assertIn(items[0].number, page)
        self.assertIn("/read/", page)
        self.assertIn("/agda/", page)
        self.assertIn("missing Agda", page)
        self.assertIn("Find a missing item", page)


if __name__ == "__main__":
    unittest.main()
