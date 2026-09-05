import json
from fractions import Fraction
from pathlib import Path
import runpy
import unittest


reconstruction = runpy.run_path(str(Path(__file__).with_name("reconstruct-quadratic-tracker.py")))
history = runpy.run_path(str(Path(__file__).with_name("reconstruct-quadratic-history.py")))


def all_configurations():
    return reconstruction["configurations"]() + history["configurations"]()


class QuadraticTrackerTests(unittest.TestCase):
    def test_archived_coordinates_match_exact_recipes(self):
        directory = Path(__file__).resolve().parents[1] / "archive" / "configurations"
        for configuration in all_configurations():
            with self.subTest(configuration=configuration["id"]):
                archived = json.loads((directory / f"{configuration['id']}.json").read_text())
                self.assertEqual(archived, configuration)

    def test_square_counts_and_unique_centers(self):
        for configuration in all_configurations():
            with self.subTest(configuration=configuration["id"]):
                centers = {json.dumps(square["center"], sort_keys=True)
                           for square in configuration["squares"]}
                self.assertEqual(len(centers), configuration["n"])

    def test_half_sqrt_two_preserves_exact_arithmetic(self):
        exact = reconstruction["exact"]
        self.assertEqual(exact(3, 4).half_sqrt_two(), exact(4, Fraction(3, 2)))
        self.assertEqual(exact(3, 4).half_sqrt_two().half_sqrt_two(), exact(Fraction(3, 2), 2))


if __name__ == "__main__":
    unittest.main()
