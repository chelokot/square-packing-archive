import json
from fractions import Fraction
from pathlib import Path
import runpy
import unittest


reconstruction = runpy.run_path(str(Path(__file__).with_name("reconstruct-sqrt-seven.py")))


class SqrtSevenReconstructionTests(unittest.TestCase):
    def test_archived_coordinates_match_exact_recipes(self):
        directory = Path(__file__).resolve().parents[1] / "archive" / "configurations"
        for configuration in reconstruction["configurations"]():
            with self.subTest(configuration=configuration["id"]):
                archived = json.loads((directory / f"{configuration['id']}.json").read_text())
                self.assertEqual(archived, configuration)

    def test_exact_unit_frames_and_unique_centers(self):
        quadratic = reconstruction["quadratic"]
        for name, count in (("eighteen_hamalainen", 18), ("eighteen_gustafsson", 18),
                            ("eighteen_cantrell", 18), ("eighteen_gensane_ryckelynck", 18),
                            ("fifty_three", 53), ("eighty_six", 86)):
            with self.subTest(recipe=name):
                squares, side = reconstruction[name]()
                self.assertEqual(len(squares), count)
                self.assertEqual(len({(square.center_x, square.center_y) for square in squares}), count)
                for square in squares:
                    self.assertEqual(square.cosine * square.cosine + square.sine * square.sine,
                                     quadratic(1))

    def test_fifty_three_retains_bound_with_rational_auxiliary_angles(self):
        quadratic = reconstruction["quadratic"]
        squares, side = reconstruction["fifty_three"]()
        self.assertEqual(side, (13 + reconstruction["root_seven"]) / 2)
        tangents = {square.sine / (1 + square.cosine) for square in squares}
        self.assertIn(quadratic(Fraction(6, 25)), tangents)
        self.assertIn(quadratic(Fraction(2, 7)), tangents)

    def test_quadratic_division_is_exact(self):
        root_seven = reconstruction["root_seven"]
        self.assertEqual((3 + root_seven) / (3 + root_seven), reconstruction["quadratic"](1))
        self.assertEqual((3 + root_seven) * (3 - root_seven), reconstruction["quadratic"](2))


if __name__ == "__main__":
    unittest.main()
