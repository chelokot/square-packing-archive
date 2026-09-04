from fractions import Fraction
from itertools import combinations
import unittest

from row_compensation import STEP, canonical, fits, resource_score, separated, translated_square


class RowCompensationTests(unittest.TestCase):
    def test_original_score_is_unchanged(self):
        score = resource_score(0, Fraction(4))
        self.assertEqual(score.area, Fraction(611022059041, 25584000000000))
        self.assertEqual(score.chord_lengths, (Fraction(1251468079, 1279200000), 0, Fraction(29, 1000), 0))
        self.assertEqual(score.total, Fraction(25009470849041, 25584000000000))

    def test_six_copies_fit_with_disjoint_interiors(self):
        row = tuple(translated_square(index) for index in range(6))
        self.assertTrue(all(fits(square) for square in row))
        self.assertTrue(all(separated(first, second) for first, second in combinations(row, 2)))
        self.assertTrue(all(canonical.polygon_area(square) == canonical.FACTOR**2 for square in row))

    def test_seventh_copy_crosses_right_wall(self):
        square = translated_square(6)
        self.assertFalse(fits(square))
        self.assertGreater(max(vertex[0] for vertex in square), 8)

    def test_shorter_step_produces_overlap(self):
        shifted = tuple(
            (horizontal + STEP * Fraction(9999, 10000), vertical)
            for horizontal, vertical in canonical.SQUARE
        )
        self.assertFalse(separated(canonical.SQUARE, shifted))

    def test_exact_row_scores(self):
        scores = tuple(resource_score(index) for index in range(6))
        self.assertEqual(tuple(score.total for score in scores), (
            Fraction(25009470849041, 25584000000000),
            Fraction(38709702849041, 25584000000000),
            Fraction(25917702849041, 25584000000000),
            Fraction(25917702849041, 25584000000000),
            Fraction(25917702849041, 25584000000000),
            Fraction(41430768838816559, 40908816000000000),
        ))
        self.assertEqual(scores[1].covered_edge_points, ((Fraction(2), Fraction(9, 10)), (Fraction(3), Fraction(9, 10))))
        self.assertEqual(sum(score.total for score in scores), Fraction(133822474074449677, 20454408000000000))
        self.assertGreater(sum(score.total for score in scores), 6)


if __name__ == "__main__":
    unittest.main()
