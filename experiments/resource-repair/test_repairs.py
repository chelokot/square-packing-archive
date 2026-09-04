from fractions import Fraction
import unittest

from verify_repairs import (
    LEFT_WITNESS, RIGHT_WITNESS, ORIGINAL_WITNESS, OFFSET,
    diagonal_affine, original_layout_dual, variable_area_dual,
)


class RepairTests(unittest.TestCase):
    def test_canonical_score_is_recovered(self):
        features = ORIGINAL_WITNESS.evaluate(OFFSET, Fraction(9, 20))
        self.assertEqual(features[0], Fraction(25009470849041, 25584000000000))

    def test_trimmed_line_repair_fails_without_rotation(self):
        features = LEFT_WITNESS.evaluate(Fraction(1), Fraction(1, 2))
        self.assertEqual(features[1], Fraction(4501, 50000000))
        self.assertEqual(features[2], (Fraction(4501, 5000), 0, Fraction(1, 10000), 0))
        self.assertEqual(features[3], ((1, Fraction(9, 10)),))
        self.assertEqual(features[4], ())
        self.assertEqual(features[0], Fraction(47512001, 50000000))

    def test_diagonal_family_has_incompatible_weight_requirements(self):
        left_intercept, left_slope = diagonal_affine(LEFT_WITNESS)
        right_intercept, right_slope = diagonal_affine(RIGHT_WITNESS)
        self.assertEqual((left_intercept, left_slope), (Fraction(72462001, 50000000), Fraction(-499, 500)))
        self.assertEqual((right_intercept, right_slope), (Fraction(50209999, 100000000), Fraction(249, 250)))
        self.assertLess((1 - left_intercept) / left_slope, (1 - right_intercept) / right_slope)
        for weight in (Fraction(0), Fraction(2, 5), Fraction(9, 20), Fraction(19, 40), Fraction(1, 2)):
            for square, intercept, slope in (
                (LEFT_WITNESS, left_intercept, left_slope),
                (RIGHT_WITNESS, right_intercept, right_slope),
            ):
                self.assertEqual(square.evaluate(Fraction(1), weight, 1 - 2 * weight)[0], intercept + slope * weight)

    def test_original_layout_needs_more_than_available_mass(self):
        multipliers, minimum_mass = original_layout_dual()
        self.assertTrue(all(multiplier > 0 for multiplier in multipliers))
        self.assertGreater(minimum_mass, 14)

    def test_changing_area_weight_still_exceeds_budget(self):
        multipliers, minimum_mass = variable_area_dual()
        self.assertEqual(len(multipliers), 4)
        self.assertTrue(all(multiplier > 0 for multiplier in multipliers))
        self.assertGreater(minimum_mass, 14)


if __name__ == "__main__":
    unittest.main()
