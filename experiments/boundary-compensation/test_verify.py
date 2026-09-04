from fractions import Fraction
import unittest

from verify import (
    RationalSquare, canonical, chord_length, dilated_polygon, examples,
    contains, from_bottom_vertex, resource_score, translate, vertical_propagation_counterexample,
)
from row_compensation import resource_score as original_row_score


class BoundaryCompensationTests(unittest.TestCase):
    def test_all_examples_are_exact_packings_of_larger_than_unit_squares(self):
        for example in examples():
            with self.subTest(example=example.name):
                example.verify_packing()
                self.assertLess(example.scores[0].total, 1)

    def test_adjacent_corner_owner_does_not_repay_deficit(self):
        example = examples()[0]
        self.assertEqual(example.scores[0].covered_corner_points, ((Fraction(1), Fraction(9, 10)),))
        self.assertEqual(example.scores[1].covered_corner_points, ((Fraction(9, 10), Fraction(1)),))
        self.assertEqual(
            sum(score.total for score in example.scores),
            Fraction(37093591185684897192768409, 18629685712216176000000000),
        )
        self.assertLess(sum(score.total for score in example.scores), 2)

    def test_nearest_edge_point_does_not_force_next_edge_point(self):
        example = examples()[1]
        self.assertEqual(example.scores[1].covered_edge_points, ((Fraction(2), Fraction(9, 10)),))
        self.assertEqual(example.scores[0].total, Fraction(25520831049041, 25584000000000))
        self.assertEqual(example.scores[1].total, Fraction(25917702849041, 25584000000000))

    def test_nearest_edge_point_owner_does_not_repay_deficit(self):
        example = examples()[2]
        self.assertEqual(example.scores[1].covered_edge_points, ((Fraction(2), Fraction(9, 10)),))
        self.assertEqual(example.scores[0].total, Fraction(38214099199069501, 39600000000000000))
        self.assertEqual(example.scores[1].total, Fraction(39795129100069501, 39600000000000000))
        self.assertEqual(
            sum(score.total for score in example.scores), Fraction(39004614149569501, 19800000000000000),
        )
        self.assertLess(sum(score.total for score in example.scores), 2)

    def test_next_translate_of_low_angle_pair_covers_two_edge_points(self):
        example = examples()[2]
        next_square = translate(
            example.squares[1], example.factor,
            (example.factor / Fraction(9999, 10001), Fraction(0)),
        )
        next_score = resource_score(next_square, example.factor)
        self.assertEqual(
            next_score.covered_edge_points,
            ((Fraction(3), Fraction(9, 10)), (Fraction(4), Fraction(9, 10))),
        )
        self.assertGreater(sum(score.total for score in example.scores) + next_score.total, 3)

    def test_general_scorer_reproduces_existing_six_square_row(self):
        original = from_bottom_vertex(
            canonical.VERTEX_HORIZONTAL, canonical.FACTOR, canonical.COSINE, canonical.SINE,
        )
        for index in range(6):
            with self.subTest(index=index):
                square = translate(
                    original, canonical.FACTOR,
                    (index * canonical.FACTOR / canonical.SINE, Fraction(0)),
                )
                self.assertEqual(resource_score(square, canonical.FACTOR), original_row_score(index))

    def test_boundary_coincident_chord_has_no_interior_length(self):
        square = RationalSquare((Fraction(1, 2), Fraction(1, 2)), Fraction(0))
        polygon = dilated_polygon(square, Fraction(1))
        self.assertEqual(chord_length(polygon, (Fraction(0), Fraction(1)), (Fraction(1), Fraction(1))), 0)
        self.assertEqual(
            chord_length(polygon, (Fraction(1, 4), Fraction(1, 2)), (Fraction(3, 4), Fraction(1, 2))),
            Fraction(1, 2),
        )

    def test_missing_upper_point_does_not_force_neighboring_vertical_crossing(self):
        example = vertical_propagation_counterexample()
        example.verify_packing()
        square = example.squares[0]
        self.assertTrue(contains(square, example.factor, (Fraction(1), Fraction(9, 10))))
        self.assertFalse(contains(square, example.factor, (Fraction(1), Fraction(1))))
        polygon = dilated_polygon(square, example.factor)
        for horizontal in (Fraction(0), Fraction(2)):
            self.assertEqual(
                chord_length(polygon, (horizontal, Fraction(9, 10)), (horizontal, Fraction(1))), 0,
            )
        self.assertGreater(example.scores[0].total, 1)


if __name__ == "__main__":
    unittest.main()
