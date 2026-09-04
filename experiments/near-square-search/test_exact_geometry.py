from fractions import Fraction
import unittest

from exact_geometry import RationalSquare, exact_errors


class ExactGeometryTests(unittest.TestCase):
    def test_exact_grid_allows_boundary_contacts(self):
        squares = tuple(
            RationalSquare((Fraction(2 * column + 1, 2), Fraction(2 * row + 1, 2)), Fraction(0))
            for row in range(8) for column in range(8)
        )
        self.assertEqual(exact_errors(squares, Fraction(8)), ())

    def test_overlap_smaller_than_float_precision_is_rejected(self):
        squares = (
            RationalSquare((Fraction(1, 2), Fraction(1, 2)), Fraction(0)),
            RationalSquare((Fraction(3, 2) - Fraction(1, 10**30), Fraction(1, 2)), Fraction(0)),
        )
        self.assertEqual(exact_errors(squares, Fraction(2)), ("squares 0 and 1 overlap in their interiors",))

    def test_rotated_square_has_exact_unit_edges(self):
        square = RationalSquare((Fraction(1), Fraction(1)), Fraction(1, 40))
        vertices = square.vertices
        for first, second in zip(vertices, vertices[1:] + vertices[:1]):
            self.assertEqual(sum((first[coordinate] - second[coordinate])**2 for coordinate in range(2)), 1)
        self.assertEqual(exact_errors((square,), Fraction(2)), ())

    def test_boundary_escape_is_rejected(self):
        square = RationalSquare((Fraction(1, 2), Fraction(1, 2)), Fraction(1, 40))
        self.assertEqual(exact_errors((square,), Fraction(2)), ("square 0 crosses the container boundary",))

    def test_rotated_edge_contact_is_allowed_despite_overlapping_bounding_boxes(self):
        squares = (
            RationalSquare((Fraction(1), Fraction(1)), Fraction(1, 2)),
            RationalSquare((Fraction(8, 5), Fraction(9, 5)), Fraction(1, 2)),
        )
        self.assertEqual(exact_errors(squares, Fraction(3)), ())

    def test_rotated_overlap_is_rejected(self):
        squares = (
            RationalSquare((Fraction(1), Fraction(1)), Fraction(1, 2)),
            RationalSquare((Fraction(159, 100), Fraction(179, 100)), Fraction(1, 2)),
        )
        self.assertEqual(exact_errors(squares, Fraction(3)), ("squares 0 and 1 overlap in their interiors",))


if __name__ == "__main__":
    unittest.main()
