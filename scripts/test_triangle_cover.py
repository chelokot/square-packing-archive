import runpy
import re
import unittest
from fractions import Fraction
from pathlib import Path


generator = runpy.run_path(str(Path(__file__).with_name("generate-triangle-cover.py")))
Quadratic = generator["Quadratic"]
Halfplane = generator["Halfplane"]
Constraint = generator["Constraint"]
Renderer = generator["Renderer"]
ZERO = generator["ZERO"]
ONE = generator["ONE"]
rational = generator["rational"]
clip = generator["clip"]
certificate = generator["certificate"]


class ExactCoverTests(unittest.TestCase):
    def test_radical_arithmetic_and_inverses(self):
        radical = Quadratic(Fraction(0), Fraction(1))
        self.assertEqual(radical * radical, rational(2))
        for first in (ONE, radical, ONE + radical, ONE - radical):
            for second in (ONE, radical, ONE + radical, ONE - radical):
                self.assertEqual((first / second) * second, first)

    def test_sign_resolves_cancellation_beyond_float_precision(self):
        numerator, denominator = 1, 1
        for exponent in range(1, 101):
            value = Quadratic(Fraction(numerator), Fraction(-denominator))
            self.assertEqual(value.sign(), -1 if exponent % 2 else 1)
            self.assertEqual((-value).sign(), -value.sign())
            numerator, denominator = numerator + 2 * denominator, numerator + denominator
        self.assertEqual(ZERO.sign(), 0)

    def test_clipping_preserves_exact_radical_intersection(self):
        radical = Quadratic(Fraction(0), Fraction(1))
        square = ((ZERO, ZERO), (rational(2), ZERO), (rational(2), rational(2)), (ZERO, rational(2)))
        boundary = Halfplane(ONE, ZERO, -radical)
        result = clip(square, boundary)
        self.assertEqual(set(result), {(radical, ZERO), (rational(2), ZERO),
                                      (rational(2), rational(2)), (radical, rational(2))})
        self.assertTrue(all(boundary.at(point).sign() >= 0 for point in result))

    def test_tangent_clipping_preserves_boundary_segment(self):
        square = ((ZERO, ZERO), (ONE, ZERO), (ONE, ONE), (ZERO, ONE))
        self.assertEqual(set(clip(square, Halfplane(-ONE, ZERO, ZERO))),
                         {(ZERO, ZERO), (ZERO, ONE)})
        self.assertEqual(clip(square, Halfplane(-ONE, ZERO, -ONE)), ())

    def assert_certificate(self, constraints):
        selected = certificate(constraints)
        for component in ("horizontal", "vertical"):
            self.assertEqual(sum((getattr(constraint.boundary, component) * weight
                                  for constraint, weight in selected), ZERO), ZERO)
        self.assertTrue(all(weight.sign() > 0 for _, weight in selected))
        constant = sum((constraint.boundary.constant * weight
                        for constraint, weight in selected), ZERO)
        self.assertTrue(constant.sign() < 0 or
                        (constant.sign() == 0 and any(constraint.strict for constraint, _ in selected)))

    def test_two_constraint_contradiction(self):
        self.assert_certificate((Constraint(Halfplane(ONE, ZERO, -ONE), "lower"),
                                 Constraint(Halfplane(-ONE, ZERO, ZERO), "upper")))

    def test_three_constraint_contradiction(self):
        self.assert_certificate((Constraint(Halfplane(ONE, ZERO, ZERO), "horizontal"),
                                 Constraint(Halfplane(ZERO, ONE, ZERO), "vertical"),
                                 Constraint(Halfplane(-ONE, -ONE, -ONE), "diagonal")))

    def test_strict_boundary_is_not_confused_with_feasible_contact(self):
        first = Constraint(Halfplane(ONE, ZERO, ZERO), "lower")
        second = Constraint(Halfplane(-ONE, ZERO, ZERO), "upper")
        with self.assertRaises(ValueError):
            certificate((first, second))
        self.assert_certificate((first, Constraint(second.boundary, "strict", True)))

    def test_cover_rejects_an_uncovered_region(self):
        domain = ((ZERO, ZERO), (ONE, ZERO), (ONE, ONE), (ZERO, ONE))
        with self.assertRaisesRegex(ValueError, "do not cover"):
            Renderer("example").cover(0, domain, (), ())

    def test_hull_normalization_includes_edges_not_used_by_triangles(self):
        _, proof = generator["render_cover"](3, False)
        definitions = set(re.findall(r"private lemma (stepThree_area_\d+_\d+)", proof))
        references = set(re.findall(r"rw \[(stepThree_area_\d+_\d+)\]", proof))
        self.assertIn("stepThree_area_0_7", definitions)
        self.assertLessEqual(references, definitions)


if __name__ == "__main__":
    unittest.main()
