from fractions import Fraction
import unittest

import numpy as np
from scipy.optimize import check_grad, minimize

from exact_geometry import exact_errors
from search import PackingObjective, rationalize


class SearchTests(unittest.TestCase):
    def test_analytic_gradient_matches_finite_differences(self):
        objective = PackingObjective(5, 2)
        generator = np.random.default_rng(100)
        for _ in range(5):
            variables = generator.uniform(-0.5, 2.5, 15)
            error = check_grad(lambda point: objective(point)[0], lambda point: objective(point)[1], variables)
            self.assertLess(error, 2e-5)

    def test_optimizer_finds_a_certifiable_control_packing(self):
        objective = PackingObjective(4, 2.2)
        variables = np.array(((0.6, 0.6, 0.01), (1.4, 0.6, -0.01), (0.6, 1.4, 0.01), (1.4, 1.4, -0.01))).ravel()
        result = minimize(objective, variables, jac=True, method="L-BFGS-B", options={"gtol": 1e-12, "ftol": 0.0})
        self.assertEqual(exact_errors(rationalize(result.x), Fraction(11, 5)), ())


if __name__ == "__main__":
    unittest.main()
