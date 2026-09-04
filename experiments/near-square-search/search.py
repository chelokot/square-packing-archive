import argparse
from fractions import Fraction
import json
import math
import sys
import time

import numpy as np
from numpy.typing import NDArray
import scipy
from scipy.optimize import minimize

from exact_geometry import RationalSquare, exact_errors


FloatArray = NDArray[np.float64]


def rationalize(variables: FloatArray) -> tuple[RationalSquare, ...]:
    return tuple(
        RationalSquare(
            (Fraction(str(center_x)), Fraction(str(center_y))),
            Fraction(str(math.tan(angle / 2))),
        )
        for center_x, center_y, angle in variables.reshape(-1, 3)
    )


class PackingObjective:
    def __init__(self, count: int, side: float, clearance: float = 1e-8):
        self.first, self.second = np.triu_indices(count, 1)
        self.side = side
        self.clearance = clearance

    def evaluate(self, variables: FloatArray) -> tuple[float, FloatArray, float]:
        squares = variables.reshape(-1, 3)
        centers = squares[:, :2]
        angles = squares[:, 2]
        cosine = np.cos(angles)
        sine = np.sin(angles)
        axes = np.stack((cosine, sine, -sine, cosine), axis=1).reshape(-1, 2, 2)
        pair_axes = np.concatenate((axes[self.first], axes[self.second]), axis=1)
        displacement = centers[self.second] - centers[self.first]
        projections = np.einsum("pax,px->pa", pair_axes, displacement)
        difference = angles[self.second] - angles[self.first]
        relative_cosine = np.cos(difference)
        relative_sine = np.sin(difference)
        radii = (1 + np.abs(relative_cosine) + np.abs(relative_sine)) / 2
        gaps = np.abs(projections) - radii[:, None] - self.clearance
        selected = gaps.argmax(axis=1)
        pair_indices = np.arange(len(selected))
        pair_violation = np.maximum(0, -gaps[pair_indices, selected])
        selected_axes = pair_axes[pair_indices, selected]
        projection_sign = np.sign(projections[pair_indices, selected])
        position_gradient = 2 * pair_violation[:, None] * projection_sign[:, None] * selected_axes
        gradient = np.zeros_like(squares)
        np.add.at(gradient[:, :2], self.first, position_gradient)
        np.add.at(gradient[:, :2], self.second, -position_gradient)
        radius_derivative = (
            -relative_sine * np.sign(relative_cosine)
            + relative_cosine * np.sign(relative_sine)
        ) / 2
        radius_gradient = 2 * pair_violation * radius_derivative
        np.add.at(gradient[:, 2], self.first, -radius_gradient)
        np.add.at(gradient[:, 2], self.second, radius_gradient)
        axis_derivative = (
            -selected_axes[:, 1] * displacement[:, 0]
            + selected_axes[:, 0] * displacement[:, 1]
        )
        owner = np.where(selected < 2, self.first, self.second)
        np.add.at(gradient[:, 2], owner, -2 * pair_violation * projection_sign * axis_derivative)
        extent = (np.abs(cosine) + np.abs(sine)) / 2 + self.clearance
        extent_derivative = (-sine * np.sign(cosine) + cosine * np.sign(sine)) / 2
        lower_violation = np.maximum(0, extent[:, None] - centers)
        upper_violation = np.maximum(0, centers + extent[:, None] - self.side)
        gradient[:, :2] += 2 * (upper_violation - lower_violation)
        gradient[:, 2] += 2 * extent_derivative * (lower_violation + upper_violation).sum(axis=1)
        loss = np.sum(pair_violation**2) + np.sum(lower_violation**2 + upper_violation**2)
        maximum_violation = max(pair_violation.max(), lower_violation.max(), upper_violation.max())
        return float(loss), gradient.ravel(), float(maximum_violation)

    def __call__(self, variables: FloatArray) -> tuple[float, FloatArray]:
        loss, gradient, _ = self.evaluate(variables)
        return loss, gradient


SEED_MODES = ("small-angle", "boundary-motif", "alternating-rows", "checkerboard", "random-angle", "random-position")


def seed_configuration(seed: int, side: float) -> FloatArray:
    generator = np.random.default_rng(seed)
    missing_patterns = (
        {(7, 0), (7, 1)},
        {(0, 0), (7, 7)},
        {(3, 3), (4, 4)},
        {(3, 0), (4, 0)},
    )
    missing = missing_patterns[seed % len(missing_patterns)]
    squares = np.array(
        [(column + 0.5, row + 0.5, 0.0) for row in range(8) for column in range(8) if (column, row) not in missing],
        dtype=float,
    )
    squares[:, :2] *= side / 8
    mode = SEED_MODES[seed % len(SEED_MODES)]
    if mode == "boundary-motif":
        boundary = np.flatnonzero(np.any((squares[:, :2] < 1) | (squares[:, :2] > side - 1), axis=1))
        squares[boundary, 2] = generator.choice((-1, 1), len(boundary)) * math.atan2(80, 1599)
    elif mode == "small-angle":
        squares[:, 2] = generator.normal(0, 0.002, len(squares))
    elif mode == "alternating-rows":
        squares[:, 2] = np.where(np.floor(squares[:, 1]).astype(int) % 2, 0.15, -0.15)
    elif mode == "checkerboard":
        squares[:, 2] = np.where(np.floor(squares[:, :2]).sum(axis=1).astype(int) % 2, 0.3, -0.3)
    elif mode == "random-angle":
        squares[:, 2] = generator.uniform(-0.3, 0.3, len(squares))
    else:
        squares[:, :2] = generator.uniform(0.75, side - 0.75, (len(squares), 2))
        squares[:, 2] = generator.uniform(-math.pi / 4, math.pi / 4, len(squares))
    return squares.ravel()


def main() -> None:
    parser = argparse.ArgumentParser(description="Local numerical search; only an exact certificate is a packing.")
    parser.add_argument("--seeds", type=int, default=8)
    parser.add_argument("--seconds-per-seed", type=float, default=20)
    parser.add_argument("--side", default="7.9999")
    parser.add_argument("--output", type=argparse.FileType("w"), default=sys.stdout)
    arguments = parser.parse_args()
    side = Fraction(arguments.side)
    if not 0 < side < 8:
        parser.error("--side must be strictly between 0 and 8")
    objective = PackingObjective(62, float(side))
    print(json.dumps({"squares": 62, "container_side": str(side), "seeds": arguments.seeds, "seconds_per_seed": arguments.seconds_per_seed, "clearance": objective.clearance, "numpy": np.__version__, "scipy": scipy.__version__, "python": sys.version.split()[0]}), file=arguments.output, flush=True)
    for seed in range(arguments.seeds):
        initial = seed_configuration(seed, float(side))
        started = time.monotonic()
        best = initial.copy()
        best_loss = objective(initial)[0]

        def callback(intermediate_result) -> None:
            nonlocal best, best_loss
            if intermediate_result.fun < best_loss:
                best = intermediate_result.x.copy()
                best_loss = float(intermediate_result.fun)
            if time.monotonic() - started >= arguments.seconds_per_seed:
                raise StopIteration

        result = minimize(
            objective, initial, jac=True, method="L-BFGS-B", callback=callback,
            options={"maxiter": 50000, "ftol": 0.0, "gtol": 1e-14, "maxls": 50, "maxcor": 20},
        )
        if result.fun < best_loss:
            best = result.x
        loss, _, violation = objective.evaluate(best)
        geometric_violation = PackingObjective(62, float(side), clearance=0).evaluate(best)[2]
        axis_deviation = np.abs((best.reshape(-1, 3)[:, 2] + math.pi / 4) % (math.pi / 2) - math.pi / 4)
        exact_squares = rationalize(best)
        errors = exact_errors(exact_squares, side)
        record = {
            "seed": seed, "seed_mode": SEED_MODES[seed % len(SEED_MODES)],
            "seconds": round(time.monotonic() - started, 3),
            "iterations": int(result.nit), "termination": str(result.message),
            "squared_violation_sum": loss, "maximum_clearance_violation": violation,
            "maximum_geometric_violation": geometric_violation,
            "maximum_axis_deviation_radians": float(axis_deviation.max()),
            "median_axis_deviation_radians": float(np.median(axis_deviation)),
            "squares_tilted_above_0.001_radians": int(np.sum(axis_deviation > 0.001)),
            "exact_certificate_passed": not errors, "exact_error_count": len(errors),
            "first_exact_error": errors[0] if errors else None,
            "candidate": [
                {"center": [str(coordinate) for coordinate in square.center], "half_angle": str(square.half_angle)}
                for square in exact_squares
            ],
        }
        print(json.dumps(record), file=arguments.output, flush=True)
        if arguments.output is not sys.stdout:
            print(json.dumps({key: value for key, value in record.items() if key != "candidate"}), flush=True)


if __name__ == "__main__":
    main()
