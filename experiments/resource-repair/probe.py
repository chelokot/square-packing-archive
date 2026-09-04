import argparse
from fractions import Fraction
import math

from scipy.optimize import differential_evolution

from measure import score, square_polygon


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=4)
    parser.add_argument("--offset", default="0.9")
    parser.add_argument("--line-offset", default="1")
    parser.add_argument("--corner-weight", default="0.5")
    parser.add_argument("--size", default="1.0001")
    parser.add_argument("--container", type=int, default=4)
    parser.add_argument("--region", choices=("all", "boundary", "bottom", "corner"), default="boundary")
    parser.add_argument("--diagonal", action="store_true")
    arguments = parser.parse_args()
    offset, line_offset, corner_weight, size = map(Fraction, (arguments.offset, arguments.line_offset, arguments.corner_weight, arguments.size))
    container = arguments.container
    diagonal_weight = 1 - 2 * corner_weight if arguments.diagonal else Fraction(0)

    def center_from_parameters(extent, horizontal, vertical):
        horizontal_limit = 1 if arguments.region == "corner" else Fraction(container, 2)
        vertical_limit = Fraction(container, 2) if arguments.region == "all" else 1
        return (
            extent + (horizontal_limit - extent) * horizontal,
            extent if arguments.region == "bottom" else extent + (vertical_limit - extent) * vertical,
        )

    def objective(variables):
        angle, horizontal, vertical = variables
        cosine, sine = math.cos(angle), math.sin(angle)
        extent = float(size) * (abs(cosine) + abs(sine)) / 2
        center = center_from_parameters(extent, horizontal, vertical)
        return float(score(center, cosine, sine, float(size), container, float(offset), float(line_offset), float(corner_weight), float(diagonal_weight))[0])

    mass = (container - 2)**2 + 2 * (container - 2 * line_offset) + 8 * corner_weight + 2 * (container - 3) + 4 * diagonal_weight
    print(f"Total resource mass {mass}; target {container**2 - 2}", flush=True)
    for seed in range(arguments.seeds):
        result = differential_evolution(objective, ((-math.pi / 4, math.pi / 4), (0, 1), (0, 1)), seed=seed, popsize=20, maxiter=300, tol=1e-11, polish=False)
        half_angle = Fraction(str(math.tan(result.x[0] / 2)))
        cosine = (1 - half_angle**2) / (1 + half_angle**2)
        sine = 2 * half_angle / (1 + half_angle**2)
        extent = size * (abs(cosine) + abs(sine)) / 2
        center = center_from_parameters(extent, Fraction(str(result.x[1])), Fraction(str(result.x[2])))
        polygon = square_polygon(center, cosine, sine, size)
        assert all(0 <= coordinate <= container for vertex in polygon for coordinate in vertex)
        exact_score = score(center, cosine, sine, size, container, offset, line_offset, corner_weight, diagonal_weight)
        print(f"seed={seed} evaluations={result.nfev} score={float(exact_score[0]):.16g} below_one={exact_score[0] < 1}", flush=True)
        print(f"center={center}; half_angle={half_angle}", flush=True)
        print(f"area={float(exact_score[1])}; lengths={tuple(map(float, exact_score[2]))}; Q={exact_score[3]}; P={exact_score[4]}; diagonal_fractions={tuple(map(float, exact_score[5]))}", flush=True)


if __name__ == "__main__":
    main()
