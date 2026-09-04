from dataclasses import dataclass
from fractions import Fraction

from measure import canonical, score, square_polygon


SIZE = Fraction(10001, 10000)
OFFSET = Fraction(9, 10)


@dataclass(frozen=True)
class Square:
    center: tuple[Fraction, Fraction]
    cosine: Fraction = Fraction(1)
    sine: Fraction = Fraction(0)

    def evaluate(self, line_offset: Fraction, corner_weight: Fraction, diagonal_weight: Fraction = Fraction(0)):
        polygon = square_polygon(self.center, self.cosine, self.sine, SIZE)
        assert self.cosine**2 + self.sine**2 == 1
        assert all(0 <= coordinate <= 4 for vertex in polygon for coordinate in vertex)
        assert canonical.polygon_area(polygon) == SIZE**2
        return score(self.center, self.cosine, self.sine, SIZE, 4, OFFSET, line_offset, corner_weight, diagonal_weight)


def bottom_square(left: Fraction) -> Square:
    return Square((left + SIZE / 2, SIZE / 2))


LEFT_WITNESS = bottom_square(Fraction(9001, 10000))
RIGHT_WITNESS = bottom_square(Fraction(4999, 5000))
CORNER_WITNESS = bottom_square(Fraction(0))
EDGE_WITNESS = bottom_square(Fraction(11, 10))
ORIGINAL_WITNESS = Square(
    tuple(sum(vertex[axis] for vertex in canonical.SQUARE) / 4 for axis in (0, 1)),
    canonical.COSINE, canonical.SINE,
)


def diagonal_affine(square: Square) -> tuple[Fraction, Fraction]:
    intercept = square.evaluate(Fraction(1), Fraction(0), Fraction(1))[0]
    half_value = square.evaluate(Fraction(1), Fraction(1, 2))[0]
    return intercept, 2 * (half_value - intercept)


def original_layout_dual() -> tuple[tuple[Fraction, ...], Fraction]:
    edge, corner, original = (
        square.evaluate(OFFSET, Fraction(9, 20))
        for square in (EDGE_WITNESS, CORNER_WITNESS, ORIGINAL_WITNESS)
    )
    assert (len(edge[3]), len(edge[4])) == (0, 1)
    assert (len(corner[3]), len(corner[4])) == (2, 0)
    assert (len(original[3]), len(original[4])) == (1, 0)
    edge_multiplier = Fraction(4)
    corner_multiplier = (
        Fraction(44, 5) - edge_multiplier * sum(edge[2]) - 8 * sum(original[2])
    ) / (sum(corner[2]) - 2 * sum(original[2]))
    original_multiplier = 8 - 2 * corner_multiplier
    multipliers = edge_multiplier, corner_multiplier, original_multiplier
    assert all(multiplier > 0 for multiplier in multipliers)
    assert sum(multiplier * sum(features[2]) for multiplier, features in zip(multipliers, (edge, corner, original))) == Fraction(44, 5)
    assert sum(multiplier * len(features[3]) for multiplier, features in zip(multipliers, (edge, corner, original))) == 8
    assert sum(multiplier * len(features[4]) for multiplier, features in zip(multipliers, (edge, corner, original))) == 4
    minimum_total_mass = 4 + sum(
        multiplier * (1 - features[1]) for multiplier, features in zip(multipliers, (edge, corner, original))
    )
    assert minimum_total_mass > 14
    return multipliers, minimum_total_mass


def variable_area_dual() -> tuple[tuple[Fraction, ...], Fraction]:
    multipliers, _ = original_layout_dual()
    weighted_area = sum(
        multiplier * square.evaluate(OFFSET, Fraction(9, 20))[1]
        for multiplier, square in zip(multipliers, (EDGE_WITNESS, CORNER_WITNESS, ORIGINAL_WITNESS))
    )
    inside_multiplier = (4 - weighted_area) / SIZE**2
    assert inside_multiplier > 0
    assert inside_multiplier * SIZE**2 + weighted_area == 4
    inside = Square((Fraction(2), Fraction(2))).evaluate(OFFSET, Fraction(9, 20))
    assert inside[1] == SIZE**2 and not any(inside[2]) and not inside[3] and not inside[4]
    all_multipliers = multipliers + (inside_multiplier,)
    minimum_total_mass = sum(all_multipliers)
    assert minimum_total_mass > 14
    return all_multipliers, minimum_total_mass


def main() -> None:
    trimmed_score = LEFT_WITNESS.evaluate(Fraction(1), Fraction(1, 2))[0]
    assert trimmed_score == Fraction(47512001, 50000000) < 1
    canonical.display("Trimmed-line repair: left witness score", trimmed_score)
    left_intercept, left_slope = diagonal_affine(LEFT_WITNESS)
    right_intercept, right_slope = diagonal_affine(RIGHT_WITNESS)
    assert left_slope < 0 < right_slope
    upper_weight = (1 - left_intercept) / left_slope
    lower_weight = (1 - right_intercept) / right_slope
    assert upper_weight < lower_weight
    print(f"Uniform diagonal: left score = {left_intercept} + ({left_slope}) * w")
    print(f"Uniform diagonal: right score = {right_intercept} + ({right_slope}) * w")
    canonical.display("Left witness requires w at most", upper_weight)
    canonical.display("Right witness requires w at least", lower_weight)
    multipliers, minimum_mass = original_layout_dual()
    print(f"Original-layout dual multipliers (edge, corner, original): {multipliers}")
    canonical.display("Original layout: necessary total mass", minimum_mass)
    _, variable_area_mass = variable_area_dual()
    canonical.display("Original layout, also varying area weight: necessary total mass", variable_area_mass)
    print("All calculations are exact Python checks, not Lean proofs. No general packing theorem follows.")


if __name__ == "__main__":
    main()
