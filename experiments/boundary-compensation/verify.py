from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "near-square-search"))

from exact_geometry import Point, RationalSquare, dot, exact_errors
from row_compensation import ResourceScore, canonical, resource_markings


CONTAINER_SIDE = Fraction(8)
Polygon = tuple[Point, ...]


def dilated_polygon(square: RationalSquare, factor: Fraction) -> Polygon:
    return tuple((horizontal * factor, vertical * factor) for horizontal, vertical in square.vertices)


def contains(square: RationalSquare, factor: Fraction, point: Point) -> bool:
    displacement = tuple(point[axis] / factor - square.center[axis] for axis in (0, 1))
    return all(abs(dot(displacement, axis)) < Fraction(1, 2) for axis in square.axes)


def chord_length(polygon: Polygon, start: Point, end: Point) -> Fraction:
    fixed_axis = 0 if start[0] == end[0] else 1
    height = start[fixed_axis]
    values = tuple(vertex[fixed_axis] for vertex in polygon)
    if not min(values) < height < max(values):
        return Fraction(0)
    section = canonical.clip_halfplane(polygon, fixed_axis, height, 1)
    section = canonical.clip_halfplane(section, fixed_axis, height, -1)
    varying_axis = 1 - fixed_axis
    coordinates = tuple(vertex[varying_axis] for vertex in section)
    lower = max(min(coordinates), min(start[varying_axis], end[varying_axis]))
    upper = min(max(coordinates), max(start[varying_axis], end[varying_axis]))
    return max(Fraction(0), upper - lower)


def resource_score(square: RationalSquare, factor: Fraction, container_side: Fraction = CONTAINER_SIDE) -> ResourceScore:
    polygon = dilated_polygon(square, factor)
    inner_polygon = polygon
    for axis in (0, 1):
        inner_polygon = canonical.clip_halfplane(inner_polygon, axis, Fraction(1), 1)
        inner_polygon = canonical.clip_halfplane(inner_polygon, axis, container_side - 1, -1)
    markings = resource_markings(container_side)
    return ResourceScore(
        canonical.polygon_area(inner_polygon),
        tuple(chord_length(polygon, start, end) for start, end in markings.segments),
        tuple(point for point in markings.corner_points if contains(square, factor, point)),
        tuple(point for point in markings.edge_points if contains(square, factor, point)),
    )


def from_bottom_vertex(horizontal: Fraction, factor: Fraction, cosine: Fraction, sine: Fraction) -> RationalSquare:
    assert cosine**2 + sine**2 == 1
    return RationalSquare(
        (horizontal / factor + (cosine - sine) / 2, (cosine + sine) / 2),
        sine / (1 + cosine),
    )


def translate(square: RationalSquare, factor: Fraction, displacement: Point) -> RationalSquare:
    return RationalSquare(
        tuple(square.center[axis] + displacement[axis] / factor for axis in (0, 1)),
        square.half_angle,
    )


@dataclass(frozen=True)
class Example:
    name: str
    factor: Fraction
    squares: tuple[RationalSquare, ...]

    @property
    def scores(self) -> tuple[ResourceScore, ...]:
        return tuple(resource_score(square, self.factor) for square in self.squares)

    def verify_packing(self) -> None:
        assert self.factor > 1
        assert exact_errors(self.squares, CONTAINER_SIDE / self.factor) == ()


def examples() -> tuple[Example, ...]:
    original = from_bottom_vertex(
        canonical.VERTEX_HORIZONTAL, canonical.FACTOR, canonical.COSINE, canonical.SINE,
    )
    corner_neighbor = RationalSquare(tuple(reversed(original.center)), original.half_angle)
    shifted = translate(original, canonical.FACTOR, (-Fraction(1, 500), Fraction(0)))
    shifted_neighbor = translate(shifted, canonical.FACTOR, (canonical.FACTOR / canonical.SINE, Fraction(0)))
    factor = Fraction(1000001, 1000000)
    sine = Fraction(9999, 10001)
    low_angle = from_bottom_vertex(Fraction(990799, 499950), factor, Fraction(200, 10001), sine)
    low_angle_neighbor = translate(low_angle, factor, (factor / sine, Fraction(0)))
    corner_factor = 1 + Fraction(1, 10**12)
    rotation_parameter = 10**7
    tiny_cosine = Fraction(2 * rotation_parameter, rotation_parameter**2 + 1)
    tiny_sine = Fraction(rotation_parameter**2 - 1, rotation_parameter**2 + 1)
    tiny_corner_square = from_bottom_vertex(
        1 + (corner_factor - Fraction(19, 20) * tiny_cosine) / tiny_sine,
        corner_factor, tiny_cosine, tiny_sine,
    )
    other_bottom_square = from_bottom_vertex(
        1 + (corner_factor - Fraction(929, 1000) * canonical.COSINE) / canonical.SINE,
        corner_factor, canonical.COSINE, canonical.SINE,
    )
    other_corner_square = RationalSquare(
        (other_bottom_square.center[1], other_bottom_square.center[0]),
        -other_bottom_square.half_angle,
    )
    return (
        Example("adjacent Q owner does not repay the deficit", canonical.FACTOR, (original, corner_neighbor)),
        Example("nearest P owner need not cover the next P", canonical.FACTOR, (shifted, shifted_neighbor)),
        Example("nearest P owner does not repay the deficit", factor, (low_angle, low_angle_neighbor)),
        Example("two bad squares can own adjacent Q points", corner_factor, (tiny_corner_square, other_corner_square)),
    )


def vertical_propagation_counterexample() -> Example:
    factor = Fraction(10001, 10000)
    cosine = Fraction(119, 169)
    sine = Fraction(120, 169)
    center = (
        1 + Fraction(43, 100) * cosine + Fraction(4, 25) * sine,
        Fraction(9, 10) - Fraction(43, 100) * sine + Fraction(4, 25) * cosine,
    )
    square = RationalSquare((center[0] / factor, center[1] / factor), -sine / (1 + cosine))
    return Example("missing upper point does not force a neighboring vertical crossing", factor, (square,))


def main() -> None:
    checked_examples = examples()
    assert sum(score.total for score in checked_examples[0].scores) < 2
    for example in checked_examples[1:3]:
        assert example.scores[1].covered_edge_points == ((Fraction(2), Fraction(9, 10)),)
    assert sum(score.total for score in checked_examples[2].scores) < 2
    assert all(score.total < 1 for score in checked_examples[3].scores)
    assert all(example.scores[0].total < 1 for example in checked_examples)
    propagation = vertical_propagation_counterexample()
    square = propagation.squares[0]
    assert contains(square, propagation.factor, (Fraction(1), Fraction(9, 10)))
    assert not contains(square, propagation.factor, (Fraction(1), Fraction(1)))
    for horizontal in (Fraction(0), Fraction(2)):
        assert chord_length(
            dilated_polygon(square, propagation.factor),
            (horizontal, Fraction(9, 10)), (horizontal, Fraction(1)),
        ) == 0
    for example in checked_examples + (propagation,):
        example.verify_packing()
        scores = example.scores
        print(json.dumps({
            "example": example.name,
            "square_side": str(example.factor),
            "container_side": str(CONTAINER_SIDE),
            "scores": [str(score.total) for score in scores],
            "total": str(sum(score.total for score in scores)),
            "Q": [[tuple(map(str, point)) for point in score.covered_corner_points] for score in scores],
            "P": [[tuple(map(str, point)) for point in score.covered_edge_points] for score in scores],
        }))


if __name__ == "__main__":
    main()
