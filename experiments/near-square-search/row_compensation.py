from dataclasses import dataclass
from fractions import Fraction
import importlib.util
from itertools import combinations
from pathlib import Path


Point = tuple[Fraction, Fraction]
Polygon = tuple[Point, ...]

source = Path(__file__).resolve().parents[2] / "scripts" / "check-nagamochi-counterexample.py"
specification = importlib.util.spec_from_file_location("nagamochi_counterexample", source)
assert specification is not None and specification.loader is not None
canonical = importlib.util.module_from_spec(specification)
specification.loader.exec_module(canonical)

CONTAINER_SIDE = Fraction(8)
STEP = canonical.FACTOR / canonical.SINE


def translated_square(index: int) -> Polygon:
    return tuple((horizontal + index * STEP, vertical) for horizontal, vertical in canonical.SQUARE)


def local_coordinates(index: int, point: Point) -> Point:
    return canonical.local_coordinates((point[0] - index * STEP, point[1]))


def contains_interior(index: int, point: Point) -> bool:
    return canonical.contains_interior((point[0] - index * STEP, point[1]))


def chord_length(index: int, start: Point, end: Point) -> Fraction:
    assert start[0] == end[0] or start[1] == end[1]
    local_start = local_coordinates(index, start)
    local_end = local_coordinates(index, end)
    lower, upper = Fraction(0), Fraction(1)
    for coordinate in range(2):
        slope = local_end[coordinate] - local_start[coordinate]
        if slope == 0:
            if not 0 < local_start[coordinate] < canonical.FACTOR:
                return Fraction(0)
        else:
            crossings = (-local_start[coordinate] / slope, (canonical.FACTOR - local_start[coordinate]) / slope)
            lower = max(lower, min(crossings))
            upper = min(upper, max(crossings))
    length = abs(end[0] - start[0]) + abs(end[1] - start[1])
    return length * max(Fraction(0), upper - lower)


@dataclass(frozen=True)
class ResourceScore:
    area: Fraction
    chord_lengths: tuple[Fraction, ...]
    covered_corner_points: tuple[Point, ...]
    covered_edge_points: tuple[Point, ...]

    @property
    def total(self) -> Fraction:
        return (
            self.area
            + sum(self.chord_lengths) / 2
            + Fraction(9, 20) * len(self.covered_corner_points)
            + Fraction(1, 2) * len(self.covered_edge_points)
        )


@dataclass(frozen=True)
class ResourceMarkings:
    segments: tuple[tuple[Point, Point], ...]
    corner_points: tuple[Point, ...]
    edge_points: tuple[Point, ...]


def resource_markings(container_side: Fraction) -> ResourceMarkings:
    assert container_side.denominator == 1 and container_side >= 3
    offset = canonical.RESOURCE_OFFSET
    segments = tuple(
        ((offset, height), (container_side - offset, height))
        for height in (Fraction(1), container_side - 1)
    ) + tuple(
        ((horizontal, offset), (horizontal, container_side - offset))
        for horizontal in (Fraction(1), container_side - 1)
    )
    corner_points = tuple(point for segment in segments for point in segment)
    edge_points = tuple(
        (Fraction(horizontal), vertical)
        for horizontal in range(2, int(container_side) - 1)
        for vertical in (offset, container_side - offset)
    ) + tuple(
        (horizontal, Fraction(vertical))
        for vertical in range(2, int(container_side) - 1)
        for horizontal in (offset, container_side - offset)
    )
    return ResourceMarkings(segments, corner_points, edge_points)


def resource_score(index: int, container_side: Fraction = CONTAINER_SIDE) -> ResourceScore:
    markings = resource_markings(container_side)
    inner_polygon = translated_square(index)
    for axis in (0, 1):
        inner_polygon = canonical.clip_halfplane(inner_polygon, axis, Fraction(1), 1)
        inner_polygon = canonical.clip_halfplane(inner_polygon, axis, container_side - 1, -1)
    assert not any(
        canonical.lies_on_square_boundary((point[0] - index * STEP, point[1]))
        for point in markings.corner_points + markings.edge_points
    )
    return ResourceScore(
        canonical.polygon_area(inner_polygon),
        tuple(chord_length(index, start, end) for start, end in markings.segments),
        tuple(point for point in markings.corner_points if contains_interior(index, point)),
        tuple(point for point in markings.edge_points if contains_interior(index, point)),
    )


def fits(polygon: Polygon) -> bool:
    return all(0 <= coordinate <= CONTAINER_SIDE for vertex in polygon for coordinate in vertex)


def separated(first: Polygon, second: Polygon) -> bool:
    for axis in ((canonical.COSINE, canonical.SINE), (-canonical.SINE, canonical.COSINE)):
        first_projection = tuple(vertex[0] * axis[0] + vertex[1] * axis[1] for vertex in first)
        second_projection = tuple(vertex[0] * axis[0] + vertex[1] * axis[1] for vertex in second)
        if max(first_projection) <= min(second_projection) or max(second_projection) <= min(first_projection):
            return True
    return False


def main() -> None:
    row = tuple(translated_square(index) for index in range(6))
    assert canonical.FACTOR > 1
    assert all(fits(square) for square in row)
    assert all(canonical.polygon_area(square) == canonical.FACTOR**2 for square in row)
    assert all(separated(first, second) for first, second in combinations(row, 2))
    assert not fits(translated_square(6))
    scores = tuple(resource_score(index) for index in range(6))
    assert scores[0].total < 1
    assert all(score.total > 1 for score in scores[1:])
    assert sum(score.total for score in scores) > 6
    canonical.display("Square side", canonical.FACTOR)
    canonical.display("Horizontal step", STEP)
    print("Six translated squares fit in 8 by 8 and have disjoint interiors.")
    print("The seventh square crosses the right wall.")
    for index, score in enumerate(scores):
        canonical.display(f"Square {index + 1} score", score.total)
        print(f"  Q points: {score.covered_corner_points}; P points: {score.covered_edge_points}")
    canonical.display("Row score", sum(score.total for score in scores))
    print("This is an exact Python calculation for one row, not a Lean proof or a general compensation theorem.")


if __name__ == "__main__":
    main()
