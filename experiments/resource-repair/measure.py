from fractions import Fraction
import importlib.util
from pathlib import Path


Number = Fraction | float
Point = tuple[Number, Number]
Polygon = tuple[Point, ...]


source = Path(__file__).resolve().parents[2] / "scripts" / "check-nagamochi-counterexample.py"
specification = importlib.util.spec_from_file_location("nagamochi_counterexample", source)
assert specification is not None and specification.loader is not None
canonical = importlib.util.module_from_spec(specification)
specification.loader.exec_module(canonical)


def square_polygon(center: Point, cosine: Number, sine: Number, size: Number) -> Polygon:
    return tuple(
        (
            center[0] + size * (first * cosine - second * sine) / 2,
            center[1] + size * (first * sine + second * cosine) / 2,
        )
        for first, second in ((-1, -1), (1, -1), (1, 1), (-1, 1))
    )


def covered_segment_fraction(center: Point, cosine: Number, sine: Number, size: Number, start: Point, end: Point) -> Number:
    lower, upper = 0, 1
    for axis in ((cosine, sine), (-sine, cosine)):
        initial = (start[0] - center[0]) * axis[0] + (start[1] - center[1]) * axis[1]
        slope = (end[0] - start[0]) * axis[0] + (end[1] - start[1]) * axis[1]
        if slope == 0:
            if not -size / 2 < initial < size / 2:
                return size * 0
        else:
            crossings = ((-size / 2 - initial) / slope, (size / 2 - initial) / slope)
            lower = max(lower, min(crossings))
            upper = min(upper, max(crossings))
    return max(0, upper - lower)


def score(
    center: Point, cosine: Number, sine: Number, size: Number, container: int,
    point_offset: Number, line_offset: Number, corner_weight: Number,
    diagonal_weight: Number = 0,
) -> tuple[Number, Number, tuple[Number, ...], tuple[Point, ...], tuple[Point, ...], tuple[Number, ...]]:
    polygon = square_polygon(center, cosine, sine, size)
    for axis in (0, 1):
        polygon = canonical.clip_halfplane(polygon, axis, 1, 1)
        polygon = canonical.clip_halfplane(polygon, axis, container - 1, -1)
    area = canonical.polygon_area(polygon)
    segments = tuple(((line_offset, height), (container - line_offset, height)) for height in (1, container - 1)) + tuple(
        ((horizontal, line_offset), (horizontal, container - line_offset)) for horizontal in (1, container - 1)
    )
    lengths = tuple(
        covered_segment_fraction(center, cosine, sine, size, start, end)
        * (abs(end[0] - start[0]) + abs(end[1] - start[1]))
        for start, end in segments
    )
    corner_points = tuple((horizontal, vertical) for horizontal in (point_offset, container - point_offset) for vertical in (1, container - 1)) + tuple(
        (horizontal, vertical) for horizontal in (1, container - 1) for vertical in (point_offset, container - point_offset)
    )
    edge_points = tuple((horizontal, vertical) for horizontal in range(2, container - 1) for vertical in (point_offset, container - point_offset)) + tuple(
        (horizontal, vertical) for horizontal in (point_offset, container - point_offset) for vertical in range(2, container - 1)
    )

    def contains(point: Point) -> bool:
        displacement = point[0] - center[0], point[1] - center[1]
        return abs(displacement[0] * cosine + displacement[1] * sine) < size / 2 and abs(-displacement[0] * sine + displacement[1] * cosine) < size / 2

    corners = tuple(point for point in corner_points if contains(point))
    edges = tuple(point for point in edge_points if contains(point))
    diagonal_segments = tuple(
        (
            (point_offset if first == 0 else container - point_offset, 1 if second == 0 else container - 1),
            (1 if first == 0 else container - 1, point_offset if second == 0 else container - point_offset),
        )
        for first in range(2) for second in range(2)
    )
    diagonal_fractions = tuple(
        covered_segment_fraction(center, cosine, sine, size, start, end)
        for start, end in diagonal_segments
    )
    total = area + sum(lengths) / 2 + corner_weight * len(corners) + Fraction(1, 2) * len(edges) + diagonal_weight * sum(diagonal_fractions)
    return total, area, lengths, corners, edges, diagonal_fractions
