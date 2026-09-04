from decimal import Decimal, localcontext
from fractions import Fraction
from typing import Literal


Point = tuple[Fraction, Fraction]
Polygon = tuple[Point, ...]
Axis = Literal[0, 1]

FACTOR = Fraction(10001, 10000)
COSINE = Fraction(80, 1601)
SINE = Fraction(1599, 1601)
CONTAINER_SIDE = Fraction(4)
RESOURCE_OFFSET = Fraction(9, 10)
VERTEX_HORIZONTAL = Fraction(2) - COSINE / SINE * RESOURCE_OFFSET - Fraction(1, 10000)
SQUARE: Polygon = (
    (VERTEX_HORIZONTAL, Fraction(0)),
    (VERTEX_HORIZONTAL + FACTOR * COSINE, FACTOR * SINE),
    (VERTEX_HORIZONTAL + FACTOR * (COSINE - SINE), FACTOR * (COSINE + SINE)),
    (VERTEX_HORIZONTAL - FACTOR * SINE, FACTOR * COSINE),
)


def polygon_edges(polygon: Polygon) -> tuple[tuple[Point, Point], ...]:
    return tuple(zip(polygon, polygon[1:] + polygon[:1]))


def interpolate(start: Point, end: Point, ratio: Fraction) -> Point:
    return (
        start[0] + ratio * (end[0] - start[0]),
        start[1] + ratio * (end[1] - start[1]),
    )


def clip_halfplane(polygon: Polygon, axis: Axis, bound: Fraction, sign: int) -> Polygon:
    result: list[Point] = []
    for start, end in polygon_edges(polygon):
        start_distance = sign * (start[axis] - bound)
        end_distance = sign * (end[axis] - bound)
        if start_distance >= 0:
            result.append(start)
        if (start_distance < 0) != (end_distance < 0):
            ratio = start_distance / (start_distance - end_distance)
            result.append(interpolate(start, end, ratio))
    return tuple(result)


def polygon_area(polygon: Polygon) -> Fraction:
    return abs(sum(
        (start[0] * end[1] - start[1] * end[0] for start, end in polygon_edges(polygon)),
        Fraction(0),
    )) / 2


def local_coordinates(point: Point) -> Point:
    horizontal = point[0] - VERTEX_HORIZONTAL
    vertical = point[1]
    return COSINE * horizontal + SINE * vertical, -SINE * horizontal + COSINE * vertical


def contains_interior(point: Point) -> bool:
    local_horizontal, local_vertical = local_coordinates(point)
    return 0 < local_horizontal < FACTOR and 0 < local_vertical < FACTOR


def lies_on_square_boundary(point: Point) -> bool:
    local_horizontal, local_vertical = local_coordinates(point)
    return (
        0 <= local_horizontal <= FACTOR
        and 0 <= local_vertical <= FACTOR
        and (local_horizontal in (0, FACTOR) or local_vertical in (0, FACTOR))
    )


def resource_chord_length(axis: Axis, height: Fraction) -> Fraction:
    intersection_coordinates: list[Fraction] = []
    for start, end in polygon_edges(SQUARE):
        if start[axis] == end[axis]:
            if start[axis] == height:
                intersection_coordinates.extend((start[1 - axis], end[1 - axis]))
        elif (start[axis] - height) * (end[axis] - height) <= 0:
            ratio = (height - start[axis]) / (end[axis] - start[axis])
            intersection_coordinates.append(interpolate(start, end, ratio)[1 - axis])
    if not intersection_coordinates:
        return Fraction(0)
    lower = max(min(intersection_coordinates), RESOURCE_OFFSET)
    upper = min(max(intersection_coordinates), CONTAINER_SIDE - RESOURCE_OFFSET)
    return max(Fraction(0), upper - lower)


def display(name: str, value: Fraction) -> None:
    with localcontext() as context:
        context.prec = 26
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
    print(f"{name}: {value} = {decimal}")


def main() -> None:
    assert COSINE**2 + SINE**2 == 1
    assert 1 < FACTOR <= Fraction(101, 100)
    assert polygon_area(SQUARE) == FACTOR**2
    assert all(0 <= coordinate <= CONTAINER_SIDE for point in SQUARE for coordinate in point)

    inner_polygon = SQUARE
    for axis in (0, 1):
        inner_polygon = clip_halfplane(inner_polygon, axis, Fraction(1), 1)
        inner_polygon = clip_halfplane(inner_polygon, axis, CONTAINER_SIDE - 1, -1)
    inner_area = polygon_area(inner_polygon)
    boundary_lengths = (
        resource_chord_length(1, Fraction(1)),
        resource_chord_length(1, CONTAINER_SIDE - 1),
        resource_chord_length(0, Fraction(1)),
        resource_chord_length(0, CONTAINER_SIDE - 1),
    )
    corner_points = tuple(
        (horizontal, vertical)
        for horizontal in (RESOURCE_OFFSET, CONTAINER_SIDE - RESOURCE_OFFSET)
        for vertical in (Fraction(1), CONTAINER_SIDE - 1)
    ) + tuple(
        (horizontal, vertical)
        for horizontal in (Fraction(1), CONTAINER_SIDE - 1)
        for vertical in (RESOURCE_OFFSET, CONTAINER_SIDE - RESOURCE_OFFSET)
    )
    edge_points = tuple(
        (Fraction(2), vertical)
        for vertical in (RESOURCE_OFFSET, CONTAINER_SIDE - RESOURCE_OFFSET)
    ) + tuple(
        (horizontal, Fraction(2))
        for horizontal in (RESOURCE_OFFSET, CONTAINER_SIDE - RESOURCE_OFFSET)
    )
    corner_score = Fraction(9, 20) * sum(map(contains_interior, corner_points))
    edge_score = Fraction(1, 2) * sum(map(contains_interior, edge_points))
    score = inner_area + sum(boundary_lengths) / 2 + corner_score + edge_score

    assert not any(map(lies_on_square_boundary, corner_points + edge_points))
    assert tuple(filter(contains_interior, corner_points)) == ((Fraction(1), RESOURCE_OFFSET),)
    assert inner_area == Fraction(611022059041, 25584000000000)
    assert boundary_lengths == (Fraction(1251468079, 1279200000), 0, Fraction(29, 1000), 0)
    assert corner_score == Fraction(9, 20)
    assert edge_score == 0
    assert score == Fraction(25009470849041, 25584000000000)
    assert score < Fraction(99, 100) < 1

    display("Factor", FACTOR)
    display("Inner area", inner_area)
    for name, length in zip(("Bottom", "Top", "Left", "Right"), boundary_lengths):
        display(f"{name} boundary length", length)
    display("Q score", corner_score)
    display("P score", edge_score)
    display("Total score", score)
    display("Deficit below one", 1 - score)


if __name__ == "__main__":
    main()
