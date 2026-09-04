from dataclasses import dataclass
from fractions import Fraction


Point = tuple[Fraction, Fraction]


@dataclass(frozen=True)
class RationalSquare:
    center: Point
    half_angle: Fraction

    @property
    def axes(self) -> tuple[Point, Point]:
        denominator = 1 + self.half_angle**2
        cosine = (1 - self.half_angle**2) / denominator
        sine = 2 * self.half_angle / denominator
        return (cosine, sine), (-sine, cosine)

    @property
    def vertices(self) -> tuple[Point, ...]:
        horizontal, vertical = self.axes
        return tuple(
            (
                self.center[0] + (first * horizontal[0] + second * vertical[0]) / 2,
                self.center[1] + (first * horizontal[1] + second * vertical[1]) / 2,
            )
            for first, second in ((-1, -1), (-1, 1), (1, 1), (1, -1))
        )


def dot(first: Point, second: Point) -> Fraction:
    return first[0] * second[0] + first[1] * second[1]


def exact_errors(squares: tuple[RationalSquare, ...], side: Fraction) -> tuple[str, ...]:
    errors: list[str] = []
    polygons = tuple(square.vertices for square in squares)
    for index, polygon in enumerate(polygons):
        if any(not 0 <= coordinate <= side for vertex in polygon for coordinate in vertex):
            errors.append(f"square {index} crosses the container boundary")
    for first in range(len(squares)):
        for second in range(first + 1, len(squares)):
            separated = False
            for axis in squares[first].axes + squares[second].axes:
                first_projection = tuple(dot(vertex, axis) for vertex in polygons[first])
                second_projection = tuple(dot(vertex, axis) for vertex in polygons[second])
                if (
                    max(first_projection) <= min(second_projection)
                    or max(second_projection) <= min(first_projection)
                ):
                    separated = True
                    break
            if not separated:
                errors.append(f"squares {first} and {second} overlap in their interiors")
    return tuple(errors)
