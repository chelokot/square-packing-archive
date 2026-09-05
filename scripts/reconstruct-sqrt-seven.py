from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from collections.abc import Callable
import json
import math


@dataclass(frozen=True)
class Quadratic:
    rational: Fraction = Fraction(0)
    radical: Fraction = Fraction(0)

    def __add__(self, other: Scalar) -> Quadratic:
        other = quadratic(other)
        return Quadratic(self.rational + other.rational, self.radical + other.radical)

    __radd__ = __add__

    def __neg__(self) -> Quadratic:
        return Quadratic(-self.rational, -self.radical)

    def __sub__(self, other: Scalar) -> Quadratic:
        return self + -quadratic(other)

    def __rsub__(self, other: Scalar) -> Quadratic:
        return quadratic(other) + -self

    def __mul__(self, other: Scalar) -> Quadratic:
        other = quadratic(other)
        return Quadratic(self.rational * other.rational + 7 * self.radical * other.radical,
                         self.rational * other.radical + self.radical * other.rational)

    __rmul__ = __mul__

    def __truediv__(self, other: Scalar) -> Quadratic:
        other = quadratic(other)
        denominator = other.rational ** 2 - 7 * other.radical ** 2
        return self * Quadratic(other.rational / denominator, -other.radical / denominator)

    def __float__(self) -> float:
        return float(self.rational) + float(self.radical) * math.sqrt(7)


Scalar = Quadratic | Fraction | int
Point = tuple[Scalar, Scalar]


def quadratic(value: Scalar) -> Quadratic:
    return value if isinstance(value, Quadratic) else Quadratic(Fraction(value))


@dataclass(frozen=True)
class Square:
    center_x: Quadratic
    center_y: Quadratic
    cosine: Quadratic = Quadratic(Fraction(1))
    sine: Quadratic = Quadratic()


def square(center_x: Scalar, center_y: Scalar, cosine: Scalar = 1, sine: Scalar = 0) -> Square:
    return Square(*(quadratic(value) for value in (center_x, center_y, cosine, sine)))


Packing = tuple[list[Square], Quadratic]


def reflected(item: Square, side: Quadratic) -> Square:
    return square(side - item.center_x, side - item.center_y, item.cosine, item.sine)


half = Fraction(1, 2)
root_seven = Quadratic(Fraction(0), Fraction(1))
cosine = (root_seven + 1) / 4
sine = (root_seven - 1) / 4


def rotated_pair(origin_x: Quadratic, origin_y: Quadratic) -> list[Square]:
    return [square(origin_x + cosine * half - sine * (row + half),
                   origin_y + sine * half + cosine * (row + half), cosine, sine)
            for row in range(2)]


def eighteen_hamalainen() -> Packing:
    side = (7 + root_seven) / 2
    items = [square(half, row + half) for row in range(3)]
    items += [square(1 + half, half), square(half, side - half)]
    origin_x = Fraction(5, 2) + root_seven / 2 - cosine + Fraction(3, 4) * sine
    origin_y = 1 - sine + Fraction(3, 4) * sine * sine / cosine
    items += rotated_pair(origin_x, origin_y)
    origin_x = (Fraction(3, 2) * sine * cosine - 2 * sine + root_seven * sine * cosine / 2
                + Fraction(5, 2) - cosine * cosine + root_seven / 2 - cosine)
    origin_y = (Fraction(5, 2) - Fraction(3, 2) * cosine * cosine + 2 * cosine
                + root_seven / 2 - root_seven * cosine * cosine / 2 - sine * cosine - sine)
    items += rotated_pair(origin_x, origin_y)
    return items + [reflected(item, side) for item in items], side


def eighteen_gustafsson() -> Packing:
    side = (7 + root_seven) / 2
    items = [square(half, row + half) for row in range(2)]
    items += [square(side - column - half, row + half)
              for row, length in enumerate((3, 2)) for column in range(length)]
    items += [square(half, side - row - half) for row in range(2)]
    items += [square(1 + half, side - half)]
    items += [square(side - column - half, side - row - half)
              for row in range(2) for column in range(2)]
    origin_x = 1 + Fraction(5, 4) * sine
    origin_y = Fraction(3, 2) + root_seven / 2 - Fraction(3, 4) * sine * sine / cosine - 2 * cosine
    pair = rotated_pair(origin_x, origin_y)
    items += pair + [square(side - 1 - item.center_x, side - item.center_y, cosine, sine)
                     for item in pair]
    return items, side


def eighteen_cantrell() -> Packing:
    side = (7 + root_seven) / 2
    items = [square(column + half, row + half) for row in range(3) for column in range(3 - row)]
    items += [square(half, side - half)]
    items += [square(side - column - half, side - row - half)
              for row in range(2) for column in range(2 - row)]
    origins = ((quadratic(3), sine),
               (quadratic(Fraction(7, 2)), (-19 + 13 * root_seven) / 12),
               ((11 - root_seven) / 4, (3 + root_seven) / 4),
               ((19 - 3 * root_seven) / 8, (5 + 5 * root_seven) / 8),
               ((119 - 11 * root_seven) / 32, (-137 + 131 * root_seven) / 96),
               ((107 - 15 * root_seven) / 32, (-149 + 167 * root_seven) / 96))
    for origin_x, origin_y in origins:
        items.append(square(origin_x + (cosine + sine) / 2,
                            origin_y + (cosine - sine) / 2, cosine, -sine))
    cosine_b = quadratic(171) / (184 + 4 * root_seven)
    sine_b = (32 + 23 * root_seven) / (184 + 4 * root_seven)
    origins = (((29699 - 381 * root_seven) / 43808, (134423 + 1969 * root_seven) / 43808),
               (quadratic(Fraction(3619, 2664)) + root_seven / 296,
                quadratic(Fraction(95, 37)) + 77 * root_seven / 148))
    for origin_x, origin_y in origins:
        items.append(square(origin_x + (cosine_b + sine_b) / 2,
                            origin_y + (cosine_b - sine_b) / 2, cosine_b, -sine_b))
    return [square(item.center_x, side - item.center_y, item.cosine, -item.sine)
            for item in items], side


def eighteen_gensane_ryckelynck() -> Packing:
    side = (7 + root_seven) / 2
    items = [square(half, row + half) for row in range(3)]
    items += [square(1 + half, half)]
    items += [square(column + half, side - half) for column in range(2)]
    items += rotated_pair((4 + 2 * root_seven) / 3, quadratic(1))
    items += [square((25 + root_seven) / 16 + (sine + cosine) / 2,
                     (23 + root_seven) / 16 + (sine - cosine) / 2, cosine, sine)]
    return items + [reflected(item, side) for item in items], side


def eighty_six() -> Packing:
    side = (17 + root_seven) / 2
    items = [square(column + half, row + half)
             for row in range(7) for column in range(7 - row)]
    items += [square(side - column - half, side - row - half)
              for row in range(7) for column in range(8 - row)]
    items += [square(side - column - half, row + half) for row in range(2) for column in range(2)]
    items += [square(half, side - half)]
    for row, offset in enumerate((0, half, 1, 1, Fraction(3, 2), 2, Fraction(5, 2), Fraction(5, 2), 3)):
        for column in range(2):
            local_x = column + half + offset - Fraction(5, 4)
            local_y = row + half
            items.append(square(side - 2 + sine * local_x - cosine * local_y,
                                2 + cosine * local_x + sine * local_y, sine, cosine))
    return [square(item.center_x, side - item.center_y, item.cosine, -item.sine)
            for item in items], side


def fifty_three(tangent_b: Fraction = Fraction(6, 25), tangent_c: Fraction = Fraction(2, 7)) -> Packing:
    side = (13 + root_seven) / 2
    cosine_b = quadratic((1 - tangent_b * tangent_b) / (1 + tangent_b * tangent_b))
    sine_b = quadratic(2 * tangent_b / (1 + tangent_b * tangent_b))
    cosine_c = quadratic((1 - tangent_c * tangent_c) / (1 + tangent_c * tangent_c))
    sine_c = quadratic(2 * tangent_c / (1 + tangent_c * tangent_c))

    def rotated(point: Point, frame: tuple[Quadratic, Quadratic]) -> tuple[Quadratic, Quadratic]:
        horizontal, vertical = point
        cos, sin = frame
        return cos * horizontal + sin * vertical, -sin * horizontal + cos * vertical

    def added(left: Point, right: Point) -> tuple[Quadratic, Quadratic]:
        return quadratic(left[0]) + right[0], quadratic(left[1]) + right[1]

    def subtracted(left: Point, right: Point) -> tuple[Quadratic, Quadratic]:
        return quadratic(left[0]) - right[0], quadratic(left[1]) - right[1]

    frame_a, frame_b, frame_c = (cosine, sine), (cosine_b, sine_b), (cosine_c, sine_c)
    frame_b_inverse = (cosine_b, -sine_b)
    r1 = (side - 7) * sine
    v2 = cosine - sine
    anchor = added((1, 5), rotated((2 - r1, -v2), frame_a))
    r3 = (anchor[1] - sine_b - 3) / cosine_b
    v5 = rotated(subtracted((3, 3), added(anchor, rotated((1, -r3), frame_b))), frame_b_inverse)[1]
    v6 = cosine_b - sine_b
    u7 = (added(anchor, rotated((2, 2 - r3 + v5 - v6), frame_b))[1] - (side - 4)) / sine_b
    angle_difference_cos = cosine_b * cosine + sine_b * sine
    r8 = rotated(subtracted(added((5, 1), rotated((0, 1), frame_a)),
                            added(anchor, rotated((3, -r3 + v5 - v6), frame_b))), frame_b_inverse)[0] / angle_difference_cos
    u9 = r8 - rotated(subtracted(added((5, 1), rotated((0, 2), frame_a)),
                                 added(anchor, rotated((3 + u7, -r3 + v5 - v6), frame_b))), frame_b_inverse)[0] / angle_difference_cos
    rA = (side - 7) * sine_c
    uB = -added((side - 1, side - 6), rotated((rA, -2), frame_c))[1] / sine_c
    items = [square(column + half, row + half) for row in range(5) for column in range(5 - row)]
    items += [square(side - column - half, side - row - half)
              for row in range(6) for column in range(6 - row)]
    items += [square(side - half, half)]
    items += [square(half, side - row - half) for row in range(2)]

    def add_at(origin: Point, frame: tuple[Quadratic, Quadratic], local: Point) -> None:
        center = added(origin, rotated((local[0] + half, local[1] + half), frame))
        items.append(square(*center, frame[0], -frame[1]))

    for column in range(2):
        for row in range(2):
            add_at((1, 5), frame_a, (column - r1, row - column * v2))
    for column in range(2):
        for row in range(2):
            add_at(anchor, frame_b, (column, -r3 + row + column * v5))
    add_at(anchor, frame_b, (2, -r3 + v5 - v6))
    add_at(anchor, frame_b, (2 + u7, 1 - r3 + v5 - v6))
    add_at((5, 1), frame_a, (-r8, 0))
    add_at((5, 1), frame_a, (-r8 + u9, 1))
    add_at((side - 1, side - 6), frame_c, (rA - 1, -1))
    add_at((side - 1, side - 6), frame_c, (rA - 1 - uB, -2))
    return [square(item.center_x, side - item.center_y, item.cosine, -item.sine)
            for item in items], side


def ratio(value: Fraction) -> dict[str, str]:
    return {'numerator': str(value.numerator), 'denominator': str(value.denominator)}


def exact(value: Scalar) -> dict[str, object]:
    value = quadratic(value)
    if value.radical == 0:
        return ratio(value.rational)
    return {'rational': ratio(value.rational), 'radical': ratio(value.radical), 'radicand': 7}


def configuration(identifier: str, recipe: Callable[[], Packing], source: str, decimal: str) -> dict[str, object]:
    items, side = recipe()
    return {
        'schemaVersion': 1, 'id': identifier, 'n': len(items),
        'containerSide': {**exact(side), 'decimal': decimal},
        'coordinateSystem': 'physical-cartesian-bottom-left', 'squareSide': ratio(Fraction(1)),
        'squares': [
            {'id': index, 'center': {'x': exact(item.center_x), 'y': exact(item.center_y)},
             'orientation': {'tangentHalfAngle': exact(item.sine / (1 + item.cosine)),
                             'cosine': exact(item.cosine), 'sine': exact(item.sine),
                             'angleRadiansApprox': math.atan2(float(item.sine), float(item.cosine))}}
            for index, item in enumerate(items)
        ],
        'certificate': {'method': 'exact-quadratic-separating-axis',
                        'minimumContainmentMargin': ratio(Fraction(0)),
                        'minimumSeparationMargin': ratio(Fraction(0)),
                        'orientationReconstruction': (
                            'Alternate exact reconstruction of Ellsworth’s pattern in Q(sqrt(7)); auxiliary half-angle tangents 6/25 and 2/7 replace the source’s algebraic angles without increasing the container side.'
                            if identifier == 'square-53-ellsworth-reconstructed' else
                            'Exact coordinates and unit frames in Q(sqrt(7)), reconstructed from the source construction.')},
        'provenance': {'source': source, 'sourceOptimizedContainerSide': decimal, 'importedAt': '2026-09-05'}
    }


def configurations() -> list[dict[str, object]]:
    recipes: dict[str, tuple[str, Callable[[], Packing], str, str]] = {
        '18': ('square-18-hamalainen', eighteen_hamalainen, 'square-18.svg', '4.822875655532295'),
        '18b': ('square-18-gustafsson', eighteen_gustafsson, 'square-18b.svg', '4.822875655532295'),
        '18c': ('square-18-cantrell', eighteen_cantrell, 'square-18c.svg', '4.822875655532295'),
        '18d': ('square-18-gensane-ryckelynck', eighteen_gensane_ryckelynck, 'square-18d.svg', '4.822875655532295'),
        '86': ('square-86-friedman', eighty_six, 'square-86.svg', '9.822875655532295'),
        '53': ('square-53-ellsworth-reconstructed', fifty_three, 'square-53.svg', '7.822875655532295'),
    }
    return [configuration(identifier, recipe, 'https://kingbird.myphotos.cc/packing/' + filename, decimal)
            for identifier, recipe, filename, decimal in recipes.values()]


if __name__ == '__main__':
    print(json.dumps(configurations(), indent=2))
