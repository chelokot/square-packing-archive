import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class Quadratic:
    rational: Fraction = Fraction(0)
    radical: Fraction = Fraction(0)

    def __add__(self, other: "Quadratic") -> "Quadratic":
        return Quadratic(self.rational + other.rational, self.radical + other.radical)

    def __sub__(self, other: "Quadratic") -> "Quadratic":
        return Quadratic(self.rational - other.rational, self.radical - other.radical)

    def half_sqrt_two(self) -> "Quadratic":
        return Quadratic(self.radical, self.rational / 2)

    def encode(self) -> dict:
        def ratio(value: Fraction) -> dict[str, str]:
            return {"numerator": str(value.numerator), "denominator": str(value.denominator)}

        if not self.radical:
            return ratio(self.rational)
        return {"rational": ratio(self.rational), "sqrtTwo": ratio(self.radical)}


Square = tuple[Quadratic, Quadratic, bool]
Packing = tuple[Quadratic, list[Square]]


def exact(rational: int | Fraction = 0, radical: int | Fraction = 0) -> Quadratic:
    return Quadratic(Fraction(rational), Fraction(radical))


def staircase(width: int) -> list[Square]:
    return [(exact(Fraction(2 * column + 1, 2)), exact(Fraction(2 * row + 1, 2)), False)
            for row in range(width) for column in range(width - row)]


def shifted(squares: list[Square], offset_x: Quadratic, offset_y: Quadratic) -> list[Square]:
    return [(center_x + offset_x, center_y + offset_y, rotated)
            for center_x, center_y, rotated in squares]


def reflected(squares: list[Square], side: Quadratic, horizontal: bool = False,
              vertical: bool = False) -> list[Square]:
    return [(side - center_x if horizontal else center_x,
             side - center_y if vertical else center_y, rotated)
            for center_x, center_y, rotated in squares]


def rotated_block(width: int, height: int, origin_x: Quadratic, origin_y: Quadratic,
                  local_x: Quadratic, local_y: Quadratic) -> list[Square]:
    squares = []
    for row in range(height):
        for column in range(width):
            center_x = exact(Fraction(2 * column + 1, 2)) + local_x
            center_y = exact(Fraction(2 * row + 1, 2)) + local_y
            squares.append((origin_x + (center_x - center_y).half_sqrt_two(),
                            origin_y + (center_x + center_y).half_sqrt_two(), True))
    return squares


def symmetric_corners(steps: int, block_width: int) -> Packing:
    side = exact(steps + 1, Fraction(block_width, 2))
    corner = staircase(steps)
    squares = [square for horizontal in [False, True] for vertical in [False, True]
               for square in reflected(corner, side, horizontal, vertical)]
    squares += rotated_block(block_width, block_width,
                             exact(Fraction(steps + 1, 2)), exact(Fraction(steps + 1, 2)),
                             exact(), exact(Fraction(-block_width, 2)))
    return side, squares


def asymmetric_corners(steps: int, block_width: int) -> Packing:
    side = exact(Fraction(2 * steps + 3, 2), Fraction(block_width, 2))
    corner = staircase(steps)
    top = corner + reflected(shifted(corner, exact(1), exact()), side, horizontal=True)
    top += [(side - exact(Fraction(1, 2)), exact(Fraction(2 * row + 1, 2)), False)
            for row in range(steps)]
    squares = top + reflected(top, side, vertical=True)
    squares.append((side - exact(Fraction(1, 2)), exact(side.rational / 2, side.radical / 2), False))
    squares += rotated_block(block_width, block_width,
                             exact((side.rational - 1) / 2, side.radical / 2),
                             exact(side.rational / 2, side.radical / 2),
                             exact(Fraction(-block_width, 2)), exact(Fraction(-block_width, 2)))
    return side, squares


def stenlund_66() -> Packing:
    side = exact(3, 4)
    squares = staircase(5) + reflected(staircase(6), side, True, True)
    squares += reflected(staircase(2), side, vertical=True)
    squares += reflected(staircase(2), side, horizontal=True)
    squares += rotated_block(3, 8, exact(Fraction(5, 4), 2), exact(Fraction(5, 4), 2),
                             exact(Fraction(-3, 2)), exact(-4))
    return side, squares


def friedman_82() -> Packing:
    inner_side, inner_squares = symmetric_corners(4, 5)
    side = inner_side + exact(1)
    squares = shifted(inner_squares, exact(), exact(1))
    squares += [(exact(Fraction(2 * column + 1, 2)), exact(Fraction(1, 2)), False)
                for column in range(4)]
    squares += [(side - exact(Fraction(1, 2)), side - exact(Fraction(2 * row + 1, 2)), False)
                for row in range(4)]
    squares += [(side - exact(Fraction(2 * column + 1, 2)), exact(Fraction(1, 2)), False)
                for column in range(5)]
    squares += [(side - exact(Fraction(1, 2)), exact(Fraction(2 * row + 1, 2)), False)
                for row in range(1, 5)]
    return side, squares


def configuration(count: int, side: Quadratic, svg_squares: list[Square],
                  source_name: str, decimal: str) -> dict:
    axis = {"tangentHalfAngle": exact().encode(), "cosine": exact(1).encode(),
            "sine": exact().encode(), "angleRadiansApprox": 0}
    rotated = {"tangentHalfAngle": exact(-1, 1).encode(),
               "cosine": exact(0, Fraction(1, 2)).encode(),
               "sine": exact(0, Fraction(1, 2)).encode(), "angleRadiansApprox": 0.7853981633974483}
    assert len(svg_squares) == count, (count, len(svg_squares))
    return {
        "schemaVersion": 1, "id": f"square-{count}-tracker", "n": count,
        "containerSide": {**side.encode(), "decimal": decimal},
        "coordinateSystem": "physical-cartesian-bottom-left", "squareSide": exact(1).encode(),
        "squares": [{"id": index, "center": {"x": center_x.encode(), "y": (side - center_y).encode()},
                     "orientation": rotated if diagonal else axis}
                    for index, (center_x, center_y, diagonal) in enumerate(svg_squares)],
        "certificate": {"method": "exact-quadratic-separating-axis",
                        "minimumContainmentMargin": exact().encode(),
                        "minimumSeparationMargin": exact().encode(),
                        "orientationReconstruction": "Exact Q(√2) coordinates; axis-aligned or 45° squares"},
        "provenance": {"source": f"https://kingbird.myphotos.cc/packing/{source_name}.svg",
                       "sourceOptimizedContainerSide": decimal, "importedAt": "2026-09-05"},
    }


def configurations() -> list[dict]:
    records = [
        (26, asymmetric_corners(2, 3), "square-26b", "5.62132034355964257320253308632"),
        (40, symmetric_corners(3, 4), "square-40", "6.82842712474619009760337744842"),
        (65, symmetric_corners(4, 5), "square-65", "8.53553390593273762200422181052425"),
        (66, stenlund_66(), "square-66", "8.65685424949238019520675489684"),
        (82, friedman_82(), "square-82", "9.53553390593273762200422181052425"),
        (85, asymmetric_corners(4, 6), "square-85b", "9.74264068711928514640506617263"),
        (89, symmetric_corners(4, 7), "square-89", "9.94974746830583267080591053473394"),
    ]
    return [configuration(count, side, squares, source_name, decimal)
            for count, (side, squares), source_name, decimal in records]


def main() -> None:
    destination = Path(__file__).resolve().parents[1] / "archive" / "configurations"
    for record in configurations():
        (destination / f"{record['id']}.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
