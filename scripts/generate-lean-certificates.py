from __future__ import annotations

import argparse
import json
import re
from fractions import Fraction
from pathlib import Path
from typing import Any


def pascal_case(identifier: str) -> str:
    return "".join(part.capitalize() for part in identifier.split("-"))


def rational(value: dict[str, str]) -> str:
    numerator = value["numerator"]
    denominator = value["denominator"]
    if denominator == "1":
        return f"({numerator} : ℚ)"
    return f"(({numerator} : ℚ) / {denominator})"


def theorem_suffix(decimal: str) -> str:
    return re.sub(r"[^0-9]+", "_", decimal).strip("_")


def fraction(value: dict[str, str]) -> Fraction:
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def square_values(square: dict[str, Any]) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    return (
        fraction(square["center"]["x"]),
        fraction(square["center"]["y"]),
        fraction(square["orientation"]["cosine"]),
        fraction(square["orientation"]["sine"]),
    )


def dot(left_x: Fraction, left_y: Fraction, right_x: Fraction, right_y: Fraction) -> Fraction:
    return left_x * right_x + left_y * right_y


def radius(square: tuple[Fraction, Fraction, Fraction, Fraction], axis: tuple[Fraction, Fraction]) -> Fraction:
    _, _, cosine, sine = square
    axis_x, axis_y = axis
    return (
        abs(dot(axis_x, axis_y, cosine, sine))
        + abs(dot(axis_x, axis_y, -sine, cosine))
    ) / 2


def best_axis(
    left: tuple[Fraction, Fraction, Fraction, Fraction],
    right: tuple[Fraction, Fraction, Fraction, Fraction],
) -> int:
    left_x, left_y, left_cosine, left_sine = left
    right_x, right_y, right_cosine, right_sine = right
    axes = (
        (left_cosine, left_sine),
        (-left_sine, left_cosine),
        (right_cosine, right_sine),
        (-right_sine, right_cosine),
    )
    margins = tuple(
        abs(dot(right_x - left_x, right_y - left_y, axis_x, axis_y))
        - radius(left, (axis_x, axis_y))
        - radius(right, (axis_x, axis_y))
        for axis_x, axis_y in axes
    )
    witness = max(range(4), key=margins.__getitem__)
    if margins[witness] < 0:
        raise ValueError(f"pair has no separating axis: {float(margins[witness]):.12g}")
    return witness


def render(configuration: dict[str, Any]) -> str:
    namespace = pascal_case(configuration["id"])
    square_count = configuration["n"]
    side = rational(configuration["containerSide"])
    theorem_name = f"s{square_count}_le_{theorem_suffix(configuration['containerSide']['decimal'])}"
    squares = []
    for square in configuration["squares"]:
        squares.append(
            "    { centerX := "
            + rational(square["center"]["x"])
            + ", centerY := "
            + rational(square["center"]["y"])
            + ", cosine := "
            + rational(square["orientation"]["cosine"])
            + ", sine := "
            + rational(square["orientation"]["sine"])
            + " }"
        )
    square_vector = ",\n".join(squares)
    values = tuple(square_values(square) for square in configuration["squares"])
    witness_names = (
        ".leftHorizontal",
        ".leftVertical",
        ".rightHorizontal",
        ".rightVertical",
    )
    witness_rows = []
    for left_index, left in enumerate(values):
        row = [
            witness_names[best_axis(left, right)] if left_index < right_index else witness_names[0]
            for right_index, right in enumerate(values)
        ]
        witness_rows.append("    #v[" + ", ".join(row) + "]")
    witness_matrix = ",\n".join(witness_rows)
    return f"""import SquarePackingArchive.RationalCertificate

namespace SquarePackingArchive.Records.{namespace}

def certificate : RationalCertificate {square_count} where
  side := {side}
  squares := #v[
{square_vector}
  ]
  separatingAxes := #v[
{witness_matrix}
  ]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate_valid : certificate.Valid := by decide +kernel

theorem {theorem_name} : HasPacking {square_count} ({side} : ℝ) :=
  by simpa [certificate] using RationalCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.{namespace}
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("configuration", type=Path)
    parser.add_argument("destination", type=Path)
    arguments = parser.parse_args()
    configuration = json.loads(arguments.configuration.read_text())
    arguments.destination.parent.mkdir(parents=True, exist_ok=True)
    arguments.destination.write_text(render(configuration))
    print(arguments.destination)


if __name__ == "__main__":
    main()
