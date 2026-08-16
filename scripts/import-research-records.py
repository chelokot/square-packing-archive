from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Frame:
    cosine: Fraction
    sine: Fraction

    @property
    def perpendicular(self) -> tuple[Fraction, Fraction]:
        return -self.sine, self.cosine


@dataclass(frozen=True)
class Square:
    center_x: Fraction
    center_y: Fraction
    tangent_half_angle: Fraction

    @property
    def frame(self) -> Frame:
        tangent_squared = self.tangent_half_angle * self.tangent_half_angle
        denominator = 1 + tangent_squared
        return Frame(
            cosine=(1 - tangent_squared) / denominator,
            sine=2 * self.tangent_half_angle / denominator,
        )


def ratio(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def dot(
    left_x: Fraction,
    left_y: Fraction,
    right_x: Fraction,
    right_y: Fraction,
) -> Fraction:
    return left_x * right_x + left_y * right_y


def projection_radius(square: Square, axis_x: Fraction, axis_y: Fraction) -> Fraction:
    frame = square.frame
    perpendicular_x, perpendicular_y = frame.perpendicular
    return (
        abs(dot(axis_x, axis_y, frame.cosine, frame.sine))
        + abs(dot(axis_x, axis_y, perpendicular_x, perpendicular_y))
    ) / 2


def containment_margin(container_side: Fraction, square: Square) -> Fraction:
    frame = square.frame
    extent = (abs(frame.cosine) + abs(frame.sine)) / 2
    return min(
        square.center_x - extent,
        square.center_y - extent,
        container_side - square.center_x - extent,
        container_side - square.center_y - extent,
    )


def separation_margin(left: Square, right: Square) -> Fraction:
    left_frame = left.frame
    right_frame = right.frame
    axes = (
        (left_frame.cosine, left_frame.sine),
        left_frame.perpendicular,
        (right_frame.cosine, right_frame.sine),
        right_frame.perpendicular,
    )
    delta_x = right.center_x - left.center_x
    delta_y = right.center_y - left.center_y
    return max(
        abs(dot(delta_x, delta_y, axis_x, axis_y))
        - projection_radius(left, axis_x, axis_y)
        - projection_radius(right, axis_x, axis_y)
        for axis_x, axis_y in axes
    )


def parse_decimal(value: object) -> Fraction:
    return Fraction(str(value))


def import_record(source_path: Path, destination_path: Path) -> tuple[Fraction, Fraction]:
    source: dict[str, Any] = json.loads(source_path.read_text())
    container_side = parse_decimal(source["claimed_container_side"])
    normalized_centers = source["centers"]
    angles = source["angles"]
    if len(normalized_centers) != source["count"] or len(angles) != source["count"]:
        raise ValueError(f"{source_path}: count does not match coordinate arrays")

    squares = tuple(
        Square(
            center_x=(parse_decimal(center[0]) + 1) * container_side / 2,
            center_y=(parse_decimal(center[1]) + 1) * container_side / 2,
            tangent_half_angle=Fraction(math.tan(float(angle) / 2)).limit_denominator(10**16),
        )
        for center, angle in zip(normalized_centers, angles, strict=True)
    )
    minimum_containment = min(containment_margin(container_side, square) for square in squares)
    minimum_separation = min(
        separation_margin(squares[left_index], squares[right_index])
        for left_index in range(len(squares))
        for right_index in range(left_index + 1, len(squares))
    )
    if minimum_containment < 0 or minimum_separation < 0:
        raise ValueError(
            f"{source_path}: rational reconstruction failed: "
            f"containment={float(minimum_containment):.12g}, "
            f"separation={float(minimum_separation):.12g}"
        )

    record = {
        "schemaVersion": 1,
        "id": source_path.stem,
        "n": source["count"],
        "containerSide": {
            **ratio(container_side),
            "decimal": str(source["claimed_container_side"]),
        },
        "coordinateSystem": "physical-cartesian-bottom-left",
        "squareSide": ratio(Fraction(1)),
        "squares": [
            {
                "id": index,
                "center": {"x": ratio(square.center_x), "y": ratio(square.center_y)},
                "orientation": {
                    "tangentHalfAngle": ratio(square.tangent_half_angle),
                    "cosine": ratio(square.frame.cosine),
                    "sine": ratio(square.frame.sine),
                    "angleRadiansApprox": angles[index],
                },
            }
            for index, square in enumerate(squares)
        ],
        "certificate": {
            "method": "exact-rational-separating-axis",
            "minimumContainmentMargin": ratio(minimum_containment),
            "minimumSeparationMargin": ratio(minimum_separation),
            "orientationReconstruction": "rational tangent-half-angle with denominator at most 10^16",
        },
        "provenance": {
            "source": "square-packing-research",
            "sourceOptimizedContainerSide": str(source["optimized_container_side"]),
            "importedAt": "2026-08-16",
        },
    }
    destination_path.parent.mkdir(parents=True, exist_ok=True)
    destination_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    return minimum_containment, minimum_separation


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    arguments = parser.parse_args()
    containment, separation = import_record(arguments.source, arguments.destination)
    print(
        json.dumps(
            {
                "destination": str(arguments.destination),
                "minimumContainmentMargin": float(containment),
                "minimumSeparationMargin": float(separation),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
