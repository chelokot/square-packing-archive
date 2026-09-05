from __future__ import annotations

import argparse
import itertools
import runpy
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


CORE = runpy.run_path(str(Path(__file__).with_name("generate-triangle-cover.py")))
Quadratic = CORE["Quadratic"]
Halfplane = CORE["Halfplane"]
rational = CORE["rational"]
halfplane = CORE["halfplane"]


def point(horizontal: str, vertical: str):
    return Quadratic(Fraction(horizontal)), Quadratic(Fraction(vertical))


ANCHOR_A = tuple(point(*coordinates) for coordinates in (
    ("1", ".914"), ("1.13", "1"), ("1.4", "1"), ("1.5", "1"), ("1.74", "1"), ("1.87", ".76")))
ANCHOR_B = tuple(point(*coordinates) for coordinates in (
    (".914", "1"), ("1", "1.13"), ("1", "1.82"), (".76", "1.96")))


@dataclass(frozen=True)
class Configuration:
    name: str
    points: tuple
    critical: tuple = ()


def configuration(name, extra, critical=()):
    points = tuple(dict.fromkeys(ANCHOR_A + ANCHOR_B + tuple(point(*entry) for entry in extra)))
    return Configuration(name, points, critical)


CONFIGURATIONS = (
    configuration("AdjacentInitial", (("2.5", "1"), ("3", "1")) + tuple(
        (horizontal, vertical) for vertical in ("1.82", "2.36", "3.09")
        for horizontal in ("1", "2", "3")),
        (("1", "2", "2.36", "3.09"), ("2", "3", "2.36", "3.09"),
         ("2", "3", "1.82", "2.36"), ("1", "2", "1.82", "2.36"))),
    configuration("AdjacentR2Left", (
        ("2.5", "2.36"), ("2.5", "3.09"), ("2", "2.72"),
        ("2.5", "1"), ("3.1", "1"), ("2.5", "1.6"), ("1.6", "1.95"),
        ("3.1", "2"), ("1", "2.72"), ("1", "3"), ("1.8", "3"), ("3.1", "3"))),
    configuration("AdjacentR2Right", (
        ("2.5", "2.36"), ("2.5", "3.09"), ("3", "2.64"),
        ("2.5", "1"), ("3", "1"), ("2", "1.82"), ("3", "1.82"),
        ("1", "2.36"), ("1.5", "2.36"), ("1", "3"), ("1.8", "3"), ("3", "3"))),
    configuration("AdjacentR3", (
        ("2.5", "1.82"), ("2.5", "2.36"), ("3", "2.10"),
        ("2.3", "1"), ("3.05", "1"), ("1.8", "1.8"), ("3", "1.86"),
        ("1", "2.14"), ("2", "2.14"), (".95", "3"), ("1.5", "3"), ("2.3", "3"), ("3.1", "3"))),
    configuration("AdjacentR4", (
        ("1.5", "1.82"), ("1.5", "2.36"), ("1", "2.10"), ("2", "2.10"),
        ("2.5", "1"), ("3.1", "1"), ("2.4", "1.6"), ("3.1", "2"),
        ("2.4", "2.5"), (".9", "3"), ("1.7", "3"), ("2.5", "3"), ("3.1", "3"))),
) + tuple(configuration(f"AdjacentR1{index:02}", (
        ("1.5", "2.36"), ("1.5", "3.09"), ("1", str(Fraction(59,25)+Fraction(2,25)*(index+1))),
        ("2.5", "1"), ("3", "1"), ("2", "1.82"), ("3", "1.82"),
        ("2.3", "2.5"), ("3", "2.5"), ("1", "3"), ("2.3", "3"), ("3", "3")) +
        ((("1", "2.84"),) if index == 7 else ()))
    for index in range(8))


def signed_area(first, second, third):
    return halfplane(first, second).at(third)


def short_triangles(points):
    for indices in itertools.combinations(range(len(points)), 3):
        vertices = tuple(points[index] for index in indices)
        if any(((first[0] - second[0]) * (first[0] - second[0]) +
                (first[1] - second[1]) * (first[1] - second[1]) - rational(1)).sign() > 0
               for first, second in itertools.combinations(vertices, 2)):
            continue
        orientation = signed_area(*vertices).sign()
        if orientation:
            yield indices if orientation > 0 else (indices[0], indices[2], indices[1])


def transformed_point(coordinates, transform):
    horizontal, vertical = coordinates
    basic = ((horizontal, vertical), (vertical, horizontal),
             (horizontal, rational(4) - vertical), (vertical, rational(4) - horizontal))[transform % 4]
    return (rational(4)-basic[0],basic[1]) if transform >= 4 else basic


def original_plane(plane, transform):
    if transform >= 4:
        plane = Halfplane(-plane.horizontal, plane.vertical, plane.constant + rational(4)*plane.horizontal)
        transform -= 4
    horizontal, vertical, constant = plane.horizontal, plane.vertical, plane.constant
    return (plane, Halfplane(vertical, horizontal, constant),
            Halfplane(horizontal, -vertical, constant + rational(4) * vertical),
            Halfplane(-vertical, horizontal, constant + rational(4) * vertical))[transform]


def boundary_pairs(points):
    for transform in range(8):
        for first_index, second_index in itertools.permutations(range(len(points)), 2):
            first, second = (transformed_point(points[index], transform) for index in (first_index, second_index))
            width = second[0] - first[0]
            if width.sign() <= 0:
                continue
            first_height, second_height = first[1], second[1]
            if any((height - rational(1)).sign() > 0 or (height - rational(1, 2)).sign() < 0
                   for height in (first_height, second_height)):
                continue
            drop = first_height - second_height
            if (width * width + drop * drop - rational(1)).sign() > 0:
                continue
            if (width - rational(4, 5)).sign() <= 0:
                kind = "short"
            elif drop.sign() == 0 and (first_height - rational(457, 500)).sign() <= 0:
                kind = "equal"
            elif drop.sign() >= 0 and (width - rational(24, 25)).sign() <= 0 and (drop-rational(6,25)).sign() >= 0:
                kind = "extended"
            elif drop.sign() >= 0 and (width - rational(89, 100)).sign() <= 0 and (drop-rational(79,1000)).sign() >= 0:
                kind = "bentz_first"
            elif drop.sign() >= 0 and (width - rational(9, 10)).sign() <= 0 and (drop-rational(1,10)).sign() >= 0:
                kind = "bentz_second"
            elif drop.sign() == 0 and (width-rational(207,250)).sign() <= 0:
                kind = "equal_wide"
            elif drop.sign() >= 0 and (width-rational(43,50)).sign() <= 0 and (drop-rational(1,20)).sign() >= 0:
                kind = "r3"
            else:
                continue
            if transform >= 4 and kind in ("short", "equal", "equal_wide"):
                continue
            local_planes = (
                Halfplane(rational(1), rational(0), -first[0]),
                Halfplane(rational(-1), rational(0), second[0]),
                Halfplane(-drop, -width, width * first_height + drop * first[0]),
            )
            yield kind, transform, first_index, second_index, tuple(original_plane(plane, transform) for plane in local_planes)


def summary(config):
    triangles = tuple(short_triangles(config.points))
    pairs = tuple(boundary_pairs(config.points))
    print(config.name, len(config.points), "points", len(triangles), "triangles", len(pairs), "boundary pairs")


def rectangle(horizontal_lower, horizontal_upper, vertical_lower, vertical_upper):
    return (Halfplane(rational(1), rational(0), -horizontal_lower),
            Halfplane(rational(-1), rational(0), horizontal_upper),
            Halfplane(rational(0), rational(1), -vertical_lower),
            Halfplane(rational(0), rational(-1), vertical_upper))


def regions(config):
    result = []
    for axis, sign, constant in ((0,-1,rational(49,100)), (1,-1,rational(49,100)),
                                  (0,1,rational(-351,100)), (1,1,rational(-351,100))):
        result.append(("outside", (axis, sign),
            (Halfplane(rational(sign if axis == 0 else 0), rational(sign if axis == 1 else 0), constant),)))
    for indices in short_triangles(config.points):
        vertices = tuple(config.points[index] for index in indices)
        result.append(("triangle", indices, tuple(halfplane(first, second) for first, second in
                      zip(vertices, vertices[1:] + vertices[:1]))))
    for index, (horizontal, vertical) in enumerate(config.points):
        radii = ((rational(7,20),rational(7,20)),)
        for horizontal_radius, vertical_radius in radii:
            result.append(("near", (index, horizontal_radius, vertical_radius),
                rectangle(horizontal-horizontal_radius, horizontal+horizontal_radius,
                          vertical-vertical_radius, vertical+vertical_radius)))
        for reflect_x, reflect_y in itertools.product((False, True), repeat=2):
            corner_x = rational(4)-horizontal if reflect_x else horizontal
            corner_y = rational(4)-vertical if reflect_y else vertical
            if (corner_x-rational(1)).sign() <= 0 and (corner_y-rational(1)).sign() <= 0:
                result.append(("corner", (index, reflect_x, reflect_y), (
                    Halfplane(rational(1) if reflect_x else rational(-1), rational(0), -horizontal if reflect_x else horizontal),
                    Halfplane(rational(0), rational(1) if reflect_y else rational(-1), -vertical if reflect_y else vertical))))
    for kind, transform, first, second, planes in boundary_pairs(config.points):
        result.append((kind, (transform, first, second), planes))
    for index, bounds in enumerate(config.critical):
        result.append(("critical", (index,), rectangle(*(Quadratic(Fraction(value)) for value in bounds))))
    return tuple(result)


def cover(config):
    prefix = config.name[0].lower() + config.name[1:]
    return CORE["render_region_cover"](
        prefix,
        (f"SquarePackingArchive.Bentz{config.name}Geometry",),
        "SquarePackingArchive.BentzThirteen",
        tuple(region[2] for region in selected_regions(config)), rational(4),
        f"theorem {prefix}_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → {prefix}Outcome square := by")


def lean_point(coordinates):
    return "⟨" + ", ".join(value.lean() for value in coordinates) + "⟩"


@lru_cache(maxsize=None)
def selected_regions(config):
    candidates = regions(config)
    renderer = CORE["Renderer"]("planning", normalize_boundaries=False)
    constraints = renderer.container_bounds(rational(4))
    domain = tuple(point(*coordinates) for coordinates in (("0","0"),("4","0"),("4","4"),("0","4")))
    renderer.cover(1, domain, tuple(CORE["Region"](index, (), planes, "boundary")
        for index, (_, _, planes) in enumerate(candidates)), constraints)
    indices = {index for _, index in renderer.used_regions}
    return tuple(candidate for index,candidate in enumerate(candidates) if index in indices)


def geometry(config, data_only=False):
    prefix = config.name[0].lower() + config.name[1:]
    points_name = prefix + "Points"
    region_data = () if data_only else selected_regions(config)
    lines = ["import SquarePackingArchive.BentzThirteenCoverGeometry", "",
             "namespace SquarePackingArchive.BentzThirteen", "", "set_option maxRecDepth 10000", "",
             f"noncomputable def {points_name} (index : Fin {len(config.points)}) : Point :=",
             "  match index.val with"]
    for index, coordinates in enumerate(config.points):
        lines.append(f"  | {index if index+1 < len(config.points) else '_'} => {lean_point(coordinates)}")
    lines.append("")
    if config.critical:
        lines.extend([f"def {prefix}CriticalRegion (index : Fin {len(config.critical)}) (center : Point) : Prop :=", "  match index.val with"])
        for index, bounds in enumerate(config.critical):
            lower_x, upper_x, lower_y, upper_y = (Quadratic(Fraction(value)).lean() for value in bounds)
            lines.append(f"  | {index if index+1 < len(config.critical) else '_'} => {lower_x} ≤ center.x ∧ center.x ≤ {upper_x} ∧ {lower_y} ≤ center.y ∧ center.y ≤ {upper_y}")
        lines.append("")
    lines.extend([f"def {prefix}Outcome (square : PlacedSquare) : Prop :=",
                  f"  (∃ index, square.Contains ({points_name} index))" +
                  (f" ∨ ∃ region, {prefix}CriticalRegion region square.center" if config.critical else ""), "",
                  f"def {prefix}Region (index : Fin {len(region_data)}) (center : Point) : Prop :=", "  match index.val with"])
    for index, (_, _, planes) in enumerate(region_data):
        predicate = " ∧ ".join(f"0 ≤ {plane.lean().replace('square.center', 'center')}" for plane in planes)
        lines.append(f"  | {index if index+1 < len(region_data) else '_'} => {predicate}")
    lines.extend(["", "set_option maxHeartbeats 4000000 in",
                  f"theorem {prefix}_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)",
                  f"    (index : Fin {len(region_data)}) (membership : {prefix}Region index square.center) :",
                  f"    {prefix}Outcome square := by", "  fin_cases index"])
    definitions = f"{points_name}, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap"
    basic_transforms = (
        ("square", "fits", ()),
        ("square.swap", "((square.swap_fits_iff 4).2 fits)", ("swap",)),
        ("(square.reflectY 4)", "((square.reflectY_fits_iff 4).2 fits)", ("reflectY",)),
        ("(square.reflectX 4).swap", "(((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))", ("reflectX", "swap")),
    )
    transforms = basic_transforms + tuple((f"({expression}.reflectX 4)",
        f"(({expression}.reflectX_fits_iff 4).2 {fits_expression})", operations+("reflectX",))
        for expression, fits_expression, operations in basic_transforms)

    def lift_membership(index, operations, hypothesis, indentation):
        square_expression = "square"
        point_expression = f"({points_name} {index})"
        for operation in operations:
            argument = "4 " if operation != "swap" else ""
            lines.append(indentation + f"apply ({square_expression}.{operation}_contains_iff {argument}{point_expression}).1")
            square_expression = f"({square_expression}.{operation}" + (" 4)" if operation != "swap" else ")")
            point_expression = f"({point_expression}.{operation}" + (" 4)" if operation != "swap" else ")")
        lines.append(indentation + f"convert {hypothesis} using 1; norm_num [{definitions}]")

    def transformed_center(operations):
        horizontal, vertical = "square.center.x", "square.center.y"
        for operation in operations:
            if operation == "swap":
                horizontal, vertical = vertical, horizontal
            elif operation == "reflectX":
                horizontal = f"(4 - {horizontal})"
            else:
                vertical = f"(4 - {vertical})"
        return horizontal, vertical

    def center_proof(statement, operations):
        return f"(by change {statement}; linarith)" if operations else "(by linarith)"

    for region_index, (kind, payload, planes) in enumerate(region_data):
        predicate = " ∧ ".join(f"0 ≤ {plane.lean()}" for plane in planes)
        lines.append(f"  · change {predicate} at membership")
        lines.append("    norm_num at membership")
        if len(planes) > 1:
            lines.append("    obtain ⟨" + ", ".join(f"plane_{index}" for index in range(len(planes))) + "⟩ := membership")
        if kind == "outside":
            lines.extend(["    exfalso", "    have bounds := center_inside_half_margin fits",
                          "    linarith [bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2]"])
            continue
        if kind == "critical":
            lines.extend([f"    exact Or.inr ⟨{payload[0]}, by norm_num [{prefix}CriticalRegion]; exact ⟨plane_0, plane_1, plane_2, plane_3⟩⟩"])
            continue
        if config.critical:
            lines.append("    apply Or.inl")
        if kind == "triangle":
            first, second, third = payload
            lines.append(f"    apply square.contains_indexed_triangleVertex {points_name} ![{first}, {second}, {third}]")
            lines.append(f"    all_goals norm_num [{points_name}, Point.orientedArea, Matrix.cons_val_two]")
            lines.append("    all_goals linarith")
        elif kind == "near":
            index, horizontal_radius, vertical_radius = payload
            lines.append(f"    refine ⟨{index}, contains_of_center_box (horizontalRadius := {horizontal_radius.lean()}) (verticalRadius := {vertical_radius.lean()}) (by norm_num) ?_ ?_ ?_ ?_⟩")
            lines.append(f"    all_goals (norm_num [{points_name}]; linarith)")
        elif kind == "corner":
            index, reflect_x, reflect_y = payload
            operations = tuple(operation for operation, enabled in (("reflectX", reflect_x), ("reflectY", reflect_y)) if enabled)
            expression, fits_expression = "square", "fits"
            for operation in operations:
                fits_expression = f"(({expression}.{operation}_fits_iff 4).2 {fits_expression})"
                expression = f"({expression}.{operation} 4)"
            target = config.points[index]
            local_target = ((rational(4)-target[0]) if reflect_x else target[0], (rational(4)-target[1]) if reflect_y else target[1])
            lines.append(f"    have contained := {expression}.contains_cornerPoint (targetX := {local_target[0].lean()}) (targetY := {local_target[1].lean()}) {fits_expression} (by norm_num) (by norm_num)")
            center_x, center_y = transformed_center(operations)
            lines.append("      " + " ".join(center_proof(statement,operations) for statement in
                (f"{center_x} ≤ {local_target[0].lean()}",f"{center_y} ≤ {local_target[1].lean()}")))
            lines.append(f"    refine ⟨{index}, ?_⟩")
            lift_membership(index, operations, "contained", "    ")
        else:
            transform, first_index, second_index = payload
            first, second = (transformed_point(config.points[index], transform) for index in (first_index, second_index))
            width = second[0]-first[0]
            expression, fits_expression, operations = transforms[transform]
            if kind in ("equal", "equal_wide"):
                lemma = "contains_bottomLowPair" if kind == "equal" else "contains_bottomSharpPair"
                root_proof = "(by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])"
                sideconditions = f"{root_proof} (by norm_num) (by norm_num)" if kind == "equal" else f"(by norm_num) (by norm_num) {root_proof}"
                lines.append(f"    have pair := {expression}.{lemma} (left := {first[0].lean()}) (gap := {width.lean()}) (targetHeight := {first[1].lean()}) {fits_expression} {sideconditions}")
            elif kind == "short":
                lines.append(f"    have pair := Stromquist.TenPoints.contains_short_pair (square := {expression}) (left := {first[0].lean()}) (width := {width.lean()}) (firstHeight := {first[1].lean()}) (secondHeight := {second[1].lean()}) {fits_expression}")
                lines.append("      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
            else:
                bound = {"bentz_first": "first", "bentz_second": "second", "extended": "third", "r3": "r3"}[kind]
                lines.append(f"    have pair := Bentz.contains_descending_pair (square := {expression}) (left := {first[0].lean()}) (width := {width.lean()}) (firstHeight := {first[1].lean()}) (secondHeight := {second[1].lean()}) {fits_expression}")
                lines.append(f"      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_{bound} (by norm_num) (by norm_num))")
            center_x, center_y = transformed_center(operations)
            below = (f"{center_y} ≤ {first[1].lean()}" if kind in ("equal", "equal_wide") else
                f"{width.lean()} * {center_y} ≤ {width.lean()} * {first[1].lean()} + ({second[1].lean()} - {first[1].lean()}) * ({center_x} - {first[0].lean()})")
            lines.append("      " + " ".join(center_proof(statement,operations) for statement in
                (f"{first[0].lean()} ≤ {center_x}",f"{center_x} ≤ {first[0].lean()} + {width.lean()}",below)))
            lines.append("    rcases pair with first_mem | second_mem")
            for index, hypothesis in ((first_index,"first_mem"), (second_index,"second_mem")):
                lines.append(f"    · refine ⟨{index}, ?_⟩")
                lift_membership(index, operations, hypothesis, "      ")
    lines.extend(["", "end SquarePackingArchive.BentzThirteen", ""])
    return "\n".join(lines)


def render_configuration(config, data_only=False, include_cover=True):
    generated = geometry(config, data_only)
    prefix = config.name[0].lower() + config.name[1:]
    data, proof = generated.split(f"def {prefix}Region", 1)
    outputs = {
        f"Bentz{config.name}Data.lean": data + "end SquarePackingArchive.BentzThirteen\n",
        f"Bentz{config.name}Geometry.lean": f"import SquarePackingArchive.Bentz{config.name}Data\n\nnamespace SquarePackingArchive.BentzThirteen\n\nset_option maxRecDepth 10000\n\ndef {prefix}Region" + proof,
    }
    if data_only:
        return {name: output for name, output in outputs.items() if name.endswith("Data.lean")}
    if include_cover:
        outputs[f"Bentz{config.name}Cover.lean"] = cover(config)
    return outputs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--configuration", choices=[entry.name for entry in CONFIGURATIONS])
    parser.add_argument("--cover", action="store_true")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--patch", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--data-only", action="store_true")
    arguments = parser.parse_args()
    for config in CONFIGURATIONS:
        if arguments.configuration is None or config.name == arguments.configuration:
            if arguments.patch or arguments.check:
                outputs = render_configuration(config, arguments.data_only, arguments.cover)
                root = Path(__file__).resolve().parent.parent / "formal" / "SquarePackingArchive"
                if arguments.check:
                    for name, output in outputs.items():
                        if (root / name).read_text() != output:
                            raise SystemExit(f"Generated proof differs: {name}")
                    print(f"{config.name}: {len(outputs)} generated files match")
                    continue
                print("*** Begin Patch")
                for name, output in outputs.items():
                    print(f"*** Add File: {root / name}")
                    print("\n".join("+" + line for line in output.splitlines()))
                print("*** End Patch")
                continue
            summary(config)
            if arguments.cover:
                output = cover(config)
                print(len(output), "cover bytes")


if __name__ == "__main__":
    main()
