from __future__ import annotations

import argparse
import itertools
import runpy
from dataclasses import dataclass
from pathlib import Path


geometry = runpy.run_path(str(Path(__file__).with_name("generate-triangle-cover.py")))
Quadratic = geometry["Quadratic"]
Halfplane = geometry["Halfplane"]
Region = geometry["Region"]
Renderer = geometry["Renderer"]
rational = geometry["rational"]
halfplane = geometry["halfplane"]
ZERO = geometry["ZERO"]
ONE = geometry["ONE"]
SIDE = rational(4)


def point(horizontal: str, vertical: str):
    return Quadratic(geometry["Fraction"](horizontal)), Quadratic(geometry["Fraction"](vertical))


INITIAL_FIXED = tuple(point(*coordinates) for coordinates in (
    ("1", "1.74"), ("3", "1.74"), ("1", "2.26"), ("3", "2.26"),
    ("2", "1.74"), ("2", "2.26"), ("1.6", "1"), ("2.4", "1"),
    ("1.6", "3"), ("2.4", "3"),
))
FINAL_FIXED = tuple(point(*coordinates) for coordinates in (
    ("1.6", "1"), ("2.26", "1"), ("3", "1.6"), ("1", "1.74"),
    ("1.78", "1.74"), ("2.26", "2"), ("1.6", "3"), ("2.26", "3"),
    ("3", "2.4"), ("1", "2.26"), ("1.78", "2.26"),
))


def points_for(final: bool, choices: int):
    corners = []
    for corner in range(4):
        horizontal, vertical = point(".914", "1") if choices & (1 << corner) else point("1", ".914")
        corners.append((SIDE - horizontal if corner % 2 else horizontal,
                        SIDE - vertical if corner >= 2 else vertical))
    return (FINAL_FIXED if final else INITIAL_FIXED) + tuple(corners)


def squared_distance(first, second):
    horizontal, vertical = first[0] - second[0], first[1] - second[1]
    return horizontal * horizontal + vertical * vertical


def transform(point, side: int):
    horizontal, vertical = point
    return ((horizontal, vertical), (vertical, horizontal),
            (horizontal, SIDE - vertical), (vertical, SIDE - horizontal))[side]


def pullback(plane, side: int):
    horizontal, vertical, constant = plane.horizontal, plane.vertical, plane.constant
    return (plane, Halfplane(vertical, horizontal, constant),
            Halfplane(horizontal, -vertical, constant + SIDE * vertical),
            Halfplane(-vertical, horizontal, constant + SIDE * vertical))[side]


@dataclass(frozen=True)
class GeometricRegion:
    kind: str
    vertices: tuple[int, ...]
    planes: tuple
    side: int = 0


def regions_for(final: bool, choices: int):
    points = points_for(final, choices)
    regions = []
    for indices in itertools.combinations(range(len(points)), 3):
        if any((squared_distance(points[first], points[second]) - ONE).sign() > 0
               for first, second in itertools.combinations(indices, 2)):
            continue
        orientation = halfplane(points[indices[0]], points[indices[1]]).at(points[indices[2]]).sign()
        if not orientation:
            continue
        if orientation < 0:
            indices = indices[0], indices[2], indices[1]
        planes = tuple(halfplane(points[indices[edge]], points[indices[(edge + 1) % 3]]) for edge in range(3))
        regions.append(GeometricRegion("triangle", indices, planes))
    for side in range(4):
        transformed = tuple(transform(value, side) for value in points)
        for first, second in itertools.permutations(range(len(points)), 2):
            first_x, first_y = transformed[first]
            second_x, second_y = transformed[second]
            width = second_x - first_x
            if width.sign() <= 0 or any((height - rational(1, 2)).sign() < 0 or (height - ONE).sign() > 0
                                        for height in (first_y, second_y)):
                continue
            kind = "short_pair"
            if (width - rational(4, 5)).sign() > 0:
                if first_y != ONE or second_y != ONE or (width - rational(413, 500)).sign() > 0:
                    continue
                kind = "wide_pair"
            planes = (Halfplane(ONE, ZERO, -first_x), Halfplane(-ONE, ZERO, second_x),
                      halfplane(transformed[second], transformed[first]))
            regions.append(GeometricRegion(kind, (first, second), tuple(pullback(plane, side) for plane in planes), side))
    for corner in range(4):
        for index, (horizontal, vertical) in enumerate(points):
            distance_x = SIDE - horizontal if corner % 2 else horizontal
            distance_y = SIDE - vertical if corner >= 2 else vertical
            if (distance_x - ONE).sign() > 0 or (distance_y - ONE).sign() > 0:
                continue
            planes = (Halfplane(ONE if corner % 2 else -ONE, ZERO, -horizontal if corner % 2 else horizontal),
                      Halfplane(ZERO, ONE if corner >= 2 else -ONE, -vertical if corner >= 2 else vertical))
            regions.append(GeometricRegion("corner", (index,), planes, corner))
    if not final:
        for left in (1, 2):
            planes = (Halfplane(ONE, ZERO, rational(-left)), Halfplane(-ONE, ZERO, rational(left + 1)),
                      Halfplane(ZERO, ONE, rational(-87, 50)), Halfplane(ZERO, -ONE, rational(113, 50)))
            regions.append(GeometricRegion("hole", (left - 1,), planes))
    return tuple(regions)


NAMESPACE = "SquarePackingArchive.BentzThirteen.Nonadjacent"


def render_data():
    lines = ["import SquarePackingArchive.BentzBoundaryPairs",
             "import SquarePackingArchive.StromquistRingBoundary", "", f"namespace {NAMESPACE}", "",
             "def choicePattern (choice : Fin 16) (corner : Fin 4) : Bool :=",
             "  decide (choice.val / 2 ^ corner.val % 2 = 1)", "",
             "lemma choicePattern_exhaustive (choices : Fin 4 → Bool) :",
             "    ∃ choice, choices = choicePattern choice := by",
             "  exact (by decide : ∀ choices : Fin 4 → Bool, ∃ choice, choices = choicePattern choice) choices", "",
             "noncomputable def cornerAlternative (choices : Fin 4 → Bool) (corner : Fin 4) : Point :=",
             "  let base : Point := if choices corner then ⟨457 / 500, 1⟩ else ⟨1, 457 / 500⟩",
             "  match corner.val with", "  | 0 => base", "  | 1 => base.reflectX 4",
             "  | 2 => base.reflectY 4", "  | _ => (base.reflectX 4).reflectY 4", ""]
    for name, fixed in (("initialPoints", INITIAL_FIXED), ("finalPoints", FINAL_FIXED)):
        lines += [f"noncomputable def {name} (choices : Fin 4 → Bool) (index : Fin {len(fixed) + 4}) : Point :=",
                  "  match index.val with"]
        for index, (horizontal, vertical) in enumerate(fixed):
            lines.append(f"  | {index} => ⟨{horizontal.lean()}, {vertical.lean()}⟩")
        for corner in range(4):
            pattern = "_" if corner == 3 else str(len(fixed) + corner)
            lines.append(f"  | {pattern} => cornerAlternative choices {corner}")
        lines.append("")
    lines += ["def Hole (point : Point) : Prop :=",
              "  1 ≤ point.x ∧ point.x ≤ 3 ∧ 87 / 50 ≤ point.y ∧ point.y ≤ 113 / 50", "",
              f"end {NAMESPACE}"]
    return "BentzThirteenNonadjacentData", "\n".join(lines) + "\n"


def render_case(final: bool, choices: int):
    family = "final" if final else "initial"
    prefix = f"{family}{choices:02}"
    module = f"BentzThirteenNonadjacent/{family.capitalize()}{choices:02}"
    points = points_for(final, choices)
    regions = regions_for(final, choices)
    renderer = Renderer(prefix, normalize_boundaries=False)
    renderer.append(0, "import SquarePackingArchive.BentzThirteenNonadjacentData")
    renderer.append(0, "")
    renderer.append(0, f"namespace {NAMESPACE}")
    renderer.append(0, "")
    renderer.append(0, f"noncomputable def {prefix}Points : Fin {len(points)} → Point := {family}Points (choicePattern {choices})")
    renderer.append(0, "")
    renderer.append(0, f"def {prefix}Region (index : Fin {len(regions)}) (center : Point) : Prop :=")
    renderer.append(1, "match index.val with")
    for index, region in enumerate(regions):
        pattern = "_" if index == len(regions) - 1 else str(index)
        predicate = " ∧ ".join(f"0 ≤ {plane.lean().replace('square.center', 'center')}" for plane in region.planes)
        renderer.append(1, f"| {pattern} => {predicate}")
    renderer.append(0, "")
    hit = f"(∃ index, square.Contains ({prefix}Points index))"
    target = hit if final else f"{hit} ∨ Hole square.center"
    definitions = f"{prefix}Points, {family}Points, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap"

    def transfer(depth, index, hypothesis, operations=()):
        renderer.append(depth, f"refine ⟨{index}, ?_⟩")
        square = "square"
        point_expression = f"({prefix}Points {index})"
        for operation in operations:
            renderer.append(depth, f"apply ({square}.{operation}_contains_iff {'4 ' if operation != 'swap' else ''}{point_expression}).1")
            point_expression = f"({point_expression}.{operation}{' 4' if operation != 'swap' else ''})"
            square = f"({square}.{operation}{' 4' if operation != 'swap' else ''})"
        renderer.append(depth, f"norm_num [{definitions}] at {hypothesis} ⊢")
        renderer.append(depth, f"exact {hypothesis}")

    def transformed_square(operations):
        square, fits = "square", "fits"
        for operation in operations:
            fits = f"(({square}.{operation}_fits_iff 4).2 {fits})"
            square = f"({square}.{operation}{' 4' if operation != 'swap' else ''})"
        return square, fits

    renderer.append(0, "set_option maxHeartbeats 4000000 in")
    renderer.append(0, f"lemma {prefix}_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)")
    renderer.append(2, f"(index : Fin {len(regions)}) (membership : {prefix}Region index square.center) :")
    renderer.append(2, f"{target} := by")
    renderer.append(1, "fin_cases index")
    for region in regions:
        names = tuple(f"bound_{index}" for index in range(len(region.planes)))
        renderer.append(1, f"· rcases membership with ⟨{', '.join(names)}⟩")
        depth = 2
        if not final:
            renderer.append(depth, "apply Or.inr" if region.kind == "hole" else "apply Or.inl")
        if region.kind == "hole":
            renderer.append(depth, "refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [" + ", ".join(names) + "]")
        elif region.kind == "triangle":
            first, second, third = region.vertices
            renderer.append(depth, "rcases square.contains_triangleVertex_of_cross_nonnegative")
            renderer.append(depth + 1, f"({prefix}Points {first}) ({prefix}Points {second}) ({prefix}Points {third})")
            renderer.append(depth + 1, f"(by norm_num [{definitions}, Point.orientedArea])")
            for name in names:
                renderer.append(depth + 1, f"(by norm_num [{definitions}, Point.orientedArea]; linarith only [{name}])")
            renderer.append(depth + 1, f"(by norm_num [{definitions}]) (by norm_num [{definitions}])")
            renderer.append(depth + 1, f"(by norm_num [{definitions}]) with first_inside | second_inside | third_inside")
            for index, hypothesis in zip(region.vertices, ("first_inside", "second_inside", "third_inside")):
                renderer.append(depth, f"· exact ⟨{index}, {hypothesis}⟩")
        elif region.kind == "corner":
            operations = (() if region.side % 2 == 0 else ("reflectX",)) + (() if region.side < 2 else ("reflectY",))
            square, fits = transformed_square(operations)
            horizontal, vertical = points[region.vertices[0]]
            horizontal = SIDE - horizontal if region.side % 2 else horizontal
            vertical = SIDE - vertical if region.side >= 2 else vertical
            renderer.append(depth, f"have inside := {square}.contains_cornerPoint (targetX := {horizontal.lean()})")
            renderer.append(depth + 1, f"(targetY := {vertical.lean()}) {fits} (by norm_num) (by norm_num)")
            for name in names:
                simplify = "dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; " if operations else ""
                renderer.append(depth + 1, f"(by {simplify}linarith only [{name}])")
            transfer(depth, region.vertices[0], "inside", operations)
        else:
            operations = ((), ("swap",), ("reflectY",), ("reflectX", "swap"))[region.side]
            square, fits = transformed_square(operations)
            first, second = (transform(points[index], region.side) for index in region.vertices)
            width = second[0] - first[0]
            if region.kind == "wide_pair":
                renderer.append(depth, f"have pair := {square}.contains_bottomSharpPair (left := {first[0].lean()})")
                renderer.append(depth + 1, f"(gap := {width.lean()}) (targetHeight := 1) {fits} (by norm_num) (by norm_num)")
                renderer.append(depth + 1, "(by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])")
            else:
                renderer.append(depth, f"have pair := Stromquist.TenPoints.contains_short_pair (square := {square})")
                renderer.append(depth + 1, f"(left := {first[0].lean()}) (width := {width.lean()})")
                renderer.append(depth + 1, f"(firstHeight := {first[1].lean()}) (secondHeight := {second[1].lean()})")
                renderer.append(depth + 1, f"{fits} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
            for name in names:
                simplify = "dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; " if operations else ""
                renderer.append(depth + 1, f"(by {simplify}linarith only [{name}])")
            renderer.append(depth, "rcases pair with first_inside | second_inside")
            for index, hypothesis in zip(region.vertices, ("first_inside", "second_inside")):
                renderer.append(depth, "·")
                transfer(depth + 1, index, hypothesis, operations)
    renderer.append(0, "")
    renderer.append(0, "set_option maxHeartbeats 4000000 in")
    renderer.append(0, f"theorem {prefix}_cover : ∀ square : PlacedSquare, square.Fits 4 → {target} := by")
    renderer.append(1, "intro square fits")
    constraints = renderer.container_bounds(SIDE)
    renderer.cover(1, ((ZERO, ZERO), (SIDE, ZERO), (SIDE, SIDE), (ZERO, SIDE)),
                   tuple(Region(index, (), region.planes, "boundary") for index, region in enumerate(regions)), constraints)
    renderer.append(0, "")
    renderer.append(0, f"end {NAMESPACE}")
    return module, "\n".join(renderer.lines) + "\n"


def render_aggregate():
    lines = [f"import SquarePackingArchive.BentzThirteenNonadjacent.{family}{choices:02}"
             for family in ("Initial", "Final") for choices in range(16)]
    lines += ["", f"namespace {NAMESPACE}", "",
              "theorem initial_cover (choices : Fin 4 → Bool) (square : PlacedSquare) (fits : square.Fits 4) :",
              "    (∃ index, square.Contains (initialPoints choices index)) ∨ Hole square.center := by",
              "  obtain ⟨choice, rfl⟩ := choicePattern_exhaustive choices",
              "  fin_cases choice"]
    lines += [f"  · exact initial{choice:02}_cover square fits" for choice in range(16)]
    lines += ["", "theorem final_unavoidable (choices : Fin 4 → Bool) : Unavoidable (finalPoints choices) 4 := by",
              "  obtain ⟨choice, rfl⟩ := choicePattern_exhaustive choices",
              "  fin_cases choice"]
    lines += [f"  · exact final{choice:02}_cover" for choice in range(16)]
    lines += ["", f"end {NAMESPACE}"]
    return "BentzThirteenNonadjacent", "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--final", action="store_true")
    parser.add_argument("--choices", type=int, choices=range(16), default=0)
    parser.add_argument("--data", action="store_true")
    parser.add_argument("--aggregate", action="store_true")
    parser.add_argument("--patch", action="store_true")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    if arguments.patch or arguments.check:
        module, result = (render_data() if arguments.data else render_aggregate() if arguments.aggregate
                          else render_case(arguments.final, arguments.choices))
        if arguments.check:
            target = Path(__file__).resolve().parents[1] / "formal" / "SquarePackingArchive" / f"{module}.lean"
            if target.read_text() != result:
                parser.exit(1, f"{target.name} differs from the generated proof\n")
            print(f"{module} is reproducible")
            return
        print(f"*** Begin Patch\n*** Add File: formal/SquarePackingArchive/{module}.lean")
        print("\n".join("+" + line for line in result.splitlines()))
        print("*** End Patch")
        return
    regions = regions_for(arguments.final, arguments.choices)
    renderer = Renderer("nonadjacent", normalize_boundaries=False)
    constraints = renderer.container_bounds(SIDE)
    renderer.cover(1, ((ZERO, ZERO), (SIDE, ZERO), (SIDE, SIDE), (ZERO, SIDE)),
                   tuple(Region(index, (), region.planes, "boundary") for index, region in enumerate(regions)), constraints)
    print(f"{len(regions)} regions, {renderer.branch_count} branches, {len(renderer.lines)} lines")


if __name__ == "__main__":
    main()
