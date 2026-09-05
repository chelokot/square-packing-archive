from __future__ import annotations

import argparse
import itertools
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class Quadratic:
    rational: Fraction = Fraction(0)
    radical: Fraction = Fraction(0)

    def __add__(self, other: Quadratic) -> Quadratic:
        return Quadratic(self.rational + other.rational, self.radical + other.radical)

    def __neg__(self) -> Quadratic:
        return Quadratic(-self.rational, -self.radical)

    def __sub__(self, other: Quadratic) -> Quadratic:
        return self + -other

    def __mul__(self, other: Quadratic) -> Quadratic:
        return Quadratic(
            self.rational * other.rational + 2 * self.radical * other.radical,
            self.rational * other.radical + self.radical * other.rational,
        )

    def __truediv__(self, other: Quadratic) -> Quadratic:
        norm = other.rational**2 - 2 * other.radical**2
        conjugate = Quadratic(other.rational / norm, -other.radical / norm)
        return self * conjugate

    def sign(self) -> int:
        rational_sign = (self.rational > 0) - (self.rational < 0)
        radical_sign = (self.radical > 0) - (self.radical < 0)
        if rational_sign == 0:
            return radical_sign
        if radical_sign == 0 or rational_sign == radical_sign:
            return rational_sign
        difference = self.rational**2 - 2 * self.radical**2
        return rational_sign * ((difference > 0) - (difference < 0))

    def approximate(self) -> float:
        return float(self.rational) + math.sqrt(2) * float(self.radical)

    def lean(self) -> str:
        def rational(value: Fraction) -> str:
            if value.denominator == 1:
                return f"({value.numerator} : ℝ)"
            return f"({value.numerator} / {value.denominator} : ℝ)"

        if not self.radical:
            return rational(self.rational)
        return f"({rational(self.rational)} + {rational(self.radical)} * Real.sqrt 2)"


def rational(numerator: int, denominator: int = 1) -> Quadratic:
    return Quadratic(Fraction(numerator, denominator))


ZERO = rational(0)
ONE = rational(1)
Point = tuple[Quadratic, Quadratic]
Polygon = tuple[Point, ...]


@dataclass(frozen=True)
class Halfplane:
    horizontal: Quadratic
    vertical: Quadratic
    constant: Quadratic

    def opposite(self) -> Halfplane:
        return Halfplane(-self.horizontal, -self.vertical, -self.constant)

    def at(self, point: Point) -> Quadratic:
        return self.horizontal * point[0] + self.vertical * point[1] + self.constant

    def lean(self) -> str:
        terms = (
            f"{self.horizontal.lean()} * square.center.x",
            f"{self.vertical.lean()} * square.center.y",
            self.constant.lean(),
        )
        return "(" + " + ".join(terms) + ")"


def halfplane(first: Point, second: Point) -> Halfplane:
    horizontal = first[1] - second[1]
    vertical = second[0] - first[0]
    return Halfplane(horizontal, vertical, -(horizontal * first[0] + vertical * first[1]))


def clip(polygon: Polygon, boundary: Halfplane) -> Polygon:
    result: list[Point] = []
    for first, second in zip(polygon, polygon[1:] + polygon[:1]):
        first_value, second_value = boundary.at(first), boundary.at(second)
        if first_value.sign() >= 0:
            result.append(first)
        if first_value.sign() * second_value.sign() < 0:
            ratio = first_value / (first_value - second_value)
            result.append(tuple(first[axis] + ratio * (second[axis] - first[axis]) for axis in (0, 1)))
    return tuple(dict.fromkeys(result))


def area(polygon: Polygon) -> float:
    total = ZERO
    for first, second in zip(polygon, polygon[1:] + polygon[:1]):
        total += first[0] * second[1] - first[1] * second[0]
    return abs(total.approximate()) / 2


@dataclass(frozen=True)
class Constraint:
    boundary: Halfplane
    name: str
    strict: bool = False


def determinant(first: Halfplane, second: Halfplane) -> Quadratic:
    return first.horizontal * second.vertical - first.vertical * second.horizontal


def certificate(constraints: tuple[Constraint, ...]) -> tuple[tuple[Constraint, Quadratic], ...]:
    def valid(selected: tuple[Constraint, ...], weights: tuple[Quadratic, ...]) -> bool:
        if any(weight.sign() < 0 for weight in weights):
            return False
        total = sum((constraint.boundary.constant * weight for constraint, weight in zip(selected, weights)), ZERO)
        strict = any(constraint.strict and weight.sign() > 0 for constraint, weight in zip(selected, weights))
        return total.sign() < 0 or (total.sign() == 0 and strict)

    for selected in itertools.combinations(constraints, 2):
        first, second = (constraint.boundary for constraint in selected)
        if determinant(first, second).sign() != 0:
            continue
        weights = (second.horizontal, -first.horizontal)
        if not any(weight.sign() for weight in weights):
            weights = (second.vertical, -first.vertical)
        for oriented in (weights, tuple(-weight for weight in weights)):
            if valid(selected, oriented):
                return tuple((constraint, weight) for constraint, weight in zip(selected, oriented) if weight.sign())
    for selected in itertools.combinations(constraints, 3):
        first, second, third = (constraint.boundary for constraint in selected)
        weights = (determinant(second, third), determinant(third, first), determinant(first, second))
        for oriented in (weights, tuple(-weight for weight in weights)):
            if valid(selected, oriented):
                return tuple((constraint, weight) for constraint, weight in zip(selected, oriented) if weight.sign())
    raise ValueError("No exact separating certificate for an allegedly impossible branch")


@dataclass(frozen=True)
class Region:
    index: int
    vertices: tuple[int, ...]
    boundaries: tuple[Halfplane, ...]
    kind: str = "triangle"


class Renderer:
    def __init__(self, prefix: str, normalize_boundaries: bool = True) -> None:
        self.lines: list[str] = []
        self.branch_count = 0
        self.leaf_count = 0
        self.prefix = prefix
        self.normalize_boundaries = normalize_boundaries

    def append(self, depth: int, text: str) -> None:
        self.lines.append("  " * depth + text)

    def sign_proof(self, value: Quadratic, strict: bool) -> str:
        relation = "<" if strict else "≤"
        if not value.radical:
            tactic = "norm_num"
        elif value.rational >= 0 and value.radical >= 0:
            tactic = "positivity"
        else:
            tactic = "nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]"
        return f"(by {tactic} : 0 {relation} {value.lean()})"

    def quadratic_identity(self, depth: int, has_squared_radical: bool) -> None:
        if has_squared_radical:
            self.append(depth, "ring_nf")
            self.append(depth, "simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]")
        self.append(depth, "ring")

    def contradiction(self, depth: int, constraints: tuple[Constraint, ...]) -> None:
        selected = certificate(constraints)
        names = []
        terms = []
        total = ZERO
        for index, (constraint, weight) in enumerate(selected):
            name = f"weighted_{index}"
            names.append(name)
            operation = "mul_pos" if constraint.strict else "mul_nonneg"
            self.append(depth, f"have {name} := {operation} {self.sign_proof(weight, constraint.strict)} {constraint.name}")
            terms.append(f"{weight.lean()} * {constraint.boundary.lean()}")
            total += weight * constraint.boundary.constant
        self.append(depth, f"have identity : {' + '.join(terms)} = {total.lean()} := by")
        has_squared_radical = any(sum(
            weight.radical * getattr(constraint.boundary, component).radical
            for constraint, weight in selected
        ) for component in ("horizontal", "vertical", "constant"))
        self.quadratic_identity(depth + 1, has_squared_radical)
        if total.sign() < 0:
            self.append(depth, f"have constant_negative := {self.sign_proof(-total, True)}")
            names.append("constant_negative")
        self.append(depth, f"nlinarith only [{', '.join(names)}, identity]")

    def membership(self, depth: int, wanted: Halfplane, constraints: tuple[Constraint, ...]) -> None:
        for constraint in constraints:
            if constraint.boundary == wanted:
                suffix = ".le" if constraint.strict else ""
                self.append(depth, f"exact {constraint.name}{suffix}")
                return
        self.append(depth, "by_contra! failed")
        opposite = wanted.opposite()
        self.append(depth, f"have negative : 0 < {opposite.lean()} := by linarith only [failed]")
        self.contradiction(depth, constraints + (Constraint(opposite, "negative", True),))

    def cover(self, depth: int, polygon: Polygon, regions: tuple[Region, ...], constraints: tuple[Constraint, ...]) -> None:
        for region in regions:
            if all(boundary.at(point).sign() >= 0 for boundary in region.boundaries for point in polygon):
                self.leaf_count += 1
                if region.kind == "boundary":
                    self.append(depth, f"apply {self.prefix}_hit_boundary square fits {region.index}")
                    if self.normalize_boundaries:
                        self.append(depth, f"rw [{self.prefix}_boundary_{region.index}]")
                    else:
                        self.append(depth, "change " + " ∧ ".join(f"0 ≤ {plane.lean()}" for plane in region.boundaries))
                    self.append(depth, f"refine ⟨{', '.join('?_ ' for _ in region.boundaries)}⟩")
                elif region.kind == "hull":
                    self.append(depth, f"apply {self.prefix}_hit_in_hull square")
                else:
                    self.append(depth, f"apply {self.prefix}_hit_triangle square {region.index}")
                for edge_index, boundary in enumerate(region.boundaries):
                    if region.kind == "boundary":
                        self.append(depth, "·")
                    else:
                        first = region.vertices[edge_index]
                        second = region.vertices[(edge_index + 1) % len(region.vertices)]
                        if region.kind == "hull":
                            self.append(depth, "·")
                        else:
                            self.append(depth, f"· change 0 ≤ Point.orientedArea ({self.prefix}Points {first}) ({self.prefix}Points {second}) square.center")
                        self.append(depth + 1, f"rw [{self.prefix}_area_{first}_{second}]")
                    self.membership(depth + 1, boundary, constraints)
                return
        intersections = []
        for region in regions:
            intersection = polygon
            for boundary in region.boundaries:
                intersection = clip(intersection, boundary)
            if intersection:
                intersections.append((region, intersection))
        regions = tuple(region for region, _ in intersections)
        choices = []
        for boundary in dict.fromkeys(boundary for region in regions for boundary in region.boundaries):
            signs = tuple(boundary.at(point).sign() for point in polygon)
            if -1 in signs and 1 in signs:
                positive, negative = clip(polygon, boundary), clip(polygon, boundary.opposite())
                straddlers = front = back = 0
                for _, intersection in intersections:
                    region_signs = tuple(boundary.at(point).sign() for point in intersection)
                    front += 1 in region_signs
                    back += -1 in region_signs
                    straddlers += 1 in region_signs and -1 in region_signs
                score = (-3 * straddlers - abs(front - back), min(area(positive), area(negative)))
                choices.append((score, boundary, positive, negative))
        if not choices:
            raise ValueError("The supplied triangles do not cover their claimed domain")
        _, boundary, positive, negative = max(choices, key=lambda choice: choice[0])
        name = f"branch_{self.branch_count}"
        self.branch_count += 1
        self.append(depth, f"by_cases {name} : 0 ≤ {boundary.lean()}")
        self.append(depth, "·")
        self.cover(depth + 1, positive, regions, constraints + (Constraint(boundary, name),))
        self.append(depth, "·")
        opposite = boundary.opposite()
        negative_name = f"{name}_negative"
        self.append(depth + 1, f"have {negative_name} : 0 < {opposite.lean()} := by linarith only [{name}]")
        self.cover(depth + 1, negative, regions, constraints + (Constraint(opposite, negative_name, True),))

    def container_bounds(self, side: Quadratic, definitions: tuple[str, ...] = ()) -> tuple[Constraint, ...]:
        self.append(1, "have center_inside : square.Contains square.center := by")
        self.append(2, "refine ⟨0, 0, by norm_num, by norm_num, ?_⟩")
        self.append(2, "simp [PlacedSquare.point, Frame.place]")
        self.append(1, "have container_bounds := fits center_inside")
        planes = (Halfplane(ONE, ZERO, ZERO), Halfplane(-ONE, ZERO, side),
            Halfplane(ZERO, ONE, ZERO), Halfplane(ZERO, -ONE, side))
        constraints = []
        for index, plane in enumerate(planes):
            name = f"container_{index}"
            constraints.append(Constraint(plane, name))
            self.append(1, f"have {name} : 0 ≤ {plane.lean()} := by")
            if definitions:
                self.append(2, f"dsimp [{', '.join(definitions)}] at container_bounds")
            self.append(2, "linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]")
        return tuple(constraints)


def render_region_cover(
    prefix: str,
    imports: tuple[str, ...],
    namespace: str,
    regions: tuple[tuple[Halfplane, ...], ...],
    container_side: Quadratic,
    theorem_statement: str,
) -> str:
    renderer = Renderer(prefix, normalize_boundaries=False)
    for module in imports:
        renderer.append(0, f"import {module}")
    renderer.append(0, "")
    renderer.append(0, f"namespace {namespace}")
    renderer.append(0, "")
    renderer.append(0, "set_option maxHeartbeats 4000000 in")
    renderer.append(0, theorem_statement)
    renderer.append(1, "intro square fits")
    constraints = renderer.container_bounds(container_side)
    domain = ((ZERO, ZERO), (container_side, ZERO), (container_side, container_side), (ZERO, container_side))
    renderer.cover(1, domain, tuple(Region(index, (), planes, "boundary")
                                   for index, planes in enumerate(regions)), constraints)
    renderer.append(0, "")
    renderer.append(0, f"end {namespace}")
    return "\n".join(renderer.lines) + "\n"


def boundary_regions(points: tuple[Point, ...]) -> tuple[Region, ...]:
    def left(value: Quadratic) -> Halfplane:
        return Halfplane(-ONE, ZERO, value)

    def right(value: Quadratic) -> Halfplane:
        return Halfplane(ONE, ZERO, -value)

    def below(value: Quadratic) -> Halfplane:
        return Halfplane(ZERO, -ONE, value)

    def above(value: Quadratic) -> Halfplane:
        return Halfplane(ZERO, ONE, -value)

    boundaries = (
        (left(points[0][0]), below(points[0][1])),
        (right(points[7][0]), below(points[7][1])),
        (right(points[5][0]), above(points[5][1])),
        (left(points[3][0]), above(points[3][1])),
        (right(points[0][0]), left(points[1][0]), halfplane(points[1], points[0])),
        (right(points[1][0]), left(points[8][0]), halfplane(points[8], points[1])),
        (right(points[8][0]), left(points[7][0]), halfplane(points[7], points[8])),
        (above(points[0][1]), below(points[2][1]), halfplane(points[0], points[2])),
        (above(points[2][1]), below(points[3][1]), halfplane(points[2], points[3])),
        (right(points[3][0]), left(points[4][0]), halfplane(points[3], points[4])),
        (right(points[4][0]), left(points[5][0]), halfplane(points[4], points[5])),
        (above(points[7][1]), below(points[6][1]), halfplane(points[6], points[7])),
        (above(points[6][1]), below(points[5][1]), halfplane(points[5], points[6])),
    )
    return tuple(Region(index, (), region, "boundary") for index, region in enumerate(boundaries))


def render_cover(step: int, full: bool) -> tuple[str, str]:
    prefix = {2: "stepTwo", 3: "stepThree", 4: "stepFour"}[step]
    region_definition = {2: "StepTwoBoundaryRegion", 3: "StepThreeBoundaryRegion", 4: "StepFourBoundaryRegion"}[step]
    gap = Quadratic(Fraction(1, 2), Fraction(1, 4))
    side = rational(2) + rational(2) * gap
    points = (
        (ONE, ONE), (rational(6, 5), ONE), (rational(3, 4), side - rational(49, 25)),
        (ONE, ONE + rational(2) * gap), (ONE + gap, rational(103, 100) + rational(2) * gap),
        (ONE + rational(2) * gap, ONE + rational(2) * gap),
        (rational(103, 100) + rational(2) * gap, ONE + gap),
        (ONE + rational(2) * gap, ONE), (rational(2), ONE), (rational(7, 5), ONE + gap),
        (rational(3, 5) + rational(2) * gap, ONE + gap),
        (ONE + gap, rational(7, 5)), (ONE + gap, rational(3, 5) + rational(2) * gap),
    )
    if step == 2:
        points = ((ONE, rational(197, 250)),) + points[1:8] + ((ONE + gap, rational(97, 100)),) + points[9:]
    vertices = (
        (9, 3, 2), (5, 10, 6), (10, 7, 6), (3, 12, 4), (12, 3, 9),
        (12, 5, 4), (12, 10, 5), (10, 8, 7), (11, 8, 10), (11, 1, 8),
        (1, 11, 9), (1, 9, 2), (0, 1, 2), (12, 11, 10), (11, 12, 9),
    )
    if step == 4:
        points = points[:1] + ((rational(53, 25), rational(9, 10)),) + points[2:]
        vertices = (
            (9, 3, 2), (5, 10, 6), (10, 7, 6), (0, 9, 2), (3, 12, 4),
            (12, 3, 9), (12, 5, 4), (12, 10, 5), (10, 8, 7), (8, 1, 7),
            (0, 11, 9), (8, 11, 0), (11, 8, 10), (12, 11, 10), (11, 12, 9),
        )
    triangles = tuple(Region(index, triangle, tuple(
        halfplane(points[triangle[edge]], points[triangle[(edge + 1) % 3]]) for edge in range(3)
    )) for index, triangle in enumerate(vertices))
    hull = (7, 6, 5, 4, 3, 2, 0)
    hull_edges = tuple(zip(hull, hull[1:] + hull[:1]))
    hull_region = Region(0, hull, tuple(halfplane(points[first], points[second]) for first, second in hull_edges), "hull")
    boundaries = boundary_regions(points) if full else ()
    if step == 4:
        pentagon = (
            Halfplane(ONE, ZERO, -ONE),
            Halfplane(-ONE, ZERO, rational(53, 25)),
            Halfplane(ZERO, -ONE, ONE),
            Halfplane(rational(-5), rational(-6), rational(16)),
        )
        bottom_right = (
            Halfplane(ONE, ZERO, -rational(53, 25)),
            Halfplane(-ONE, ZERO, side - ONE),
            halfplane(points[7], points[1]),
        )
        boundary_planes = tuple(region.boundaries for region in boundaries)
        boundary_planes = boundary_planes[:4] + (pentagon, bottom_right) + boundary_planes[7:]
        boundaries = tuple(Region(index, (), planes, "boundary") for index, planes in enumerate(boundary_planes))
    regions = ((hull_region,) if step == 3 and full else triangles) + boundaries
    all_edges = dict.fromkeys((region.vertices[edge], region.vertices[(edge + 1) % len(region.vertices)])
        for region in regions if region.kind != "boundary" for edge in range(len(region.vertices)))
    if not full:
        all_edges.update(dict.fromkeys(hull_edges))
    renderer = Renderer(prefix)
    if full and step == 3:
        module = "StromquistTenCover"
        renderer.append(0, "import SquarePackingArchive.StromquistTenTriangleCover")
        renderer.append(0, "import SquarePackingArchive.StromquistTenBoundary")
    elif step == 2:
        module = "StromquistStepTwoCover"
        renderer.append(0, "import SquarePackingArchive.StromquistStepTwo")
    elif step == 4:
        module = "StromquistStepFourCover"
        renderer.append(0, "import SquarePackingArchive.StromquistStepFour")
    else:
        module = "StromquistTenTriangleCover"
        renderer.append(0, "import SquarePackingArchive.StromquistTenReplacementPoints")
    renderer.append(0, "")
    renderer.append(0, "namespace SquarePackingArchive.Stromquist.TenPoints")
    renderer.append(0, "")
    for first, second in all_edges:
        renderer.append(0, f"private lemma {prefix}_area_{first}_{second} (square : PlacedSquare) :")
        renderer.append(2, f"Point.orientedArea ({prefix}Points {first}) ({prefix}Points {second}) square.center =")
        renderer.append(3, f"{halfplane(points[first], points[second]).lean()} := by")
        extra_definition = f"{prefix}Points, " if step != 3 else ""
        renderer.append(1, f"norm_num [{extra_definition}stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,")
        renderer.append(2, "side, gap, Records.Square5.diagonal]")
        has_squared_radical = points[first][0].radical * points[second][1].radical != points[first][1].radical * points[second][0].radical
        renderer.quadratic_identity(1, has_squared_radical)
        renderer.append(0, "")
    for boundary in boundaries:
        predicates = " ∧ ".join(f"0 ≤ {plane.lean()}" for plane in boundary.boundaries)
        renderer.append(0, f"private lemma {prefix}_boundary_{boundary.index} (square : PlacedSquare) :")
        renderer.append(2, f"{region_definition} {boundary.index} square.center ↔ {predicates} := by")
        definitions = {2: "StepTwoBoundaryRegion, ", 3: "", 4: "StepFourBoundaryRegion, stepFourOldRegion, "}[step]
        names = [f"part_{index}" for index in range(len(boundary.boundaries))]
        renderer.append(1, f"constructor <;> rintro ⟨{', '.join(names)}⟩ <;> repeat' apply And.intro")
        if any(coefficient.radical for plane in boundary.boundaries
               for coefficient in (plane.horizontal, plane.vertical, plane.constant)):
            renderer.append(1, f"all_goals dsimp -failIfUnchanged [{definitions}StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at {' '.join(names)} ⊢")
        renderer.append(1, f"all_goals nlinarith only [{', '.join(names)}, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]")
        renderer.append(0, "")
    renderer.append(0, "set_option maxHeartbeats 4000000 in")
    constraints = []
    if full:
        if step == 4:
            renderer.append(0, "theorem stepFour_cover : ∀ square : PlacedSquare, square.Fits side → StepFourHit square := by")
        else:
            renderer.append(0, f"theorem {prefix}_unavoidable : Unavoidable {prefix}Points side := by")
        renderer.append(1, "intro square fits")
        constraints = list(renderer.container_bounds(side, ("side", "gap", "Records.Square5.diagonal")))
        domain = ((ZERO, ZERO), (side, ZERO), (side, side), (ZERO, side))
    else:
        renderer.append(0, f"theorem {prefix}_hit_in_hull (square : PlacedSquare)")
        for index, (first, second) in enumerate(hull_edges):
            name = f"hull_{index}"
            constraints.append(Constraint(halfplane(points[first], points[second]), name))
            renderer.append(2, f"({name} : 0 ≤ Point.orientedArea ({prefix}Points {first}) ({prefix}Points {second}) square.center)")
        renderer.append(2, f": ∃ index, square.Contains ({prefix}Points index) := by")
        for index, (first, second) in enumerate(hull_edges):
            renderer.append(1, f"rw [{prefix}_area_{first}_{second}] at hull_{index}")
        domain = tuple(points[index] for index in hull)
    renderer.cover(1, domain, regions, tuple(constraints))
    renderer.append(0, "")
    renderer.append(0, "end SquarePackingArchive.Stromquist.TenPoints")
    return module, "\n".join(renderer.lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--patch", action="store_true")
    parser.add_argument("--step", type=int, choices=(2, 3, 4), default=3)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--stats", action="store_true")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    if arguments.step != 3 and not arguments.full:
        parser.error("Steps 2 and 4 have nonconvex interior boundaries; use --full")
    module, result = render_cover(arguments.step, arguments.full)
    if arguments.check:
        target = Path(__file__).resolve().parents[1] / "formal" / "SquarePackingArchive" / f"{module}.lean"
        if target.read_text() != result:
            parser.exit(1, f"{target.name} differs from the generated proof\n")
        print(f"{target.name} is reproducible")
    elif arguments.stats:
        print(f"{module}: {len(result.splitlines())} lines, {result.count('by_cases branch_')} branches, {len(result)} characters")
    elif arguments.patch:
        target = f"formal/SquarePackingArchive/{module}.lean"
        print(f"*** Begin Patch\n*** Add File: {target}")
        print("\n".join("+" + line for line in result.splitlines()))
        print("*** End Patch")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
