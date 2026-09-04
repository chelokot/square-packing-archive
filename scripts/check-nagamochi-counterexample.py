import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from typing import Literal
from xml.etree import ElementTree


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


def resource_chord(axis: Axis, height: Fraction) -> tuple[Fraction, Fraction] | None:
    intersection_coordinates: list[Fraction] = []
    for start, end in polygon_edges(SQUARE):
        if start[axis] == end[axis]:
            if start[axis] == height:
                intersection_coordinates.extend((start[1 - axis], end[1 - axis]))
        elif (start[axis] - height) * (end[axis] - height) <= 0:
            ratio = (height - start[axis]) / (end[axis] - start[axis])
            intersection_coordinates.append(interpolate(start, end, ratio)[1 - axis])
    if not intersection_coordinates:
        return None
    lower = max(min(intersection_coordinates), RESOURCE_OFFSET)
    upper = min(max(intersection_coordinates), CONTAINER_SIDE - RESOURCE_OFFSET)
    return (lower, upper) if lower < upper else None


def resource_chord_length(axis: Axis, height: Fraction) -> Fraction:
    chord = resource_chord(axis, height)
    return Fraction(0) if chord is None else chord[1] - chord[0]


def display(name: str, value: Fraction) -> None:
    with localcontext() as context:
        context.prec = 26
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
    print(f"{name}: {value} = {decimal}")


def figure_description() -> str:
    fingerprint = sha256(Path(__file__).read_bytes()).hexdigest()
    return f"Generated from exact rational counterexample data; source SHA-256: {fingerprint}"


def figure_path(suffix: str) -> Path:
    return Path(__file__).resolve().parents[1] / "docs" / "assets" / f"nagamochi-counterexample.{suffix}"


def check_figure() -> None:
    description = figure_description()
    document = ElementTree.parse(figure_path("svg"))
    assert description in tuple(element.text for element in document.iter()), (
        "SVG is stale; run python3 scripts/check-nagamochi-counterexample.py --figure"
    )
    assert description.encode() in figure_path("png").read_bytes(), (
        "PNG is stale; run python3 scripts/check-nagamochi-counterexample.py --figure"
    )


def render_figure(
    inner_polygon: Polygon,
    corner_points: tuple[Point, ...],
    edge_points: tuple[Point, ...],
    score: Fraction,
) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plot
    from matplotlib.axes import Axes
    from matplotlib.patches import Polygon as PolygonPatch, Rectangle
    from matplotlib.ticker import FuncFormatter

    background = "#f5f3ec"
    ink = "#252b27"
    muted = "#69716b"
    square_color = "#315d40"
    area_color = "#8b66b0"
    chord_color = "#bb7213"
    excluded_color = "#b74834"
    inner_background = "#e6e6df"
    inner_area = float(polygon_area(inner_polygon))
    bottom_length = float(resource_chord_length(1, Fraction(1)))
    left_length = float(resource_chord_length(0, Fraction(1)))
    description = figure_description()
    plot.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 12,
        "text.color": ink,
        "axes.labelcolor": muted,
        "xtick.color": muted,
        "ytick.color": muted,
        "svg.fonttype": "none",
        "svg.hashsalt": description,
    })
    figure = plot.figure(figsize=(14, 11.2), facecolor=background)
    figure.text(.055, .955, "SQUARE PACKING ARCHIVE  /  LEAN-CHECKED COUNTEREXAMPLE",
        fontsize=11, color=square_color, weight="bold")
    figure.text(.055, .91, "Counterexample to Nagamochi’s Lemma 1", fontsize=25, weight="bold")
    figure.text(.055, .875,
        "The lemma requires σ(S) > 1. This square has σ(S) < 1.", fontsize=14)

    def draw_geometry(axes: Axes, *, detail: bool) -> None:
        axes.set_facecolor(background)
        axes.add_patch(Rectangle((0, 0), float(CONTAINER_SIDE), float(CONTAINER_SIDE),
            fill=False, edgecolor=muted, linewidth=1.2))
        axes.add_patch(Rectangle((1, 1), float(CONTAINER_SIDE - 2), float(CONTAINER_SIDE - 2),
            facecolor=inner_background, edgecolor="none"))
        axes.add_patch(PolygonPatch([(float(horizontal), float(vertical)) for horizontal, vertical in SQUARE],
            closed=True, facecolor=square_color, alpha=.14, edgecolor="none"))
        axes.add_patch(PolygonPatch([(float(horizontal), float(vertical)) for horizontal, vertical in SQUARE],
            closed=True, fill=False, edgecolor=square_color, linewidth=1.8))
        axes.add_patch(PolygonPatch([(float(horizontal), float(vertical)) for horizontal, vertical in inner_polygon],
            closed=True, facecolor=area_color, alpha=.75, edgecolor="none"))
        for axis, height in ((1, Fraction(1)), (1, CONTAINER_SIDE - 1),
                             (0, Fraction(1)), (0, CONTAINER_SIDE - 1)):
            limits = (float(RESOURCE_OFFSET), float(CONTAINER_SIDE - RESOURCE_OFFSET))
            fixed = (float(height), float(height))
            axes.plot(*( (limits, fixed) if axis == 1 else (fixed, limits)),
                color=muted, linewidth=.9, linestyle=(0, (4, 3)), zorder=2)
            chord = resource_chord(axis, height)
            if chord is not None:
                endpoints = tuple(map(float, chord))
                axes.plot(*( (endpoints, fixed) if axis == 1 else (fixed, endpoints)),
                    color=chord_color, linewidth=3.6, solid_capstyle="butt", zorder=4)
        for point in corner_points:
            present = contains_interior(point)
            axes.plot(*map(float, point), marker="o", markersize=6 if detail else 5,
                markerfacecolor=ink if present else background, markeredgecolor=ink,
                markeredgewidth=1.2, zorder=6)
        for point in edge_points:
            axes.plot(*map(float, point), marker="D", markersize=6 if detail else 5,
                markerfacecolor=background, markeredgecolor=excluded_color,
                markeredgewidth=1.3, zorder=6)
        axes.set_aspect("equal")
        axes.spines[["top", "right", "left", "bottom"]].set_visible(False)
        axes.tick_params(length=0, pad=5, labelsize=10)

    overview = figure.add_axes((.055, .505, .30, .325))
    draw_geometry(overview, detail=False)
    overview.set(xlim=(-.15, 4.15), ylim=(-.15, 4.15), xticks=range(5), yticks=range(5))
    overview.set_title("01  The full 4 × 4 container", loc="left", fontsize=14, pad=16, weight="bold")
    overview.text(2, 2, "Inner region\n[1,3]²", ha="center", va="center", color=muted, fontsize=13)
    overview.add_patch(Rectangle((.75, -.04), 1.45, 1.22, fill=False,
        edgecolor=muted, linewidth=.9, linestyle=(0, (2, 3))))
    figure.text(.065, .457, "Dashed box: enlarged at right", fontsize=11, color=muted)

    focus = figure.add_axes((.44, .49, .515, .345))
    draw_geometry(focus, detail=True)
    focus.set(xlim=(.75, 2.2), ylim=(-.08, 1.19), xticks=(1, 1.5, 2), yticks=(0, .5, .9, 1))
    focus.set_title("02  Only these resources contribute", loc="left", fontsize=14, pad=16, weight="bold")
    focus.annotate("Q = (1, 0.9)\ninside: +0.45", xy=(1, .9), xytext=(1.09, .64),
        fontsize=11, arrowprops={"arrowstyle": "-", "color": ink}, color=ink)
    focus.annotate("P = (2, 0.9)\noutside: +0", xy=(2, .9), xytext=(1.67, .53),
        fontsize=11, arrowprops={"arrowstyle": "-", "color": excluded_color}, color=excluded_color)
    focus.annotate(f"Inner area ≈ {inner_area:.6f}", xy=(1.30, 1.02), xytext=(1.15, 1.125),
        fontsize=10, color=area_color, arrowprops={"arrowstyle": "-", "color": area_color})
    focus.text(1.42, .948, f"chord ≈ {bottom_length:.6f}", fontsize=10, color=chord_color)
    focus.annotate(f"{left_length:.3f}", xy=(1, .918), xytext=(.77, .80), fontsize=10, color=chord_color,
        arrowprops={"arrowstyle": "-", "color": chord_color})
    focus.text(1.23, .28, f"λ = {float(FACTOR):.4f}", color=square_color, fontsize=16, weight="bold")
    focus.annotate("A", xy=tuple(map(float, SQUARE[0])), xytext=(-15, -17),
        textcoords="offset points", fontsize=11, color=square_color)
    figure.text(.475, .444, "Purple area + gold chords + the filled Q point. All plots use equal x/y scale.",
        fontsize=10, color=muted)

    figure.text(.055, .385, "03  The excluded point, magnified", fontsize=14, weight="bold")
    inset = figure.add_axes((.07, .19, .25, .17))
    draw_geometry(inset, detail=True)
    inset.set(xlim=(1.99955, 2.00025), ylim=(.89972, .90028),
        xticks=(2,), yticks=(.9,))
    inset.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:g}"))
    inset.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:.1f}"))
    edge_horizontal = VERTEX_HORIZONTAL + COSINE / SINE * RESOURCE_OFFSET
    assert edge_horizontal == Fraction(19999, 10000)
    assert Fraction(2) - edge_horizontal == Fraction(1, 10000)
    inset.plot((float(edge_horizontal), 2), (.9, .9), color=excluded_color, linewidth=1.1, zorder=5)
    inset.annotate("gap = 0.0001", xy=(1.99995, .9), xytext=(1.99963, .90016),
        fontsize=10, color=excluded_color,
        arrowprops={"arrowstyle": "-", "color": excluded_color})
    inset.text(1.99958, .89981, "inside S", color=square_color, fontsize=10)
    inset.text(2.00004, .89981, "outside", color=excluded_color, fontsize=10)
    inset.annotate("P", xy=(2, .9), xytext=(8, 8), textcoords="offset points", color=excluded_color)
    figure.text(.055, .115,
        "At y = 0.9, the square ends at x = 1.9999.\nThe point P has x = 2, strictly outside.",
        fontsize=11, linespacing=1.6)

    figure.text(.425, .385, "04  The total", fontsize=14, weight="bold")
    figure.text(.425, .34,
        f"{inner_area:.6f}  +  ½ × ({bottom_length:.6f} + {left_length:.3f})  +  0.45", fontsize=13)
    figure.text(.425, .26, f"σ(S) ≈ {float(score):.10f} < 1", fontsize=25, weight="bold", color=square_color)
    figure.text(.425, .224, "Values above are rounded. The exact score is given below.", fontsize=11, color=muted)
    figure.text(.425, .177, "Lean certificate:  σ(S) ≤ 199/200 < 1", fontsize=16, weight="bold")
    figure.text(.425, .137, "Other Q atoms, all P atoms, and top/right chords contribute zero.\nThe exact score is 25009470849041 / 25584000000000.",
        fontsize=11, linespacing=1.6, color=muted)
    figure.text(.055, .075, "This refutes the score lemma, not the packing theorem s(n² − 2) = n.",
        fontsize=12, weight="bold")
    figure.text(.055, .045, "Coordinates: cos θ = 80/1601, sin θ = 1599/1601, A = (10419467/5330000, 0).",
        fontsize=11, color=muted)
    figure.text(.055, .021, "Square Packing Archive · CC BY 4.0 · Generated from the exact rational coordinates.",
        fontsize=10, color=muted)
    figure_path("svg").parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(figure_path("svg"), metadata={"Date": None, "Description": description,
        "Title": "Counterexample to the Nagamochi resource-score premise"})
    figure.savefig(figure_path("png"), dpi=150, metadata={"Description": description})
    plot.close(figure)


def main() -> None:
    parser = argparse.ArgumentParser(description="Check the exact Nagamochi score counterexample.")
    parser.add_argument("--figure", action="store_true", help="Generate the SVG and PNG diagrams (requires matplotlib).")
    parser.add_argument("--check-figure", action="store_true", help="Check that committed diagrams match this source.")
    arguments = parser.parse_args()
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
    shifted_vertex_horizontal = VERTEX_HORIZONTAL + Fraction(1, 10000)
    contact_offset = Fraction(2) - shifted_vertex_horizontal
    assert -SINE * contact_offset + COSINE * RESOURCE_OFFSET == 0
    assert 0 < COSINE * contact_offset + SINE * RESOURCE_OFFSET < FACTOR
    assert FACTOR * SINE < 1

    display("Factor", FACTOR)
    display("Inner area", inner_area)
    for name, length in zip(("Bottom", "Top", "Left", "Right"), boundary_lengths):
        display(f"{name} boundary length", length)
    display("Q score", corner_score)
    display("P score", edge_score)
    display("Total score", score)
    display("Deficit below one", 1 - score)
    if arguments.figure:
        render_figure(inner_polygon, corner_points, edge_points, score)
    if arguments.check_figure:
        check_figure()


if __name__ == "__main__":
    main()
