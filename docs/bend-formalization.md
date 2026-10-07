# Bend formalization

The `bend/` directory restates the canonical problem in
[Bend 2](https://github.com/bendlang/bend) and proves results against it with
Bend's kernel, which is itself proved correct in Lean (`bend --verdict`). The
shared number theory lives in [`chelokot/bend-math`](https://github.com/chelokot/bend-math),
pinned as the `bend/bend-math` submodule.

## What a Bend result means

Bend has no type of classical real numbers, and its constructive reals cannot
decide comparisons. Every Bend theorem here is therefore stated for **every
ordered field** satisfying `bend-math/Field.bend`. The real numbers are such a
field, so each theorem holds for them in particular. That last step is
ordinary mathematics and is not checked by Bend.

The interface writes equality as `a ≤ b` and `b ≤ a`, and states every axiom
through the order. This keeps the axioms satisfiable by the one-element
structure, which the kernel requires before it accepts a generic proof, and by
the rationals, which `bend-math/RationalField.bend` proves. The field also
provides `half` with `half + half = 1`.

## Correspondence with `Problem.lean`

| Lean                                                       | Bend (`bend/Problem.bend`)                                                            |
| ---------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| `Point`                                                    | `Problem.Point`                                                                       |
| `Frame` with `cosine ^ 2 + sine ^ 2 = 1`                   | `Problem.Frame`, the equation as two inequalities                                     |
| `PlacedSquare.point`: `center + (x·c − y·s, x·s + y·c)`    | the same expression inside `Containment`                                              |
| `Contains`: `∃ x y, abs x ≤ 1/2 ∧ abs y ≤ 1/2 ∧ point = …` | `Containment`: witnesses, `−half ≤ x ≤ half`, and both coordinates equal              |
| `InteriorContains`: strict bounds                          | `InteriorContainment`: `half ≤ x` and `x ≤ −half` are impossible                      |
| `Container.Contains`                                       | `InContainer`                                                                         |
| `Packing n side` over `Fin n`                              | `Packing` over indices `i` with `i + 1 ≤ n`; distinct indices have disjoint interiors |

## Checked results

Each catalog claim with a Bend proof is a law of `bend/MANIFEST.bend`, which
`scripts/generate-bend-manifest.py` writes from `archive/manifest.json`: an
upper bound `s(n) ≤ v` is the law `<claim>_upper`, a packing of `n` squares in
side `v`, and a lower bound `v ≤ s(n)` is the law `<claim>_lower`, `v ≤ side`
for every packing of at least `n` squares. `bend/PROOF.bend` proves each law, so
`--verdict` checks every claim exactly as the catalog states it.

| Claims                      | Proofs in `bend/PROOF.bend`                     |
| --------------------------- | ----------------------------------------------- |
| `s(2) = s(3) = 2`           | `Grids.packing` and `Small.lower_bound_two`     |
| `s(5) = 2 + √2/2`           | `Five.packing` and `Five.lower_bound`           |
| `s(6) = s(7) = s(8) = 3`    | `Grids.packing` and `StromquistSix.lower_bound` |
| `s(k²) = k` for `1 ≤ k ≤ 9` | `Grids.packing` and `Chords.lower_bound`        |

A value with `√2` is stated for every `root ≥ 0` of the field with
`root · root = 2`: the laws of `s(5)` take such a root, so they hold in every
ordered field that has one. `bend/Five.bend` packs four axis-aligned squares in
the corners and one turned by 45° in the middle, and proves the lower bound as
`Square5.lean` does: a square that fits `[0, 2 + √2/2]²` contains one of four
points, and five closed-disjoint squares cannot share four points.

`bend/LAWS.bend` keeps the general laws: the local coordinates of a square
(`Laws.contains_iff_local_coordinates_forward` and `_backward`, and the same
for the open square), the symmetries of packings, `Laws.fewer_squares`, the
scaling to a closed-disjoint family, and the chord and area bounds below.

`bend/Chords.bend`, written by `scripts/generate-bend-chords.py`, starts the
area argument for `s(k²) = k`. A square in first-quadrant normal form meets the
vertical line at `x` in an open chord whose ends are piecewise linear in `x`,
with breakpoints at the abscissae of its vertices. Points strictly inside the
chord are interior points of the square, and the chord of a square that fits
`[0, side]^2` lies in `[0, side]`. Chords of squares with disjoint interiors do
not overlap, so `Laws.vertical_chords_fit_the_side` bounds the total length of
the chords of a packing at any `x` by `side`.

`Laws.squares_fit_by_area` turns the chord bound into the area bound: a packing
of `n` unit squares in side `s` has `n ≤ s²`. `Chords.area` is the area of a
square left of `x`, piecewise quadratic in `x` with the same breakpoints. On an
interval `[a, b]` with no vertex abscissa strictly inside, the area gained is
`(b − a)` times the chord length at the midpoint (`Chords.strip`); the midpoint
is used because the chord length of an axis-aligned square jumps at its sides.
So `Σ area(x) − s·x` does not increase between breakpoints, and `Chords.sweep`
carries that across all `4n` vertex abscissae with the bookkeeping of
`bend-math/Sweep.bend`. Each area is 0 at `x = 0` and 1 at `x = s`.

The upper bounds, and the basic grid bound `s(n) ≤ ⌈√n⌉` the site shows for
counts without a catalogued claim, are one theorem: `bend/Grids.bend` packs
any `n ≤ k²` axis-aligned unit squares in side `k`, column by column. Square
`i` sits in the cell whose column is the quotient and whose row is the
remainder of `i` by `k`, built by `Grids.place` with the proof that
`quotient · k + remainder = i`. `bend/Grid.bend` proves that a cell fits in side
`k` and that cells whose positions differ by at least 1 in one coordinate have
disjoint interiors; two different indices differ in their remainder or, with
equal remainders, in their quotient.

`bend/Small.bend` proves the lower bounds for one and two squares, following
`NearSquare.lean`'s two-square argument: the corners of a square in first-quadrant normal form are
`cosine + sine ≥ 1` apart, and a square that fits `[0, 2]^2` contains `(1, 1)`,
so two squares in side less than 2, scaled to closed-disjoint squares in
`[0, 2]^2`, would share that point.

Run the check with Bend at the pinned revision and Lean 4.34.0:

```console
git submodule update --init
bun /path/to/bend/bend2/main.ts bend/PROOF.bend --verdict
```

## The lower bound

`bend/StromquistSix.bend` ports Stromquist's argument from the
`StromquistSix*` Lean files. The law takes a packing of any `count ≥ 6`
squares: the kernel checks a generic proof only when each `~` parameter has a
model, and a packing has one when `count` is a parameter (at zero squares) but
not at a fixed six. Its first six squares give the theorem for six.

A packing of side less than 3 scales to six
squares that fit `[0, 3]^2` with pairwise disjoint closed squares
(`bend/Scaling.bend`). Each square is moved into first-quadrant normal form by
the symmetries of the container (`bend/Symmetry.bend`), and its incidences with
the nine key points `{1, 3/2, 2}^2` and the extra points of the centre
patterns become Booleans decided by the field order (`bend/Membership.bend`).

The geometric facts about one square are stated in normal form and proved by
inequality certificates: it holds a key point (`bend/Unavoidable.bend`, the
perimeter and unavoidable triangles of `Unavoidable.lean`), the pairs it can
hold, the centre patterns and their extra points (`bend/Stromquist.bend`), and
the boundary points shared by two squares holding adjacent single key points
(`bend/Singletons.bend`). Disjointness turns them into constraints on the 54
incidence bits, and `bend/Incidence.bend` shows by a Boolean case analysis
that no six rows satisfy them.

The certificates are found by `bend-math/tools/certificate.py` and stored in
`scripts/bend-certificates.json`, so the generators rewrite every `.bend`
file without a solver:

```console
for generator in scripts/generate-bend-*.py; do python3 "$generator"; done
```

Square roots do not appear: where the Lean proof bounded `cosine + sine` by
`√2`, the Bend proof uses the rational bound `17/12`.

Bend issues met along the way are tracked in
[`bend-math/docs/bend-issues.md`](https://github.com/chelokot/bend-math/blob/main/docs/bend-issues.md).
