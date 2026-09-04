# Can the failed lemma lead to a better packing?

Status, 5 September 2026: **no counterexample to the packing theorem and no
replacement proof of the full theorem yet**. The work below tests whether the
[low-scoring square](nagamochi-score-counterexample.md) can help build a packing
of 62 unit squares in a container with side less than 8.

## The `n²−1` family now has a complete Lean proof

For every integer `n ≥ 2`, **`s(n²−1)=n`** is now proved without an unproved
scoring hypothesis. This is not yet the requested `n²−2` theorem.

The repaired rule keeps the original area and extended lines, but raises each
Q point's weight from `0.45` to `0.5`. Every fitting square with side
`1 < λ ≤ 1.01` now scores more than one. The eight increases add `0.4` to the total resource mass,
making it `n²−1.6`. That is enough to exclude `n²−1` squares, but not `n²−2`.

[NagamochiAugmented.lean](../formal/SquarePackingArchive/NagamochiAugmented.lean)
proves `Records.NearSquare.squareMinusOne_isMinimumSide` for all `n ≥ 2`,
including containment, arbitrary rotations, all four edges, and the packing
count. Its axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. The archive now marks the previously unchecked exact results for
63, 80, and 99 squares as Lean verified.

## Every marked point would have an owner

The repaired measure also restricts a hypothetical packing of `N=n²−2` squares
below side `n`. After a small dilation, its total score is greater than `N`
and at most `N+0.4`.

Every P and Q point must lie strictly inside exactly one square. Leaving even
one uncovered would waste `0.5` of the measure, more than the available `0.4`.
Each square must score less than `1.4` under the repaired rule. A square owning
two adjacent bottom P points would score more than `1.5`, so that cannot happen.

These are consequences of the actual packing assumptions, proved in
[NagamochiPackingConstraints.lean](../formal/SquarePackingArchive/NagamochiPackingConstraints.lean).
They are necessary conditions, not a proof that such a packing is impossible.

## A tilted-square count, proved in Lean

Any such packing must have **at least 13 tilted squares**. Here “tilted” means
that the square's edges are not parallel to the container's edges; there is no
minimum angle in this statement.

More generally, for every integer `n ≥ 2`, a packing of `n²−2` unit squares in
a container with side less than `n` requires at least `2n−3` tilted squares.

The proof does not use Nagamochi's scoring rule:

1. Let the container side be `L < n`. Put grid points at `(iL/n, jL/n)` for
   integers `1 ≤ i,j ≤ n−1`. There are `(n−1)²` points, spaced less than one
   unit apart.
2. Every axis-aligned unit square in the container contains a grid point
   **strictly inside**. In each coordinate, round the square's center to the
   nearest grid coordinate. The distance is less than half a unit, and the
   containment bounds keep the chosen point away from the container walls.
3. Two squares with disjoint interiors cannot contain the same grid point.
   Therefore at most `(n−1)²` squares contain any grid point.
4. At least `n²−2−(n−1)² = 2n−3` squares contain none. Each must be tilted.

The grid is compressed to the actual container size. Using unscaled integer
points instead would be wrong: a unit square can have integers only on its
boundary.

[GridObstruction.lean](../formal/SquarePackingArchive/GridObstruction.lean)
proves the grid-coverage, counting and tilt statements. The main theorems are
`Packing.sixtyTwo_requires_thirteen_tilted` and
`Packing.squareMinusTwo_requires_many_tilted`. They are included in the regular
Lean build and axiom audit and use only `propext`, `Classical.choice`, and
`Quot.sound`.

This rules out a counterexample with only a few tilted squares. It does not
rule out a coordinated arrangement with many tilted squares.

## Numerical search

We ran 24 starts: 12 at container side `7.9999` and 12 at `7.999999`. The
starting arrangements included boundary tilts, alternating tilted rows,
checkerboard tilts, and random positions and angles. All centers and angles
were free to move.

**All 24 candidates failed exact containment or non-overlap checks.** The
closest numerical results returned almost to the grid but retained small
overlaps. At side `7.999999`, the best candidate still had a maximum geometric
violation of about `1.85×10⁻⁷`. That is not a packing.

The [experiment](../experiments/near-square-search/README.md) includes the
optimizer, tests, saved candidates, exact rational checker, and commands to
repeat the search or replay its results. A failed local search proves no lower
bound. These two target sizes also do not exhaust all possible improvements
below 8.

## Repeating the low-scoring square

We also checked a simple way of placing copies together: translate the square
horizontally by `λ/s`, where `λ=10001/10000` is its side and `s=1599/1601` is
the sine of its angle. This places consecutive copies against a common edge.

Six copies fit in an 8×8 box without overlapping. Their total score is

```text
133822474074449677 / 20454408000000000 = 6.542476031300914… > 6.
```

The first square still scores `0.977543…`, but the second contains **two** P
points, `(2,0.9)` and `(3,0.9)`, and scores `1.513043…`. Its extra score more
than offsets the first square's deficit. A seventh copy at the same spacing
crosses the right wall.

The [row probe](../experiments/near-square-search/row_compensation.py) checks
these facts with exact fractions, including every pair's separation and the
score components. Its tests also reproduce the original 4×4 counterexample.
This is an exact Python calculation for one arrangement, not a Lean proof or
a general rule about neighboring squares.

## A repaired bottom-edge case, proved in Lean

[NagamochiEdgeStripNoCorners.lean](../formal/SquarePackingArchive/NagamochiEdgeStripNoCorners.lean)
proves that a square in the bottom edge strip scores greater than one if it
contains none of the eight Q points, the special points near the corners worth
`0.45` each. This covers every rotation angle, including axis-aligned squares.

The precise assumptions are: integer container side `n ≥ 3`, square side
`1 < λ ≤ 1.01`, containment in `[0,n]²`, and center coordinates
`1 ≤ x ≤ n−1`, `y ≤ 1`. The formal statement uses the archive's representation
of a unit square dilated about the origin by `λ`, with the original square also
fitting a container. It does not assume a covered P point, a long intersection,
or an area estimate; those are derived from the geometry.

The proof uses two new geometric estimates:

- [NagamochiBoundaryAnchor.lean](../formal/SquarePackingArchive/NagamochiBoundaryAnchor.lean)
  finds a point inside an edge-strip square on the nearest counting line. If
  the square contains no Q points, its entire intersection with that line lies
  in the counted segment. It also bounds the area above the line by the counted
  central area plus the parts cut off at the other three sides.
- [NagamochiCapLowerBound.lean](../formal/SquarePackingArchive/NagamochiCapLowerBound.lean)
  constructs the triangular part of a square above a line crossing two adjacent
  edges. For a square larger than unit size that stays above the bottom wall,
  its area above `y=1` plus half the full intersection length at `y=1` is greater
  than `1/2`. The triangle and its area are derived from the square's coordinates,
  not assumed.

For a short intersection, the area above the bottom counting line plus half
the intersection length exceeds `0.5`. The other counted lines cover the area
lost outside the central region. A covered P point contributes another `0.5`.
Long intersections and axis-aligned squares are handled separately.

The final theorem is `score_gt_one_of_bottom_strip_without_corners`. All three
modules are included in the regular Lean build and axiom audit; they use only
`propext`, `Classical.choice`, and `Quot.sound`.

The later [Q-point proof](../formal/SquarePackingArchive/NagamochiEdgeStripWithCorners.lean)
strengthens this: if just the two horizontal Q points are absent, central area
plus half the bottom-line intersection exceeds `0.5`. Other Q points may be
present. The lost cap area lies in two narrow strips and is bounded directly.
This is the geometric step behind the complete `n²−1` proof above.

The [symmetry proofs](../formal/SquarePackingArchive/NagamochiResourceSymmetry.lean)
transport the measures through coordinate exchange and reflection. Thus the
augmented scoring argument covers every edge, not just the bottom.

## Repairs that do not work

Removing the short line extensions to pay for higher Q weights fails, even for
an axis-aligned square. Replacing those extensions with uniformly weighted
diagonals also fails. Exact linear inequalities from four squares rule out
repairing the original markings by changing their four symmetric weights while
keeping the total budget at `n²−2`.

The [repair experiments](../experiments/resource-repair/README.md) include the
witnesses and checks. The geometric coefficients are checked in exact Python;
the resulting scalar contradictions are checked in Lean.

Simple local compensation rules fail too. A low-scoring square and the owner
of its nearest missing P point can have a combined score below two. The
[exact pair examples](../experiments/boundary-compensation/README.md) rule out
that shortcut; compensation may require a longer chain or a different argument.

## What remains

The current repair attempt follows chains of squares along the container's
boundary. Several parts are now checked in Lean:

- A low-scoring bottom-edge square in a positive coordinate frame must cross
  the next marked point's vertical segment.
- A right-going neighbor either crosses the next column or satisfies a
  terminal condition involving its vertex height.
- Under that terminal condition, a P-point owner's actual area and line
  score can repay two incoming shortfalls. The proof checks that the counted
  area really lies inside the inner square, including the last P column.
- No square can own P points on different container sides.

These statements are in
[NagamochiBoundaryPropagation.lean](../formal/SquarePackingArchive/NagamochiBoundaryPropagation.lean),
[NagamochiChainStep.lean](../formal/SquarePackingArchive/NagamochiChainStep.lean),
[NagamochiEndpointResource.lean](../formal/SquarePackingArchive/NagamochiEndpointResource.lean),
and [NagamochiEdgeOwnership.lean](../formal/SquarePackingArchive/NagamochiEdgeOwnership.lean).
They do not yet connect all boundary chains to a global score bound. In
particular, the initial shortfall must be tracked quantitatively, the corner
endpoints must be covered, and the complete argument must handle every frame.

To disprove the theorem, we need an actual non-overlapping packing below the
claimed bound, followed by a Lean certificate. To prove it, we need a global
argument that covers arrangements with many tilted squares. Neither result
follows from the tilt count or the unsuccessful searches above.

The `n²−2` claims remain unverified. Neither failed searches nor conditional
lemmas are used to promote them.
