# The 13-square proof

The formalization follows [Bentz's 2010 point-set and counting argument](https://doi.org/10.37236/398),
with corrected auxiliary configurations. Lean checks the complete theorem
**s(13) = 4**, including all generated coverage proofs:

[`s13_eq_four : IsMinimumSide 13 4`](../formal/SquarePackingArchive/Records/Square13Exact.lean).

The packing model allows arbitrary rotations and touching boundaries. A packing
with side strictly below four is first turned into a closed-disjoint family
fitting side four. The proof then assigns carefully chosen points to squares and
shows that thirteen squares would need more points than are available.

## Changes to the auxiliary configurations

- Add `(1.5, 1)` to the points already forced inside the first corner-restricted
  square. The checked replacement lemma proves the entire horizontal segment
  from `(1.12, 1)` to `(1.74, 1)` is inside that square.
- Replace the moving-point argument in case R1 by eight rational heights:
  `2.44, 2.52, 2.60, 2.68, 2.76, 2.84, 2.92, 3.00`. The rectangle-intersection
  proof guarantees that the square contains at least one of these points. When
  that point is `(1, 3)`, also include the unassigned point `(1, 2.84)`.
- In R2's first subcase, add the unassigned point `(3.1, 3)`. There is enough
  slack in the counting argument for this extra point.
- In R3, move the unassigned point `(1, 3)` to `(0.95, 3)`. This keeps the same
  number of points.

Every modified configuration has its own Lean coverage proof. A point search
or a picture is not treated as proof. The
[generated files are reproducible](generated-geometric-covers.md); the final
theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Two printed sets are avoidable

Lean checks that each square below fits inside `[0, 4]²` and misses every point
in the corresponding printed set. A frame `(c, s)` has orthogonal unit axes
`(c, s)` and `(-s, c)`.

| Printed set       | Square center       | Frame `(c, s)`   | Lean proof                                                                     |
| ----------------- | ------------------- | ---------------- | ------------------------------------------------------------------------------ |
| R2, first subcase | `(569/200, 109/40)` | `(20/29, 21/29)` | [R2 counterexample](../formal/SquarePackingArchive/BentzThirteenR2Repair.lean) |
| R3                | `(7/10, 2553/1000)` | `(4/5, 3/5)`     | [R3 counterexample](../formal/SquarePackingArchive/BentzThirteenR3Repair.lean) |

These refute the claims that those particular point sets are unavoidable on
their own. They do **not** provide thirteen nonoverlapping squares in a smaller
container, or refute the packing theorem. In particular, they do not establish
compatibility with the other squares assumed in the surrounding argument.

## Statement corrections

Lemma 10 prints `(1, 1.74)` where the later configuration uses `(1.74, 1)`.
The formalization proves the horizontal version. Lemma 11 is used with its
opening assumption that the square is corner-restricted, not merely the shorter
list of excluded points repeated in that lemma.

For Corollary 7, the formal statement uses a rectangle of width one and height
`0 < b < 2√2 − 2`, with the square's center inside the rectangle and all four
rectangle corners outside the square. Its two vertical intersection lengths
total at least `2√2 − 2`; each is
strictly greater than `2√2 − 2 − b`. The proof establishes that the intersections
are actually inside the rectangle edges, using exclusion of the four corners.
