# Proof status: 6, 10, 13, 22, and 33 squares

The complete minimum-side theorems are checked for **6, 10, 22, and 33 squares**:

- `SquarePackingArchive.Records.Square6.s6_eq_three : IsMinimumSide 6 3`.
- `SquarePackingArchive.Records.Square10.s10_eq_goebel : IsMinimumSide 10 (3 + Real.sqrt 2 / 2)`.
- `SquarePackingArchive.Records.Square22.s22_eq_five : IsMinimumSide 22 5`.
- `SquarePackingArchive.Records.Square33.s33_eq_six : IsMinimumSide 33 6`.

The 13-square exact result remains **Published · awaiting Lean**. A checked
construction proves an upper bound; checked lemmas alone do not prove optimality.

## Completed parts

| Squares | Checked in Lean                                                                                                         | Still needed for optimality                                               |
| ------- | ----------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| 6       | The full lower bound and matching grid construction.                                                                    | Nothing.                                                                  |
| 10      | The full lower bound and matching Göbel construction.                                                                   | Nothing.                                                                  |
| 13      | Bentz's initial sixteen-point unavoidable set and the conclusion that at least two corner points have singleton owners. | The replacement-point lemmas and the adjacent/non-adjacent case analysis. |
| 22      | The full lower bound and matching grid construction.                                                                    | Nothing.                                                                  |
| 33      | The full lower bound and matching grid construction.                                                                    | Nothing.                                                                  |

The initial configurations and geometric lemmas cover arbitrary rotations. The
packing arguments start with interior-disjoint squares; where a proof needs
closed-disjoint squares, an explicit scaling theorem supplies them.

The integrated theorems are included in `formal/SquarePackingArchive/Audit.lean`.
Their axiom checks allow only `propext`, `Classical.choice`, and `Quot.sound`.

## Why six squares need side three

The checked proof follows Stromquist's nine-point argument. An eight-point
perimeter set ensures every square contains a point other than the center.
Geometry prevents adjacent perimeter points from being the sole points of two
different squares. A finite counting argument then forces one square to contain
exactly the center and one neighboring point.

After a rotation or reflection, that square must contain four points of a
second, eight-point unavoidable set. Only four points remain for the other five
squares, a contradiction. The proof handles arbitrary rotations and touching
squares: a hypothetical packing with side below three is first transformed into
a closed-disjoint family fitting side three.

The final theorem is in `formal/SquarePackingArchive/Records/Square6Exact.lean`.

## Why ten squares need side 3 + √2 / 2

The proof follows Stromquist's point-ownership argument. An initial ten-point
unavoidable set assigns a different point to each square in a hypothetical
smaller packing. Replacement configurations force the four side squares to
contain points on eight specified segments.

For any choice of those eight points, Lean proves that they, the four corner
points, and the center form an unavoidable set. The eight boundary points belong
to the four side squares; the four corner points belong to four other squares.
Only the center remains for two squares, contradicting disjointness.

The proof checks all eight segment parameters independently. Its triangle
coverage and boundary arguments handle arbitrary rotations. The fixed
replacement configurations include both rotated inner points, with their
ownership proved separately.

The final theorem is in `formal/SquarePackingArchive/Records/Square10Exact.lean`.
The [generated coverage proofs](generated-geometric-covers.md) are reproducible
and checked by Lean, not trusted as external certificates.

## Layouts

Every catalogued square count has coordinates in the viewer. Grid constructions
are generated from manifest recipes; the 5- and 10-square constructions use exact
numbers in Q(√2). Every generated layout is checked for containment and pairwise
non-overlap using exact arithmetic during the archive build.

An uncatalogued count displays a labelled **grid example**, not a best-known
record. These examples do not change the proof-status matrix.

## Sources

- Walter Stromquist, [Packing 10 or 11 Unit Squares in a Square](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v10i1r8).
- Wolfram Bentz, [Optimal Packings of 13 and 46 Unit Squares in a Square](https://doi.org/10.37236/398).
- Wolfram Bentz, [Optimal Packings of 22 and 33 Unit Squares in a Square](https://arxiv.org/abs/1606.03746).
