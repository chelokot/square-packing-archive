# Proof status: 6, 10, 13, 22, and 33 squares

The complete minimum-side theorems are checked for **6, 22, and 33 squares**:

- `SquarePackingArchive.Records.Square6.s6_eq_three : IsMinimumSide 6 3`.
- `SquarePackingArchive.Records.Square22.s22_eq_five : IsMinimumSide 22 5`.
- `SquarePackingArchive.Records.Square33.s33_eq_six : IsMinimumSide 33 6`.

The other two exact results remain **Published · awaiting Lean**. A checked
construction proves an upper bound; checked lemmas alone do not prove optimality.

## Completed parts

| Squares | Checked in Lean                                                                                                                                                                                 | Still needed for optimality                                               |
| ------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| 6       | The full lower bound and matching grid construction.                                                                                                                                            | Nothing.                                                                  |
| 10      | The exact Göbel construction, Stromquist's boundary quadrilateral and pentagon lemmas, the initial ten-point unavoidable set, and assignment of these points to a hypothetical smaller packing. | The subsequent point replacements and final contradiction.                |
| 13      | Bentz's initial sixteen-point unavoidable set and the conclusion that at least two corner points have singleton owners.                                                                         | The replacement-point lemmas and the adjacent/non-adjacent case analysis. |
| 22      | The full lower bound and matching grid construction.                                                                                                                                            | Nothing.                                                                  |
| 33      | The full lower bound and matching grid construction.                                                                                                                                            | Nothing.                                                                  |

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
