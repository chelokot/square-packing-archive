# Proof status: 6, 10, 13, 22, and 33 squares

The complete minimum-side theorem is checked for **33 squares**:
`SquarePackingArchive.Records.Square33.s33_eq_six : IsMinimumSide 33 6`.

The other four exact results remain **Published · awaiting Lean**. A checked
construction proves an upper bound; checked lemmas alone do not prove optimality.

## Completed parts

| Squares | Checked in Lean                                                                                                                                                                                 | Still needed for optimality                                                         |
| ------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
| 6       | The two seven-point configurations, their incidence restrictions, the two possible center-free matchings, and explicit contact-coordinate identities.                                           | Excluding the remaining arrangements, including the center-covered case.            |
| 10      | The exact Göbel construction, Stromquist's boundary quadrilateral and pentagon lemmas, the initial ten-point unavoidable set, and assignment of these points to a hypothetical smaller packing. | The subsequent point replacements and final contradiction.                          |
| 13      | Bentz's initial sixteen-point unavoidable set and the conclusion that at least two corner points have singleton owners.                                                                         | The replacement-point lemmas and the adjacent/non-adjacent case analysis.           |
| 22      | The exceptional-square distance inequalities and the boundary-chord estimate.                                                                                                                   | Connecting the moving configurations, their exceptional point, and the final count. |
| 33      | The full lower bound and matching grid construction.                                                                                                                                            | Nothing.                                                                            |

The initial configurations and geometric lemmas cover arbitrary rotations. The
packing arguments start with interior-disjoint squares; where a proof needs
closed-disjoint squares, an explicit scaling theorem supplies them.

The integrated theorems are included in `formal/SquarePackingArchive/Audit.lean`.
Their axiom checks allow only `propext`, `Classical.choice`, and `Quot.sound`.

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
