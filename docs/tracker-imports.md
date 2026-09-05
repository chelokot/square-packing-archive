# Tracker imports — September 2026

These are formalizations of published constructions, not new packing records.
The source snapshot and remaining work are in [issue #4](https://github.com/chelokot/square-packing-archive/issues/4).

## Six reconstructed packings

Each layout has exact coordinates, a Lean upper-bound proof, and a working viewer.
None of these six results proves optimality.

| Squares | Container side | Construction                                                                | View                                                               |
| ------- | -------------- | --------------------------------------------------------------------------- | ------------------------------------------------------------------ |
| 27      | `5 + √2/2`     | Göbel, 1979                                                                 | [Packing](https://chelokot.github.io/square-packing-archive/?n=27) |
| 38      | `6 + √2/2`     | Göbel, 1979                                                                 | [Packing](https://chelokot.github.io/square-packing-archive/?n=38) |
| 50      | `53/7`         | Schadt, 13 December 2025; exact optimization by Ellsworth, 14 December 2025 | [Packing](https://chelokot.github.io/square-packing-archive/?n=50) |
| 52      | `7 + √2/2`     | Göbel, 1979                                                                 | [Packing](https://chelokot.github.io/square-packing-archive/?n=52) |
| 67      | `8 + √2/2`     | Stenlund, 1980, extending Göbel's construction                              | [Packing](https://chelokot.github.io/square-packing-archive/?n=67) |
| 84      | `9 + √2/2`     | Stenlund, 1980, extending Göbel's construction                              | [Packing](https://chelokot.github.io/square-packing-archive/?n=84) |

### Diagonal strips

[One general Lean construction](../formal/SquarePackingArchive/Records/GoebelStrip.lean)
proves that `a(a+1) + 2 + b` squares fit in side `a + 1 + √2/2` when
`a ≥ 1` and `(b−1)√2/2 ≤ a−1`. Two triangular grids flank a strip of
45-degree squares; two more squares occupy the opposite corners.
The five instances above use `(a,b) = (4,5), (5,6), (6,8), (7,9), (8,10)`.

The viewer generates the same center formulas in exact `Q(√2)` arithmetic.
Every archive build checks containment and all square pairs independently.
Source and attribution: [tracker's diagonal-strip family](https://kingbird.myphotos.cc/packing/squares_in_squares__G%C3%B6bel_strips.html).

### Fifty squares

The [source construction](https://kingbird.myphotos.cc/packing/square-50.svg)
uses 34 axis-aligned squares and 16 rotated squares with cosine `4/5` and sine `3/5`.
All centers are rational. The [canonical coordinates](../archive/configurations/square-50-schadt-ellsworth.json)
generate a [Lean certificate](../formal/SquarePackingArchive/Records/Square50SchadtEllsworth.lean)
that checks unit frames, containment, and all 1,225 pairs in Lean's kernel.
Its theorem uses exactly `53/7`, not the displayed decimal approximation.

## Four historical inequalities

[These proofs](../formal/SquarePackingArchive/Records/HistoricalRadicalBounds.lean)
enlarge our existing, stronger 68- and 69-square packings. They establish the
historical upper bounds below but **do not reconstruct the original layouts**.
Those coordinate sets remain part of the backlog.

| Squares | Bound         | Attribution and source                                                            |
| ------- | ------------- | --------------------------------------------------------------------------------- |
| 68      | `6 + 2√2`     | [Stenlund, 1980](https://kingbird.myphotos.cc/packing/square-68_r1.svg)           |
| 68      | `15/2 + √7/2` | [Cantrell, September 2002](https://kingbird.myphotos.cc/packing/square-68_r2.svg) |
| 68      | `13/3 + 2√5`  | [Brendberg, June 2023](https://kingbird.myphotos.cc/packing/square-68_r3.svg)     |
| 69      | `5/2 + 9√2/2` | [Friedman, 1997](https://kingbird.myphotos.cc/packing/square-69_r1.svg)           |

The first source's caption incorrectly writes `5 + 2√2`; its decimal and
container size correspond to `6 + 2√2`. The archive uses the latter expression.

We also corrected an earlier attribution error: the displayed 68-square bound
`8.80357394752856` belongs to [Schadt's improvement on 19 December 2025](https://kingbird.myphotos.cc/packing/square-68_r4.svg),
not Brendberg's June 2023 result. Its existing Lean proof checks that rational
upper bound via our stronger construction; it is not an exact algebraic
reconstruction of Schadt's original layout.

Discovery dates stay separate from the Lean check date, 5 September 2026.
Only factual construction data was reconstructed. Source artwork and prose
were not copied or relicensed.
