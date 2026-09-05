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
The original 68-square Stenlund and 69-square Friedman layouts have now also
been reconstructed in the quadratic batch below. The Cantrell and Brendberg
coordinate sets remain part of the backlog.

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

## Twenty-one quadratic layouts

The September 6 batch adds 17 historical claims and attaches reconstructed
coordinates to four existing claims. The archive now contains 72 claims and
65 configurations. These are upper bounds, not optimality proofs or newly
discovered packing records.

| Squares | Side          | Construction                                                                                                  |
| ------- | ------------- | ------------------------------------------------------------------------------------------------------------- |
| 11      | `5/2 + √2`    | Göbel and independently Cottingham, 1979; equal-bound variant                                                 |
| 11      | `2 + 4√2/3`   | Hämäläinen, known by April 20, 1980                                                                           |
| 17      | `7/3 + 5√2/3` | Hämäläinen, 1980; historical, not the current best known bound                                                |
| 18      | `(7 + √7)/2`  | Hämäläinen 1980, Gustafsson 1981, Cantrell September 2002, and Gensane–Ryckelynck 2004: four separate layouts |
| 19      | `4 + 2√2/3`   | Göbel, early 1979                                                                                             |
| 19      | `7/2 + √2`    | Cottingham, early 1979                                                                                        |
| 19      | `3 + 4√2/3`   | Wainwright and independent rediscoverers, November 1979–March 1980                                            |
| 26      | `7/2 + 3√2/2` | Friedman, 1997; bilateral-symmetry variant                                                                    |
| 40      | `4 + 2√2`     | Göbel, 1979                                                                                                   |
| 53      | `(13 + √7)/2` | Ellsworth, February 7, 2026; alternate exact reconstruction                                                   |
| 65      | `5 + 5√2/2`   | Göbel, 1979                                                                                                   |
| 66      | `3 + 4√2`     | Stenlund, 1980                                                                                                |
| 68      | `6 + 2√2`     | Stenlund, 1980; centered symmetric variant                                                                    |
| 69      | `5/2 + 9√2/2` | Friedman, 1997                                                                                                |
| 82      | `6 + 5√2/2`   | Probably Friedman, 1997, extending Göbel's 65-square construction; attribution and date tentative             |
| 85      | `11/2 + 3√2`  | Friedman, 1997; bilateral-symmetry variant                                                                    |
| 86      | `(17 + √7)/2` | Friedman, 1997, generalizing Gustafsson's 18-square layout                                                    |
| 89      | `5 + 7√2/2`   | Stenlund, 1980                                                                                                |

Each coordinate file retains its specific source URL. The four 18-square
alternatives have equal bounds; they are not presented as successive
improvements. The 19-square date field uses the conservative known-by year
1980, while its source title preserves the documented date interval and the
claim credits all named independent discoverers.

For 53 squares, GPT 6 Astra replaced two auxiliary algebraic rotations with
exact rational half-angle tangents `6/25` and `2/7`. The published container
side is unchanged. This is an alternate reconstruction, not a claim to have
recovered Ellsworth's exact original coordinates or improved his bound.

The general [quadratic certificate theorem](../formal/SquarePackingArchive/QuadraticCertificate.lean)
proves that the exact unit-frame, containment, and separating-axis checks
produce a packing. Generated record certificates evaluate those checks in
Lean's kernel, with separate per-row proofs to limit peak memory and without
native-evaluation oracles. Four newly reconstructed
historical layouts retain their earlier inequality evidence and additionally
have their own kernel-checked, axiom-audited coordinate certificates.

Exact reconstruction recipes and regression tests are in
`scripts/reconstruct-quadratic-tracker.py`, `scripts/reconstruct-quadratic-history.py`,
and `scripts/reconstruct-sqrt-seven.py`. CI checks both recipe reproducibility
and generated Lean correspondence, then compiles the certificates sequentially
to bound peak memory use before checking the complete library.

The original discoverers retain their credits. The exact-coordinate
reconstruction and Lean formalization are credited to GPT 6 Astra.
