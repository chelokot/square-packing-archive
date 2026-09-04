# Nagamochi 2005 formalization notes

## Current result: the square-container theorem is proved

Lean proves **`s(n²−2)=n` for every integer `n ≥ 2`**, with no scoring
hypothesis. The [compensation proof](nagamochi-compensation-proof.md) covers
`n ≥ 4`; independent proofs handle two and seven squares. The weaker family
`s(n²−1)=n` is also proved for every `n ≥ 2`, using an augmented measure.

The original per-square claim remains false. Lean proves
`¬ NagamochiResource.ScoresDilatedSquares 4`: the per-square resource inequality
used by our translation of Hiroshi Nagamochi's
[Packing Unit Squares in a Rectangle](https://doi.org/10.37236/1934)
has a counterexample.

The replacement proof does not try to prove this false premise. Instead,
it shows that other squares must supply enough excess score to compensate
every low-scoring square in a hypothetical packing. The paper's full theorem
for rectangular containers is not verified here.

The counterexample uses the original resource definition: area in
`[1,n−1]²`, four half-weighted boundary segments, eight `Q` atoms of weight
`9/20`, and the `P` atoms of weight `1/2`. The total mass remains `n²−2`.

See [the exact counterexample](nagamochi-score-counterexample.md) for coordinates,
component scores, reproducible calculations, and the precise distinction
between the failed lemma and the original packing claim.

## Kernel-checked components

| Component                                                          | Status                                         |
| ------------------------------------------------------------------ | ---------------------------------------------- |
| Resource measure and total mass `n²−2`                             | Proved                                         |
| Scaling, disjointness, finite-measure counting                     | Proved                                         |
| Conditional near-square theorem from `ScoresDilatedSquares`        | Proved, but its premise is false for size 4    |
| Every square with center in the inner rectangle: Cases 1–4         | Proved                                         |
| Every square with center in one of the four corner regions: Case 5 | Proved                                         |
| Canonical pinned terminal square                                   | Proved under its stated geometric hypotheses   |
| Universal edge-strip score: Cases 6–7                              | Cannot hold as stated; explicit counterexample |
| General `s(n²−2)=n`, using compensation and separate small cases   | Proved for every `n ≥ 2`                       |
| General `s(n²−1)=n`, using the augmented measure                   | Proved for every `n ≥ 2`                       |

These statements use the same `PlacedSquare`, arbitrary orthonormal frames,
and open square interiors. Only the augmented proof changes the resource
measure, raising each Q weight to `1/2`. The counterexample is
checked by the same Lean kernel as the positive results. No custom axioms,
unfinished proofs, or native evaluation are used.

### Inner-center geometry

`SquarePackingArchive.Nagamochi.score_gt_one_of_center_inner`, defined in
`NagamochiInnerCorners.lean`, proves the actual resource score exceeds one
whenever the dilated square lies in the container, its center lies in
`[1,n−1]²`, and `1 < factor ≤ 101/100`. There are no supplied chord,
area, missing-corner, or classification hypotheses.

The geometric proof uses active boundaries: a side is active when the square
meets that side inside the inner rectangle. A convex segment from any exterior
point to the inner center identifies an active side whose cut covers that point.
This avoids a false intermediate assumption that every full-line intersection
lies in the finite resource segment; a separate rational counterexample to
that assumption is also kernel-checked.

For active sides, a chord extending past a resource endpoint forces its
corresponding `Q` point into the square. Its weight pays for the missing
length. Adjacent cuts are bounded by exact right-triangle areas. Long chords
are combined with central-reflection half-area bounds. A finite budget theorem
combines these contributions, counting each resource only once.

The implementation is split into:

- `NagamochiClipping.lean`: active-boundary coverage and endpoint implications.
- `NagamochiCutBudget.lean`: finite cut coverage and score accounting.
- `NagamochiInner.lean`: arbitrary-frame cut classification and the no-`Q` case.
- `NagamochiInnerCorners.lean`: charged endpoint extensions and all inner centers.

### Corner centers and restricted edge-strip certificates

`score_gt_one_of_case5` handles all four container corners and every frame.
Container containment forces the two relevant `Q` points and the unit-corner
point into the square; convexity and positive inner area finish the score bound.

The edge-strip library also proves long grid chords, extraction of an indexed
`Q` or `P` point, several sufficient chord/point combinations, and the exact
canonical pinned terminal certificate. These remain valid restricted theorems.
They do not justify deforming an arbitrary edge-strip square to that certificate.

In the published Case 6 reduction, contact with `(2,0.9)` is required only to
occur on an edge. Lemma 6 additionally requires that contact edge to be one of
the two edges crossed by `y=1`. The counterexample demonstrates why that
incidence condition cannot be omitted.

## Earlier formula corrections

Two printed formulas already required correction during translation:

- Lemma 3's displayed factorization is twice the preceding polynomial; the
  correct factorization has an additional factor `1/2`. Its sign is unchanged.
- Lemma 6's printed chord numerator `t+t²` conflicts with the following
  identity `c+d=1`. The checked canonical geometry gives numerator `1+t²`.

Those algebraic corrections do not repair the universal score inequality.

## Archive policy

The records for 7, 14, 62, 79, and 98 squares now link to unconditional Lean
proofs. No record is promoted on the basis of the conditional near-square
reduction. Previously verified individual cases retain their independent proofs.
The archive distinguishes a published mathematical claim, a checked proof of
that claim, and a checked obstruction to a proposed proof.
