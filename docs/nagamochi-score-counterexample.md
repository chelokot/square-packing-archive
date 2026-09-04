# Counterexample to the Nagamochi resource-score premise

This is a counterexample to the per-square score inequality, not a packing of
`n²−2` unit squares in a smaller container and not a disproof of `s(n²−2)=n`.

## Exact geometry

Use a container `[0,4]²`, square side `λ = 10001/10000`, and orthonormal frame

```text
cosine = 80/1601
sine   = 1599/1601
cosine² + sine² = 1
```

Let the lower vertex be

```text
A = (2 − (80/1599)·(9/10) − 1/10000, 0)
  = (10419467/5330000, 0).
```

The four vertices, in counterclockwise order, are

```text
A
A + λ·(cosine, sine)
A + λ·(cosine − sine, sine + cosine)
A + λ·(−sine, cosine).
```

All vertices lie in the container. Only the resource atom `Q=(1,9/10)` is in
the square interior; no `P` atom is present. No `Q` or `P` atom is on the square
boundary, so changing open/closed atom membership does not resolve the issue.

## Independent exact calculation

[The standard-library Python checker](../scripts/check-nagamochi-counterexample.py)
uses rational polygon clipping, line intersection, and shoelace area. Assertions
use `Fraction` only; decimal conversion is for display.

| Contribution                | Exact value                     |
| --------------------------- | ------------------------------- |
| Inner area                  | `611022059041 / 25584000000000` |
| Bottom chord length         | `1251468079 / 1279200000`       |
| Left chord length           | `29/1000`                       |
| Top and right chord lengths | `0`                             |
| Q score                     | `9/20`                          |
| P score                     | `0`                             |

Each chord has weight `1/2`. The total score is therefore

```text
25009470849041 / 25584000000000
= 0.977543419677962789… < 1.
```

Reproduce from the repository root:

```console
python3 scripts/check-nagamochi-counterexample.py
```

## Lean certificate

[NagamochiCounterexample.lean](../formal/SquarePackingArchive/NagamochiCounterexample.lean)
constructs the square in the archive's existing geometric model and proves
membership equivalence with four explicit rational half-plane inequalities.
It proves both the original closed unit square fits in a container of side
`4/λ` and the closed dilated square fits in `[0,4]²`. It then establishes the
exact atomic contributions and sufficient
upper bounds on the continuous contributions:

```text
inner area ≤ 3/100
bottom chord ≤ 1
left chord ≤ 3/100
top chord = right chord = 0
score ≤ 3/100 + (1/2)·(1 + 3/100) + 9/20 = 199/200 < 1.
```

The final theorem is

```lean
SquarePackingArchive.Nagamochi.not_scoresDilatedSquares_four :
  ¬ SquarePackingArchive.NagamochiResource.ScoresDilatedSquares 4
```

Lean proves the upper bound `199/200`; the sharper exact total above is the
independent rational calculation, not an asserted Lean equality. The proof
depends only on `propext`, `Classical.choice`, and `Quot.sound`, as checked by
the repository's explicit axiom audit.

## Relation to the published proof

The weights and supports match Section 3 of
[Nagamochi's 2005 paper](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v12i1r37/pdf).
Its Lemma 1 asserts the corresponding score is greater than one for every
admissible square; Section 5 reduces the edge-strip cases to a pinned geometry.

The incidence distinction is visible before the small horizontal displacement:
`(2,0.9)` lies on the edge from the bottom vertex to the right vertex, but that
edge ends at height `λ·1599/1601 < 1`. It does not cross `y=1`. Contact with
an arbitrary edge therefore does not establish Lemma 6's hypothesis that the
contact edge is one of the two edges crossing that line.

This identifies a failed premise in the existing proof route. A corrected
resource argument, a packing-level argument, or an independent proof is needed
to formalize the general near-square theorem. The separately verified finite
packing minima remain verified by their own Lean proofs.
