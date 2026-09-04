# Search for 62 squares below side 8

This experiment searches for 62 non-overlapping unit squares in a square of side
7.9999. A successful local minimization is not a counterexample: the exported
coordinates must also pass the exact rational checker. This checker is Python,
not Lean; even a passing result would still need a Lean certificate before being
added to the verified archive.

Run with Python 3, NumPy 2.4.2 and SciPy 1.18.0 (pinned in `requirements.txt`):

```sh
cd experiments/near-square-search
python3 -m unittest -v
OPENBLAS_NUM_THREADS=1 python3 search.py --seeds 12 --seconds-per-seed 15 --output results-7.9999.jsonl
OPENBLAS_NUM_THREADS=1 python3 search.py --seeds 12 --seconds-per-seed 15 --side 7.999999 --output results-7.999999.jsonl
python3 check_results.py results-7.9999.jsonl
python3 check_results.py results-7.999999.jsonl
```

The saved-candidate checker and its geometry tests need no NumPy or SciPy:

```sh
python3 -S -m unittest -v test_exact_geometry test_row_compensation
python3 -S check_results.py results-7.9999.jsonl
python3 -S check_results.py results-7.999999.jsonl
```

The optimizer minimizes squared boundary and pairwise overlap violations. Each
pair uses all four separating axes of the two rotated squares. Analytic
derivatives are tested against finite differences away from nondifferentiable
points. Boundary contacts and edge contacts are allowed; overlapping interiors
are not. The search is local and nonsmooth; failure says nothing about whether a
counterexample exists.

Seeds start from an 8-by-8 grid with two positions removed. Four hole patterns
are used. Six seed modes cycle through small random angles, all-boundary tilts
of approximately 2.86 degrees (the Nagamochi motif), alternating row tilts of
0.15 radians, checkerboard tilts of 0.3 radians, random tilts up to 0.3 radians,
and random positions with random angles. Centers and angles are then all free
to move. These seeds explore a tilt motif, not a claim that copies of the
counterexample fit together.

Each JSON output line includes the seed, stopping reason, runtime, maximum
constraint violation, and the full rational candidate. Rational rotations use
the half-angle parameter `t`: cosine is `(1-t²)/(1+t²)` and sine is
`2t/(1+t²)`. This makes unit edge lengths exact, without rounded trigonometric
values. The independent checker constructs all vertices with `Fraction`, checks
containment, and tests separating axes exactly. It deliberately has no numerical
tolerance. The search never reports a packing based on the optimizer's success
flag alone.

The optimizer targets a clearance of `1e-8` between squares and from the walls,
to leave room for rationalization. Results distinguish violations of this
requested clearance from violations of the actual unit-square constraints. The
exact checker still uses the original unit squares and allows contact; the
clearance is not a tolerance for accepting overlaps.

## Results, 2026-09-05

No counterexample was found. All 24 candidates failed the exact checker.

| Container side | Starts | Total search and checking time | Best loss   | Actual maximum violation in that candidate |
| -------------- | ------ | ------------------------------ | ----------- | ------------------------------------------ |
| 7.9999         | 12     | 50.944 seconds                 | 1.84934e-8  | 1.99203e-5                                 |
| 7.999999       | 12     | 43.214 seconds                 | 2.15369e-12 | 1.85110e-7                                 |

“Best” means the smallest sum of squared clearance violations, not a feasible
packing. The loss can become very small while squares still overlap or cross
the walls. That is what happened here.

For side 7.9999, the best candidate was seed 9 (initial checkerboard tilts).
Its largest remaining tilt from an axis was 0.000468 radians; the median was
0.00000586 radians. For side 7.999999, the best was seed 1 (boundary motif),
with largest and median remaining tilts both about 0.0000000828 radians.
Both searches returned almost to the grid. Random-position seeds retained
larger tilts but also substantial overlaps: their maximum violations ranged
from 0.154 to 0.254.

This is a failed local search, not evidence of a global lower bound. The files
retain every candidate so these results can be checked without rerunning the
optimizer. The recorded runs used Python 3.13.13, single-threaded OpenBLAS, and
at most 15 seconds per seed; most stopped earlier on the optimizer's stopping
criteria or evaluation limit. Timing and floating-point trajectories can vary
between machines.

## An exact row experiment

One low-scoring square does not mean its neighbors can also score below one.
Here is a specific arrangement where they do not.

`row_compensation.py` imports the original counterexample's exact coordinates
from `scripts/check-nagamochi-counterexample.py`, without changing that module's
constants. It places six copies along the bottom of an 8-by-8 container. Each
copy has side `10001/10000`; the horizontal step is its side divided by its
sine, exactly `16011601/15990000`. The squares touch without overlapping
interiors. All six fit; a seventh copy would cross the right wall.

Their scores, using the 8-by-8 container's resource markings, are:

| Square from the left | Score, rounded | Covered point resources    |
| -------------------- | -------------- | -------------------------- |
| 1                    | 0.977543419678 | Q at (1, 0.9)              |
| 2                    | 1.513043419678 | P at (2, 0.9) and (3, 0.9) |
| 3                    | 1.013043419678 | P at (4, 0.9)              |
| 4                    | 1.013043419678 | P at (5, 0.9)              |
| 5                    | 1.013043419678 | P at (6, 0.9)              |
| 6                    | 1.012758932911 | Q at (7, 0.9)              |

The total is exactly `133822474074449677/20454408000000000`, or about
`6.542476031301`: more than six. In this row, the second square alone collects
enough extra score to cover the first square's shortfall.

```sh
python3 row_compensation.py
python3 -m unittest -v test_row_compensation
```

These checks need only the Python standard library. They verify containment,
pairwise separation, clipped area, resource-segment lengths, and point
membership with exact fractions. The tests also recover the original 4-by-4
score and reject an overlapping row with a slightly shorter step.

This calculation is not a Lean proof and does not establish a compensation
rule for other arrangements. It shows why repeating this particular
counterexample along an edge does not repeat its score deficit.
