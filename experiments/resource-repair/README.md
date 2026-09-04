# Attempts to repair the resource measure

These experiments rule out three simple repairs. They do not prove the packing
theorem, and they do not produce a packing counterexample.

The exact checks use only Python's standard library:

```sh
cd experiments/resource-repair
python3 -S verify_repairs.py
python3 -S -m unittest -v test_repairs
```

`measure.py` reuses the canonical counterexample's polygon-clipping functions.
It computes covered area, segment fractions, and point membership. All verified
witnesses use rational coordinates and squares of side `10001/10000` inside a
4-by-4 container. Exact checks allow boundary contact, but point resources count
only when they lie in a square's interior.

## Raising Q weights and trimming the lines

Raising each Q weight from 0.45 to 0.5 costs 0.4 in total. Trimming the four
resource lines to `[1,3]` saves 0.4. The budget stays 14, and the original
counterexample's score increases.

But the axis-aligned square `[0.9001,1.9002] × [0,1.0001]` then scores only
`47512001/50000000 = 0.95024002`. It covers Q at `(1,0.9)`, no P points,
area `0.00009002`, and resource-line lengths `0.9002` and `0.0001`.

## Replacing the extensions with a diagonal

Keep the trimmed lines. At each corner, give both Q points weight `w`, then
distribute the remaining corner budget `1−2w` uniformly along the segment joining
them. This preserves total mass 14 for `0 ≤ w ≤ 1/2`.

Two axis-aligned squares give incompatible requirements:

| Square                         | Exact score           |
| ------------------------------ | --------------------- |
| `[0.9001,1.9002] × [0,1.0001]` | `1.44924002 − 0.998w` |
| `[0.9998,1.9999] × [0,1.0001]` | `0.50209999 + 0.996w` |

For both to score at least one, `w` would have to be at most
`22462001/49900000 ≈ 0.45014030` and at least
`16596667/33200000 ≈ 0.49989961`. No such weight exists. This rules out every
weight in this uniform-diagonal family, not just the values sampled numerically.

## Changing all weights on the original markings

Keep the paper's original area, lines, Q points, and P points. Let their weights
be `A`, `B`, `Q`, and `P`, respectively. The total mass in a 4-by-4 container is
`4A + 8.8B + 8Q + 4P`.

Four squares already make a budget of 14 impossible:

| Square                              | Covered area                  | Covered line length     | Q count | P count |
| ----------------------------------- | ----------------------------- | ----------------------- | ------- | ------- |
| Interior square centered at `(2,2)` | `100020001/100000000`         | 0                       | 0       | 0       |
| `[1.1,2.1001] × [0,1.0001]`         | `10001/100000000`             | `10001/10000`           | 0       | 1       |
| `[0,1.0001]²`                       | `1/100000000`                 | `1001/5000`             | 2       | 0       |
| Original rotated counterexample     | `611022059041/25584000000000` | `1288564879/1279200000` | 1       | 0       |

Multiplying their score requirements by explicit positive rational coefficients
and adding gives a necessary total mass of at least
`1636357243551479206/116074907399696959 ≈ 14.09742450`.
With area weight fixed at one, the lower bound is slightly larger:
`818060198173335527/58025847950000000 ≈ 14.09820325`.
The checker verifies the coefficients and all cancellations exactly.

The scalar implications are formalized in
[`NagamochiWeightObstruction.lean`](../../formal/SquarePackingArchive/NagamochiWeightObstruction.lean).
Those Lean theorems start from the numerical inequalities above. The geometric
calculations linking these four squares to those inequalities are checked in
Python, not yet formalized in that Lean module. These results concern the
specified symmetric weights and supports, not arbitrary resource measures.

## Repeating the numerical search

The optional search needs SciPy 1.18.0 and NumPy 2.4.2, as pinned in the adjacent
`near-square-search/requirements.txt`:

```sh
OPENBLAS_NUM_THREADS=1 python3 probe.py --seeds 4 --region bottom
OPENBLAS_NUM_THREADS=1 python3 probe.py --seeds 3 --region bottom --diagonal --corner-weight .45
```

It searches square angle and position, then reconstructs rational coordinates
with a rational half-angle rotation and checks the resulting score exactly.
Numerical failure to find a score below one does not validate a measure.
For example, an unrestricted run settled on interior squares and missed the
axis-aligned obstruction above; restricting the run to bottom-edge squares
found it immediately.
