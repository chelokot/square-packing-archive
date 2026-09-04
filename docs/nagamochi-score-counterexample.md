# Counterexample to Nagamochi’s Lemma 1

Lemma 1 in [Nagamochi’s 2005 paper](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v12i1r37/pdf)
states that every admissible square has resource score greater than one.
The square below has score less than one. Lean proves the bound
`σ(S) ≤ 199/200 < 1`.

This refutes the score lemma, **not** the packing theorem `s(n²−2)=n`.

[![The square in a 4-by-4 container, its contributing resources, a magnified view of the excluded point P, and the score calculation.](assets/nagamochi-counterexample.png)](assets/nagamochi-counterexample.svg)

[Open the vector diagram](assets/nagamochi-counterexample.svg) ·
[Download the PNG](assets/nagamochi-counterexample.png)

Circles are `Q` points; diamonds are `P` points. A filled point is inside the
square. Purple shows the counted area; gold shows the counted chord lengths.
The inset uses the same scale on both axes, magnified enough to show the
horizontal gap of `1/10000` between the square and `P=(2,0.9)`.

## The square

The container is `[0,4]²`. Set

```text
λ = 10001/10000
c = 80/1601
s = 1599/1601
A = (10419467/5330000, 0).
```

Since `c²+s²=1`, these four vertices form a square of side `λ`:

```text
A
A + λ(c, s)
A + λ(c−s, s+c)
A + λ(−s, c).
```

The closed square fits in the container. Only `Q=(1,9/10)` is inside it.
No `P` point is inside, and no `Q` or `P` point lies on its boundary.

## The score

Using the weights and supports from Section 3 of the paper:

| Resource                        | Contribution to the score       |
| ------------------------------- | ------------------------------- |
| Area inside `[1,3]²`            | `611022059041 / 25584000000000` |
| Bottom chord, weighted by `1/2` | `1251468079 / 2558400000`       |
| Left chord, weighted by `1/2`   | `29/2000`                       |
| The point `Q=(1,9/10)`          | `9/20`                          |
| All other resources             | `0`                             |

Thus

```text
σ(S) = 25009470849041 / 25584000000000
     = 0.977543419677962789… < 1.
```

## Check it

[The Python checker](../scripts/check-nagamochi-counterexample.py) computes that
exact score using rational arithmetic. It also generates the diagram from the
same coordinates.

```console
python3 scripts/check-nagamochi-counterexample.py --check-figure
```

To regenerate the SVG and PNG, install `matplotlib` and run the checker with
`--figure`. Drawing uses rounded coordinates; every mathematical check uses
exact fractions.

[The Lean proof](../formal/SquarePackingArchive/NagamochiCounterexample.lean)
checks containment of both the closed dilated square in `[0,4]²` and the
closed unit square in a container of side `4/λ`. It proves a sufficient
upper bound rather than the exact score:

```text
σ(S) ≤ 3/100 + (1/2)(1 + 3/100) + 9/20
     = 199/200 < 1.
```

The final theorem is `SquarePackingArchive.Nagamochi.not_scoresDilatedSquares_four`.
Its only axioms are Lean’s standard `propext`, `Classical.choice`, and
`Quot.sound`. The exact score above comes from Python; the upper bound comes
from Lean.

## Where the argument fails

In Case 6, the paper moves a square until `(2,0.9)` touches an edge, then
applies Lemma 6. But Lemma 6 requires **that edge to cross `y=1`**.

Shift the square right by `1/10000`. Then `(2,0.9)` touches the edge from the
bottom vertex to the right vertex. That edge ends at height `λ·1599/1601 < 1`.
It does not cross `y=1`, so Lemma 6 does not apply.

The general packing theorem needs a repaired argument or a different proof.
This counterexample does not affect the archive’s independently verified
finite packing minima.
