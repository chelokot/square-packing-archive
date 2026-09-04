# Failed local compensation rules

These are exact counterexamples to four proposed ways of repairing Nagamochi's
individual-square score lemma. They are **not** counterexamples to the packing
theorem. None of these new pair calculations is a Lean proof.

Run with the Python standard library only:

```console
cd experiments/boundary-compensation
python3 -S verify.py
python3 -S -m unittest -v
```

The checker reuses the archive's rational square and separation checker,
polygon clipping, polygon area, and resource markings. Every reported score,
point membership, wall constraint, and non-overlap check uses `Fraction`.
The generic scorer also reproduces the existing six-square row exactly.

## A neighboring Q point does not guarantee compensation

Take the original low-scoring square and translate a same-orientation copy so
that its center coordinates are swapped. These squares are disjoint and cover
the two Q points `(1,0.9)` and `(0.9,1)`. Their total score is about `1.9911013`,
less than two. The neighboring Q-point owner need not repay the deficit.

## A neighboring P point need not force the next P point

Shift the original square left by `1/500`. It still scores below one. Translate
a second copy right by `λ/s`, where `λ=10001/10000` and `s=1599/1601`.
The copies meet along an edge without interior overlap.

The second copy contains `(2,0.9)` but not `(3,0.9)`. In this example the pair
does score above two, but the proposed forced-extra-point rule is false.

## A neighboring P-point owner need not repay the deficit

Use a square with bottom vertex `A`, side `λ`, and orthonormal edge directions
`(c,s)` and `(-s,c)`:

```text
λ = 1000001/1000000
c = 200/10001
s = 9999/10001
A = (990799/499950, 0)
```

Its vertices are `A`, `A+λ(c,s)`, `A+λ(c−s,s+c)`, and `A+λ(-s,c)`.
Let the second square be its translation by `(λ/s,0)`, where
`λ/s = 99019901/99000000`. Both fit in `[0,8]²` and have disjoint interiors.

The first contains Q `(1,0.9)`. The second contains P `(2,0.9)` but not
P `(3,0.9)`. Their scores are

```text
first  = 38214099199069501 / 39600000000000000 = 0.965002505027…
second = 39795129100069501 / 39600000000000000 = 1.004927502527…
sum    = 39004614149569501 / 19800000000000000 = 1.969930007554… < 2.
```

A third copy at the same spacing contains both P `(3,0.9)` and P `(4,0.9)`;
the three-square total exceeds three. That is a fact about this particular
row, not a general compensation theorem for neighboring squares.

## A missing upper point does not force a neighboring vertical crossing

A square containing `(1,0.9)` but missing `(1,1)` need not intersect either
vertical segment from `(0,0.9)` to `(0,1)` or from `(2,0.9)` to `(2,1)`.
The checker includes an exact example with side `10001/10000`, rotation
cosine `119/169`, rotation sine `-120/169`, and center

```text
(1 + (43/100)(119/169) + (4/25)(120/169),
 9/10 - (43/100)(120/169) + (4/25)(119/169)).
```

It fits the container and has score greater than one. Thus a proposed boundary
chain cannot use the missing upper point alone to force its next crossing;
it needs an additional geometric or score condition.
