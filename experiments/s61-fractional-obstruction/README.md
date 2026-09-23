# Proposed computer-assisted proof that s(61) = 8

This is an independently checkable proof proposal, not a Lean-checked archive
claim. It is intentionally kept in `experiments/`: it does not alter the
manifest, the coverage matrix, or the published status of `s(61)`. The upper
bound is the 8-by-8 grid with three squares omitted. The proposed lower bound
follows from the finite certificate in `s61-certificate.txt`, the metadata
checker in `verify_s61_metadata.py`, and the integer-arithmetic verifier in
`verify_interval.rs`. Independent review of the reduction and verifier is
welcome before promoting this to a catalog result.

The prior published lower bound is about 7.8906, from Bašić and Slivková,
[On optimal piercing of a square](https://doi.org/10.1016/j.dam.2018.03.048)
(2018, Theorem 10). Bentz proved the analogous `s(m²−3)=m` cases for `m=5,6`
in [Optimal Packings of 22 and 33 Unit Squares in a Square](https://arxiv.org/abs/1606.03746).
Neither result gives `s(61)=8`.

In plain language, the certificate places weighted dots in the 8-by-8
container. Every unit square, however positioned or rotated, must cover dots
with combined weight at least one, while all dots together weigh less than 61.
This is a _fractional_ version of the unavoidable-points method. A packing in a
smaller container could be enlarged to fit the 8-by-8 container. Each enlarged
square has room for a unit-sized core strictly inside it, so those 61 closed
cores are disjoint and cannot count any dot twice. They would require at least
61 total weight, contradicting the strict mass deficit.

## Weighted obstruction

The certificate gives a nonnegative atomic measure `μ` in `[0,8]²` with 5,344 atoms. Atom coordinates are multiples of `1/16`, atom weights are integer multiples of `10⁻⁹`, and its exact mass is

    μ([0,8]²) = 60,990,002,548 / 1,000,000,000 = 60.990002548 < 61.

The exhaustive check establishes `μ(Q) ≥ 1` for every closed unit square `Q` contained in `[0,8]²`, at every orientation. If 61 unit squares fitted in a square of side `L < 8`, scale the packing by `8/L > 1`. The concentric closed unit-square cores of the enlarged squares would be pairwise disjoint, because each core lies strictly inside its enlarged square. Their total `μ`-mass would be at least 61 and at most `μ([0,8]²) < 61`, a contradiction.

## Finite orientation reduction

The weights have exact dihedral symmetry. Rotate or reflect any candidate square so that its center has both coordinates at least 4 and its angle lies in `[0,π/4]`. An atom with either grid coordinate below 53 cannot be in such a square: its corresponding coordinate is at most `52/16 = 3.25 < 4 − √2/2`. Only 2,118 atoms remain relevant. Their grid-coordinate differences have absolute value at most 67; the event generator conservatively uses 74.

Put `t = tan(θ/2)`, `d = 1+t²`, `c = 1−t²`, and `s = 2t`. Atoms capture a square center in rectangles bounded by transformed atom coordinates plus or minus half a unit. An ordering change between two horizontal or vertical atom boundaries must satisfy

    a cos θ + b sin θ = z,
    |a|, |b| ≤ 74,    z ∈ {−16, 0, 16}.

After multiplying by `d`, this is the integer quadratic

    (−a−z)t² + 2bt + (a−z) = 0.

`exact_orientation_samples.py` enumerates and exactly deduplicates the roots in `(0, √2−1)` using integer discriminants and rational isolating intervals. It finds 6,870 interior events, hence 6,871 open orientation cells. The rational sample and outward-rounded sine/cosine bounds for every cell are stored in the certificate. `verify_s61_metadata.py` recomputes them and checks exact mass, atom uniqueness, positivity, coordinate range, and dihedral symmetry.

For clarity, write a square center as `(X/16,Y/16)` and an atom as
`(i/16,j/16)`. Let `c=cos θ`, `s=sin θ`, `w=c+s`, and transform the center to
`u=cX+sY`, `v=−sX+cY`. The atom lies in the closed unit square exactly when

    ci+sj−8 ≤ u ≤ ci+sj+8,
    −si+cj−8 ≤ v ≤ −si+cj+8.

Thus each atom contributes its weight on a rectangle in `(u,v)` space. For a
contained square whose center is in the upper-right quadrant, the feasible
center conditions are `64 ≤ X,Y ≤ 128−8w`. A subthreshold position rectangle
`(uL,uR)×(vB,vT)` is safely outside this region if any of these eight
separations holds:

    uR ≤ 64w                         uL ≥ (128−8w)w
    vT ≤ −s(128−8w)+64c             vB ≥ −64s+c(128−8w)
    c·uR−s·vB ≤ 64                  c·uL−s·vT ≥ 128−8w
    s·uR+c·vT ≤ 64                  s·uL+c·vB ≥ 128−8w.

The verifier proves at least one separation for every low-weight run over its
entire orientation cell, using either outward interval bounds or an exact
positive polynomial in `t`. This is the finite replacement for checking every
real-valued position and angle separately.
The `±256` sentinel edges in the verifier enclose all feasible transformed
centers and all retained atom-capture boundaries throughout the angle range.

## Coverage audit

At one exact rational angle in each orientation cell, `verify_interval.rs` constructs the complete atom-boundary arrangement using integers. It sweeps every open rectangular position cell and merges consecutive cells of weight below 1 into horizontal runs. The atom-boundary ordering, and therefore each cell's captured atom set and weight, is constant throughout that orientation cell.

For each subthreshold run, the verifier proves that its moving rectangle stays outside the feasible-center square throughout the orientation cell. It first tries outward integer bounds on the rectangle and the feasible-center region along their four pairs of separating axes. If those bounds overlap, it forms the exact separator polynomial in `t`, of degree at most four, and proves it strictly positive by outward-rounded integer interval Horner evaluation. A zero factor `t` may be removed because the audited orientation cells have `t > 0`. All arithmetic is integer arithmetic; the recommended build enables overflow traps.

The audit reports `failures=0 total_runs=78014122` across all 6,871 cells.
Every generic contained closed square therefore has mass at least 1. Event
angles, atom-boundary positions, and the two orientation endpoints follow by
limits: for a finite atomic measure, the captured mass of a closed square at a
limiting placement is at least the limit superior of captured masses at nearby
placements. Thus every contained closed unit square has mass at least 1.

The LP search that found the weights is not trusted by this argument; the
integer certificate is the result being checked. Python regenerates the event
metadata, and Rust checks the claimed geometric coverage. This does not prove
`s(m²−3)=m` for all `m`, and it does not meet the archive's Lean-kernel policy
for catalog claims.

## Reproduction

Run from this directory:

```sh
python3 -S verify_s61_metadata.py s61-certificate.txt
rustc --edition 2021 --test -C overflow-checks=yes verify_interval.rs -o /tmp/verify_s61_tests
/tmp/verify_s61_tests
rustc --edition 2021 -C opt-level=3 -C overflow-checks=yes verify_interval.rs -o /tmp/verify_s61
/tmp/verify_s61 cells < s61-certificate.txt
```

The certificate SHA-256 is `33ae71eb6012e4d9570b14c1447a0c3127527f54e41f785bdd5d6c4dfe69ea65`. The exhaustive verifier should end with `failures=0`.
