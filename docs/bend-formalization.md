# Bend formalization

The `bend/` directory restates the canonical problem in
[Bend 2](https://github.com/bendlang/bend) and proves results against it with
Bend's kernel, which is itself proved correct in Lean (`bend --verdict`). The
shared number theory lives in [`chelokot/bend-math`](https://github.com/chelokot/bend-math),
pinned as the `bend/bend-math` submodule.

## What a Bend result means

Bend has no type of classical real numbers, and its constructive reals cannot
decide comparisons. Every Bend theorem here is therefore stated for **every
ordered field** satisfying `bend-math/Field.bend`. The real numbers are such a
field, so each theorem holds for them in particular. That last step is
ordinary mathematics and is not checked by Bend.

The interface writes equality as `a ≤ b` and `b ≤ a`, and states every axiom
through the order. This keeps the axioms satisfiable by the one-element
structure, which the kernel requires before it accepts a generic proof, and by
the rationals, which `bend-math/RationalField.bend` proves. The field also
provides `half` with `half + half = 1`.

## Correspondence with `Problem.lean`

| Lean                                                       | Bend (`bend/Problem.bend`)                                                            |
| ---------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| `Point`                                                    | `Problem.Point`                                                                       |
| `Frame` with `cosine ^ 2 + sine ^ 2 = 1`                   | `Problem.Frame`, the equation as two inequalities                                     |
| `PlacedSquare.point`: `center + (x·c − y·s, x·s + y·c)`    | the same expression inside `Containment`                                              |
| `Contains`: `∃ x y, abs x ≤ 1/2 ∧ abs y ≤ 1/2 ∧ point = …` | `Containment`: witnesses, `−half ≤ x ≤ half`, and both coordinates equal              |
| `InteriorContains`: strict bounds                          | `InteriorContainment`: `half ≤ x` and `x ≤ −half` are impossible                      |
| `Container.Contains`                                       | `InContainer`                                                                         |
| `Packing n side` over `Fin n`                              | `Packing` over indices `i` with `i + 1 ≤ n`; distinct indices have disjoint interiors |

## Checked results

Each catalog claim with a Bend proof is a law of `bend/MANIFEST.bend`, which
`scripts/generate-bend-manifest.py` writes from `archive/manifest.json`: an
upper bound `s(n) ≤ v` is the law `<claim>_upper`, a packing of `n` squares in
side `v`, and a lower bound `v ≤ s(n)` is the law `<claim>_lower`, `v ≤ side`
for every packing of at least `n` squares. `bend/PROOF.bend` proves each law, so
`--verdict` checks every claim exactly as the catalog states it.

| Claims                   | Proofs in `bend/PROOF.bend`                     |
| ------------------------ | ----------------------------------------------- |
| `s(1) = 1`               | `Grids.packing` and `Small.lower_bound_one`     |
| `s(2) = s(3) = s(4) = 2` | `Grids.packing` and `Small.lower_bound_two`     |
| `s(6) = 3`               | `Grids.packing` and `StromquistSix.lower_bound` |
| `s(7) = s(8) = s(9) = 3` | `Grids.packing` and `StromquistSix.lower_bound` |

`bend/LAWS.bend` keeps the general laws: the local coordinates of a square
(`Laws.contains_iff_local_coordinates_forward` and `_backward`, and the same
for the open square), the symmetries of packings, `Laws.fewer_squares`, and
the scaling to a closed-disjoint family.

The upper bounds, and the basic grid bound `s(n) ≤ ⌈√n⌉` the site shows for
counts without a catalogued claim, are one theorem: `bend/Grids.bend` packs
any `n ≤ k²` axis-aligned unit squares in side `k`, column by column. Square
`i` sits in the cell whose column is the quotient and whose row is the
remainder of `i` by `k`, built by `Grids.place` with the proof that
`quotient · k + remainder = i`. `bend/Grid.bend` proves that a cell fits in side
`k` and that cells whose positions differ by at least 1 in one coordinate have
disjoint interiors; two different indices differ in their remainder or, with
equal remainders, in their quotient.

`bend/Small.bend` proves the lower bounds for one and two squares, following
`NearSquare.lean`'s two-square argument: the corners of a square in first-quadrant normal form are
`cosine + sine ≥ 1` apart, and a square that fits `[0, 2]^2` contains `(1, 1)`,
so two squares in side less than 2, scaled to closed-disjoint squares in
`[0, 2]^2`, would share that point.

Run the check with Bend at the pinned revision and Lean 4.34.0:

```console
git submodule update --init
bun /path/to/bend/bend2/main.ts bend/PROOF.bend --verdict
```

## The lower bound

`bend/StromquistSix.bend` ports Stromquist's argument from the
`StromquistSix*` Lean files. The law takes a packing of any `count ≥ 6`
squares: the kernel checks a generic proof only when each `~` parameter has a
model, and a packing has one when `count` is a parameter (at zero squares) but
not at a fixed six. Its first six squares give the theorem for six.

A packing of side less than 3 scales to six
squares that fit `[0, 3]^2` with pairwise disjoint closed squares
(`bend/Scaling.bend`). Each square is moved into first-quadrant normal form by
the symmetries of the container (`bend/Symmetry.bend`), and its incidences with
the nine key points `{1, 3/2, 2}^2` and the extra points of the centre
patterns become Booleans decided by the field order (`bend/Membership.bend`).

The geometric facts about one square are stated in normal form and proved by
inequality certificates: it holds a key point (`bend/Unavoidable.bend`, the
perimeter and unavoidable triangles of `Unavoidable.lean`), the pairs it can
hold, the centre patterns and their extra points (`bend/Stromquist.bend`), and
the boundary points shared by two squares holding adjacent single key points
(`bend/Singletons.bend`). Disjointness turns them into constraints on the 54
incidence bits, and `bend/Incidence.bend` shows by a Boolean case analysis
that no six rows satisfy them.

The certificates are found by `bend-math/tools/certificate.py` and stored in
`scripts/bend-certificates.json`, so the generators rewrite every `.bend`
file without a solver:

```console
for generator in scripts/generate-bend-*.py; do python3 "$generator"; done
```

Square roots do not appear: where the Lean proof bounded `cosine + sine` by
`√2`, the Bend proof uses the rational bound `17/12`.

Bend issues met along the way are tracked in
[`bend-math/docs/bend-issues.md`](https://github.com/chelokot/bend-math/blob/main/docs/bend-issues.md).
