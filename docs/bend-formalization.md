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

| Result                          | Bend                                                                         |
| ------------------------------- | ---------------------------------------------------------------------------- |
| `HasPacking 6 3`, so `s(6) ≤ 3` | `Laws.square6_has_packing_at_three` in [`bend/LAWS.bend`](../bend/LAWS.bend) |

The packing places six axis-aligned unit squares in a 3 by 2 grid.
`bend/Grid.bend` proves that a grid cell fits in side 3 and that cells whose
centres differ by at least 1 in one coordinate have disjoint interiors;
`scripts/generate-bend-square6.py` writes the case analysis over the 36 ordered
index pairs in `bend/Square6.bend`.

Run the check with Bend at the pinned revision and Lean 4.34.0:

```console
git submodule update --init
bun /path/to/bend/bend2/main.ts bend/PROOF.bend --verdict
```

## Plan for the remaining proofs

The Lean proof of `s(6) = 3` depends on about 8,400 lines. Measure theory
appears only for `side_positive`, and the upper bound is the grid above, so the
port is dominated by Stromquist's point-set argument. The order of work:

1. **Inequality certificates in `bend-math`.** The Lean geometry closes about
   50 goals with `nlinarith`. Each such goal is an ordered-field inequality with
   a Positivstellensatz certificate: a nonnegative combination of hypothesis
   products and squares equal to the goal. A Bend checker verifies the identity
   with `FieldRing.equal` and the nonnegativity term by term. A script extracts
   each goal from Lean and searches for an exact rational certificate.
2. **Constants and square roots.** Fractions such as `4/5` need an inverse for
   nonzero naturals in the interface. `FriedmanStrip.lean` and
   `StromquistSixPoints.lean` use `Real.sqrt`; where it cannot be eliminated,
   the interface gains a square root of nonnegative elements, and the model
   moves from the rationals to a field with that root.
3. **Geometry layer in `bend/`.** Port `Geometry.lean` (local coordinates,
   containment, separation), the symmetries in `PackingSymmetry.lean`, the
   unavoidable-set framework in `Unavoidable.lean`, and the scaling to a
   closed-disjoint family in `PackingPointCapacity.lean`.
4. **Finite combinatorics.** The incidence and pigeonhole steps over the nine
   key points need counting lemmas over Bend lists or bounded naturals.
5. **Stromquist's argument.** Port the `StromquistSix*` files, then the final
   `IsMinimumSide 6 3`. Later records reuse layers 1 to 4.

Bend issues met along the way are tracked in
[`bend-math/docs/bend-issues.md`](https://github.com/chelokot/bend-math/blob/main/docs/bend-issues.md).
