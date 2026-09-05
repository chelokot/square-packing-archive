# Generated geometric covers

The 10- and 13-square proofs use finite point configurations. For each one,
Lean must check that every unit square fitting the container contains a listed
point. Triangle and boundary-strip lemmas handle individual regions; the
generated proofs check that these regions cover the container.

`scripts/generate-triangle-cover.py` divides the domain by straight lines and
produces ordinary Lean proofs. Coordinates and intersections use exact numbers
of the form `a + b√2`, with rational `a` and `b`. Floating-point area estimates
only choose which line to split on next.

Each leaf applies a geometric lemma already proved in Lean. Each half-plane
implication is justified by a nonnegative weighted combination of inequalities.
Lean checks the coefficients, signs, and algebraic identities. A mistake in the
Python generator cannot establish a false theorem: its output still has to pass
Lean's kernel.

The 10-square configurations are:

- `StromquistTenTriangleCover.lean`: the triangulated interior of step 3.
- `StromquistStepTwoCover.lean`: the complete step-2 configuration.
- `StromquistTenCover.lean`: the complete step-3 configuration.
- `StromquistStepFourCover.lean`: step 4, whose conclusion also allows a point
  on either of two specified segments.

Step 3 includes both rotated inner points, whose ownership is proved separately.
The lower-bound proof must establish that ownership; this coverage theorem alone
does not prove the packing optimum. Step 2 and step 4 have nonconvex interior
boundaries, so their proofs check the triangles and boundary regions together.

For 13 squares, `scripts/generate-nonadjacent-covers.py` produces 32 covers:
an initial and a final set for each of the 16 corner-point choices.
`scripts/generate-bentz-adjacent-covers.py` produces 13 covers: the initial
configuration, eight R1 cases, two R2 cases, R3, and R4. Initial covers allow
specified center rectangles, which the later counting and geometry handle.

Both generators use the same exact arithmetic and half-plane proof renderer.
They emit the point definitions and geometric certificates from the same data.
See the [13-square proof notes](bentz-13-formalization.md) for corrections to
the published point sets.

Run the arithmetic regression tests and check that all proof files match their
generator:

```sh
python3 -S -m unittest discover -s scripts -p 'test_triangle_cover.py'
python3 -S -m unittest discover -s scripts -p 'test_nonadjacent_cover.py'
python3 -S -m unittest discover -s scripts -p 'test_bentz_adjacent_cover.py'
python3 -S scripts/generate-triangle-cover.py --check
python3 -S scripts/generate-triangle-cover.py --step 2 --full --check
python3 -S scripts/generate-triangle-cover.py --step 3 --full --check
python3 -S scripts/generate-triangle-cover.py --step 4 --full --check
```

Use the same arguments with `--patch` instead of `--check` to generate an
`apply_patch` patch. CI checks reproducibility as well as compiling the proofs.
