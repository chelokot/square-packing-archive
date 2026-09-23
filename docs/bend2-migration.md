# Bend2 migration boundary

This branch is an investigation into replacing Lean with Bend2. It does not
claim that any existing result has been re-proved in Bend2.

The result to preserve is the exact `IsMinimumSide n x` proposition in the
[source branch's `Problem.lean`](https://github.com/chelokot/square-packing-archive/blob/c35d6a0/formal/SquarePackingArchive/Problem.lean): for every
nonnegative real side length, every placement of `n` unit squares with
arbitrary real centers and rotations, the interiors are disjoint and all
squares fit in the container. An exact result needs both a construction at
side `x` and a proof that no smaller real side works.

A replacement must supply a Bend2 definition with the same quantifiers and
geometry, prove every catalog claim against that definition, and make the
archive reject any claim whose Bend2 proof is absent or has an unproved law.
The rational and quadratic coordinate checks are useful inputs but do not
replace the universal lower-bound theorems. Checking the S61 integer
certificate also does not, by itself, formalize the reduction from all real
placements to its finite list of cells.

The current Bend2 base has `Nat`, `U32`, and `F32`, but no exact real-number
type. The [Bend2 limitations](https://github.com/bendlang/bend#limitations)
say that `F32` is axiomatic and that its properties cannot be proved. A
floating-point restatement would therefore be a different, weaker problem.
An exact migration needs a formally justified real-number construction or
another formally justified semantics for the relevant real algebra and order,
plus the geometry and arithmetic library used by the existing proofs.

Until that foundation and all theorem translations pass a Bend2 proof gate,
deleting the Lean proofs would remove the archive's present verification
evidence. No existing green status should be relabeled as Bend2-checked merely
because an executable verifier reports success.
