# What does `s(n) = x` mean?

The single canonical Lean statement is
[`IsMinimumSide n x`](../formal/SquarePackingArchive/Problem.lean). That file
contains the complete domain-specific definitions needed to review the claim:

1. A placed unit square has a center and an orthonormal frame. Local
   coordinates between `−1/2` and `1/2` in both directions form the closed
   square; strict inequalities form its interior. Every rotation is allowed.
2. The container is the closed, axis-aligned square `[0, x] × [0, x]`.
3. A packing assigns one placed square to each index in `Fin n`. Every square
   fits the container, and distinct squares have disjoint interiors. Touching
   along edges or at points is allowed.
4. `IsMinimumSide n x` says a packing exists at side `x`, and every side that
   admits such a packing is at least `x`.

In ordinary notation, this is exactly

```text
s(n) = x  ⇔  packing(n, x) exists and
             for every L, packing(n, L) exists only if x ≤ L.
```

The theorem is a proposition, not a decimal approximation or an optimizer
output. The archive checks the exact Lean theorem type against each manifest
claim. Green means an exact claim has linked Lean evidence for
`IsMinimumSide n x`; the generated manifest audit checks the theorem at that
count and exact value. CI rejects `sorry`, custom axioms, and unchecked native
oracles. The site then links the theorem itself.

This file concentrates the **problem-specific** trust boundary. As with any
Lean formalization, one must still trust the Lean kernel, the imported real
number foundations, and the build that connects the checked theorem to the
published site. A computer-checked certificate outside Lean is not yet a green
cell, even if its mathematical argument appears sound.
