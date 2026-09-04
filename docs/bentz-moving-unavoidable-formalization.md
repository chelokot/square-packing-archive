# Continuously moving unavoidable configurations

Primary source: Wolfram Bentz, [Optimal Packings of 22 and 33 Unit Squares in a
Square](https://arxiv.org/abs/1606.03746), submitted 12 June 2016, Theorem 8.

`SquarePackingArchive.moving_unavoidable_preserves_assignment` proves the
topological preservation theorem for arbitrary preconnected parameter spaces
and finite families of disjoint open boxes. The ambient space need not be the
Euclidean plane. Its hypotheses exactly expose the conditions used in the
paper: every box contains a point at every parameter, every point trajectory
is continuous, and initially uncovered or multiply assigned points remain
stationary.

The proof does not need to select a first exit time. The set of parameters
preserving all initial assignments is open by continuity and finiteness. Its
complement is also open: when a point leaves its box, unavoidability supplies
a replacement point. The stationarity conditions imply that the replacement
initially belonged to a different box. Its presence in the new open box then
gives a neighborhood on which its old assignment remains violated.
Preconnectedness and the initial parameter force all assignments to persist.

This completes Theorem 8, not the packing results for 22 or 33 squares.
Their full proofs still require explicit continuous point configurations,
unavoidability throughout each movement, and the final line-intersection
resource contradiction. Neither historical exact claim is promoted by this
intermediate theorem.
