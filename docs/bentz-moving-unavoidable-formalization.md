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

This topological theorem alone does not prove a packing bound. The archive now
also contains the complete argument for **s(33) = 6**, checked on 2026-09-05:
`SquarePackingArchive.Records.Square33.s33_eq_six : IsMinimumSide 33 6`.

The proof starts with 33 unavoidable points in six staggered rows. Each square
has exactly one assigned point. Continuous vertical compression preserves these
assignments, and a small horizontal shift makes each odd row's leftmost point
reach x = 2/5. A separate endpoint-replacement argument and a reflected copy of
the configuration identify six distinct squares that reach this strip.

Each such unit square has a vertical chord of length at least one on the fixed
line x = 451/500. Their interiors are disjoint, so the six chord lengths cannot
fit in a container of side less than six. The ordinary 6×6 grid with three
squares removed supplies the matching upper bound.

The finite row heights are exact rationals. The endpoint argument is a direct
geometric replacement proof; it does not assume that the whole row can be
shifted arbitrarily. The final theorem has no unproved geometric hypotheses.
Its axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`.

The main modules are `BentzSixRows.lean`, `BentzSixRowsShift.lean`,
`BentzSixRowsEndpoint.lean`, `BentzSixRowsCombine.lean`, and `BentzLineCuts.lean`.

## The 22-square proof

The full theorem **s(22) = 5** is also checked on 2026-09-05:
`SquarePackingArchive.Records.Square22.s22_eq_five : IsMinimumSide 22 5`.

This case uses two staggered configurations: 22 red points and 23 blue points
in five rows. The extra blue point means some points may be uncovered or share
a square. A counting argument puts all such points in one square, unless just
one point is uncovered. A reflection makes the leftmost blue points uniquely
assigned; at most one of the three blue rows can obstruct horizontal motion.

Endpoint replacements identify five distinct squares, one per row. Four reach
the narrow left strip and therefore have unit-length chords on x = 451/500.
For the remaining square, these four chords exclude specific points on that
line. Exact distance inequalities then force a fifth unit chord. Five disjoint
unit chords cannot fit in a container of side less than five. A 5×5 grid with
three squares removed gives the matching upper bound.

The formal argument may first enlarge a hypothetical container to a side of
at least 4.999, still below five. This preserves the packing and supplies the
rational margins used in the distance estimates. Both final theorems cover
arbitrary rotations and allow squares to touch. Neither assumes any unproved
geometric lemma.

The 22-square modules are `BentzFiveRows.lean`, `BentzFiveRowsMotion.lean`,
`BentzFiveRowsReflection.lean`, `BentzFiveRowsEndpoint.lean`,
`BentzFiveRowsWitnesses.lean`, and `BentzFiveRowsContradiction.lean`.
