# Bentz's staggered lattice

Primary source: Wolfram Bentz, [Optimal Packings of 13 and 46 Unit Squares in a
Square](https://doi.org/10.37236/398), 2010.

`SquarePackingArchive.Records.Square46.s46_eq_seven` proves
`IsMinimumSide 46 7`. The proof uses a rationalized variant of Bentz's
45-point lattice: the seven rows have heights
`451/500 + row × 433/500`. Even rows have six points at integer horizontal
coordinates from 1 to 6; odd rows have seven points at half-integer
coordinates from 1/2 to 13/2.

The row separation satisfies `(433/500)² + (1/2)² ≤ 1`, so a complete
triangulation of each band is covered by the existing triangle lemma. The
boundary-strip lemma applies because `451/500 ≤ √2 − 1/2`. Exact reflections
handle the opposite edge.

Virtual boundary and exterior vertices simplify the triangulation. They
are excluded using `PlacedSquare.StrictFits`, not assumed absent from an
arbitrary closed packing. The generic theorem
`lowerBound_succ_of_strict_unavoidable` proves the required reduction:
scaling centers from a smaller container places every unit square strictly
inside the larger container, and a covered point scales back into the
original square's interior. Finite pigeonhole then gives the lower bound.

The same lower bound, packing monotonicity, and a seven-by-seven grid give
`s47_eq_seven` and `s48_eq_seven`. These verify the numerical historical
claims, but are not formalizations of Nagamochi's general theorem or of
his original proofs for those two values. The archive preserves the
historical attribution and links the separate Lean evidence to this file.
