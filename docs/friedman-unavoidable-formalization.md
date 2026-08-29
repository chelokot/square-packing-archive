# Friedman unavoidable-point formalization

The formal layer models both forms of an unavoidable-point argument. A closed
unavoidable set pierces every unit square in the target container. Scaling the
container and point set proves that the corresponding points lie in square
interiors at every strictly smaller side length. A finite pigeonhole theorem
then bounds a packing by the number of piercing points.

Lean checks this reduction in `SquarePackingArchive.Unavoidable`, including the
strict inequalities introduced by scaling. No discretization or numerical
tolerance is involved.

The geometric layer now covers the three ingredients used by Friedman's proof
of `s(5)`. The corner lemma normalizes arbitrary frame signs by quarter
rotations and checks inverse frame coordinates algebraically. The side-strip
lemma excludes every way both adjacent piercing points could lie outside a
rotated square. The triangle lemma checks the 27 possible combinations of
three vertices escaping through the four local sides.

The corner and side-strip lemmas are parameterized rather than tied to the
four-point example. A corner target may have any coordinates at most one. A
side strip carries its row origin, height, gap, and a frame inequality that
can be discharged exactly for the rational grids used by later historical
claims. This shared interface is intended for the `s(8)`, `s(15)`, `s(24)`,
and `s(35)` unavoidable configurations.

Lean partitions the container center region into four corners, four side
strips, and two central triangles. The four points at the corners of the
central square are therefore unavoidable. Scaling and finite pigeonhole give
the matching lower bound for five squares. Together with the separately
verified Göbel construction, this proves
`IsMinimumSide 5 (2 + Real.sqrt 2 / 2)` without numerical tolerances.
