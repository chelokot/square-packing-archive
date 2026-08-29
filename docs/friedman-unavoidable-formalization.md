# Friedman unavoidable-point formalization

The formal layer models both forms of an unavoidable-point argument. A closed
unavoidable set pierces every unit square in the target container. Scaling the
container and point set proves that the corresponding points lie in square
interiors at every strictly smaller side length. A finite pigeonhole theorem
then bounds a packing by the number of piercing points.

Lean checks this reduction in `SquarePackingArchive.Unavoidable`, including the
strict inequalities introduced by scaling. No discretization or numerical
tolerance is involved.

The first geometric lemma from Friedman's survey is also connected. A unit
square contained in the first quadrant whose center lies in the unit corner
region contains the point `(1, 1)`. The proof normalizes arbitrary frame signs
by quarter rotations, derives center bounds from container containment, and
checks the inverse frame coordinates algebraically.

For `s(5)`, the exact Göbel construction is verified separately. Completing
the exact result still requires formal versions of the survey's side-strip and
triangle lemmas and the exhaustive partition of the container center region.
The manifest therefore exposes the construction as a verified upper bound but
does not yet mark the historical exact claim as Lean-verified.
