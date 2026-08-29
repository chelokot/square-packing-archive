# Nagamochi 2005 formalization notes

The formalization follows Hiroshi Nagamochi's [Packing Unit Squares in a
Rectangle](https://doi.org/10.37236/1934). Lean checks the resource mass,
scaling and counting reduction, and the analytic inequalities used by the
geometric case split.

Two typographical corrections are required when translating the published
formulas literally:

- In Lemma 3, the displayed factorization of `f(√2 − 0.5, t)` is twice the
  preceding definition of `f`. The correct identity has a factor `1/2` on the
  factored right-hand side. This does not change its sign.
- In Lemma 6, the printed chord formula has numerator `t + t²`, but the next
  sentence uses `c = 1 − d` with `d = t(1 − t)/(1 + t)`. The consistent chord
  numerator is `1 + t²`. Lean proves the resulting identity `c + d = 1`.

The archive does not mark the near-square family as verified until the full
seven-case geometric score theorem is connected to these checked analytic
lemmas. Intermediate reductions are intentionally not treated as proof of the
historical claim.

The current Case 3 layer now includes exact formulas for both kinds of
opposite-edge horizontal chord, proofs that their open chords lie in the
dilated square, and the score consequences used in the paper. Two distinct
boundary-line chords of length at least the dilation factor have combined score
greater than one. A single such chord together with at least half of the
dilated square's area in the inner rectangle also has score greater than one.
The remaining work is the exhaustive geometric classification that derives
these measure hypotheses from the position of every admissible square, plus
the corresponding Case 2 and Cases 4–7 bridges.

For Case 2, the formal layer also contains the aggregate compensation theorem:
if the central-area score plus a stated loss covers the full dilated-square
area, and the boundary-line score covers that loss, then the total score is
greater than one. The remaining Case 2 obligation is geometric: construct the
finite family of cut-off triangles and derive those two inequalities from the
strict chord-versus-triangle lemma.

The discrete `Q` and `P` resources are represented by typed finite indices, so
their coordinates have a single formal definition. Lean proves that membership
of two distinct `Q` points contributes at least `0.9`, while membership of any
valid indexed `P` point contributes at least `0.5`. The Case 5 score arithmetic
is connected as well: positive inner-area score, two distinct `0.1` boundary
chords, and two distinct `Q` points imply total score greater than one. The
geometric premise is now connected too: every dilated square whose center lies
in one of the four corner regions contains the corresponding unit-corner and
two `Q` points, and therefore has score greater than one.

The final pinned subcase of Case 6 is now connected to the resource measure.
The corrected Lemma 6 expression is represented as an inner-area contribution
plus a combined boundary-line/`Q` contribution; the previously checked strict
real inequality lifts to an `ENNReal` score theorem once those two geometric
lower bounds are supplied. A general nonnegative real-component compositor is
used for this and the remaining subcases instead of repeating measure
arithmetic.

The inner-area premise of that pinned subcase is no longer an opaque numerical
bound. Lean computes the exact Lebesgue measure of a right triangle by Tonelli's
theorem and the fundamental theorem of calculus, transports the result from
`ℝ × ℝ` to the archive's `Fin 2 → ℝ` plane, and proves that translations preserve
the area. The pinned triangle's perpendicular edge lengths are `1 − t` and
`2t / (1 + t)`, so its area is `t(1 − t) / (1 + t)`, exactly the corrected
Lemma 6 term. Its open interior has the same area because the frontier of a convex set has zero
Lebesgue measure. The two legs are oriented by the square's orthonormal frame,
and Lean proves that this rotation and translation preserve volume. A typed
witness records convexity and openness of the dilated square, the three
frame-oriented triangle vertices in its closure, and those vertices in the
closed inner rectangle. Convexity then puts the complete open triangle in both
resource regions, even when a contact vertex lies on the square boundary, and
a kernel-checked bridge feeds the resulting `innerArea` bound directly into
the pinned score theorem.

That canonical placed-square certificate is now complete. Lean constructs the
square from a tangent-half-angle frame, pins its lower vertex to the container
bottom, and places `(2, 0.9)` on the required edge. It proves that the exact
horizontal cut of length `(1+t²)/(1+t)` and the vertical cut of length
`0.1-c′` lie in the open square, that `(1, 0.9)` contributes the corresponding
`Q` mass, and that the oriented cut triangle lies in both the square and the
closed inner rectangle. These three contributions compose to a kernel-checked
theorem that the canonical terminal square has resource score greater than
one. The remaining Case 7 obligation is therefore the deformation bridge:
derive the original square's score bound from each typed disconnected endpoint
outcome through a formal resource-preserving deformation or an equivalent
direct dominance lemma, including the appropriate container symmetries.

The formal model also constructs this cut directly at a square vertex. The
first endpoint has local coordinates `(t − 1/2, 1/2)` and the second has local
coordinates `(1/2, 1/2 − 2t/(1+t))`. For `0 < t < 1`, Lean checks that both
belong to the closed unit square and proves that the complete open cut triangle
is contained in the square interior. This rules out a merely area-equivalent,
but geometrically misoriented, triangle certificate.

The Lemma 5 branch of Case 6 is connected too. Its checked
triangle-area-plus-half-chord inequality now composes directly with a typed `P`
point, a boundary chord, and an inner-area lower bound. For the canonical bottom
orientation of Case 7, Lean also closes the nonadjacent-chord-plus-`P` branch
and the short-corner-chord-plus-`Q`-plus-`P` branch. If both extreme `Q` points
on the boundary line are present, convexity supplies the whole chord between
them and Lean closes that branch directly. These alternatives are exposed as
one typed Case 7 resource witness, so the score theorem is independent of the
geometric classification that constructs it. The remaining obligation is that
exhaustive classification, including the reduction from the last Case 7 branch
back to Case 6.

The positive-inner-area part of Nagamochi's Lemma 7(iv) is now proved for the
entire set of four edge strips, not left as a witness. Container containment
forces the point aligned with the square's scaled center onto the corresponding
inner boundary inside the open dilated square. Typed horizontal and vertical
reflections, coordinate swap, and an explicit inward-point family then enter
the open inner rectangle from every side and either half of the container.
Consequently the Case 7 `Q`/`P` and dual-`Q` branches derive their strict inner
contribution directly from the stated center-strip geometry.
The dual-`Q` constructor is side-independent: for any of the four edge strips,
the two matching extreme `Q` points, convexity and the strip geometry produce
the complete typed witness and hence score greater than one. The older
bottom-side theorem is retained as a specialization of this common interface.

The discrete implication in Lemma 7(iii) is kernel-checked for every side. A
typed long open chord on the corresponding `0.9` grid line contains a natural
coordinate strictly between its endpoints. Coordinates `1` and `n − 1` become
the correct endpoint `Q` constructors; every other coordinate is proved to lie
in the finite `P` index range `2..n − 2`. Typed eliminators recover a `Q` under
the assumption that no `P` is present, or a `P` when neither endpoint `Q` is
present. Endpoint bounds no longer have to be supplied by a geometric caller:
Lean derives them from the fact that every point of the open chord lies in the
closed container.

The canonical bottom-side geometric constructors for that long-grid-chord
witness are now checked as well. For a nonadjacent cut, either full cosine or
sine chord has length at least the dilation factor. For the first adjacent
pairing, the paper's Lemma 2 inequality is connected to the exact chord of the
dilated square. For the second adjacent pairing, the missing chord-membership
and chord-length identities are formalized, and the corrected Lemma 3
inequality proves the chord longer than one. Instead of the paper's informal
step that translates the square until it touches the bottom side, container
containment supplies the weaker half-extent inequality needed by monotonicity,
so the theorem applies directly to the original square. A tangent-half-angle
witness, including its
`t ≤ √2 − 1` bound, is derived directly from any positive frame with
`sin θ ≤ cos θ`; the complementary angle ordering is reduced to it by
an exact frame swap. Lean exhausts all four linear orderings of the chord
endpoints, separates centers below and above `y = 0.9`, and handles axis-aligned
frames without division. Consequently Lemma 7(i), followed by its discrete
Lemma 7(iii) consequence, is now proved for every frame in the canonical bottom
strip. Exact reflection and coordinate-swap transports carry the open chord to
the top, left and right grid lines. A single side-independent theorem now turns
the paper's `centerInStrip` hypothesis into the correctly typed `Q`-or-`P`
witness on any of the four sides; no long-grid-chord premise remains for callers
of Lemma 7(iii).

Case 7 now has a single side-independent combinatorial classifier after that
geometric input is supplied. A `P` combines with the long boundary chord. An
endpoint `Q` combines with its perpendicular `0.1` chord, with separate typed
constructors for the near and far endpoints. The latter score inequality—one
long chord, one short chord and one `Q`—is also proved directly from the resource
measure. The endpoint-to-perpendicular connection is constructed whenever its
second endpoint lies in the dilated square. The remaining branch is the final
deformation into Case 6 from the paper's geometric hypotheses.

The Case 7 bridge now consumes the actual edge-strip geometry rather than a
caller-supplied grid witness. Given the long chord on the inner boundary line,
it constructs the matching `Q`-or-`P` witness on the `0.9` grid line and feeds
both into the side-independent resource classifier. In particular, if neither
endpoint `Q` is present, Lean extracts an indexed `P` and closes the score
inequality immediately. The two perpendicular connection points and their
short boundary sides are now typed uniformly for all four edge strips. If the
matching connection point is present, convexity supplies the short chord and
Lean closes the endpoint-`Q` branch. The exhaustive Case 7 theorem therefore
returns either a proved score or one of exactly two typed disconnected-endpoint
outcomes; each such outcome additionally certifies that no indexed `P` is
present, since any `P` would already close the long-chord branch. The classifier
also checks the opposite endpoint `Q`: if both endpoints are present, their
combined point mass, the long boundary chord, and positive inner area close the
score directly. A surviving disconnected outcome therefore carries a proof
that the opposite `Q` is absent as well. Proving that those remaining outcomes
reduce to Case 6 under the
paper's terminal deformation is the sole remaining Case 7 obligation.

Coordinate-swap symmetry is formalized as an involution on points, frames and
placed squares. Lean proves that it preserves membership in dilated open square
regions, allowing the vertical chord theory to be derived from the horizontal
theory without duplicating analytic formulas. Consequently, the two-chord
branch of Case 3 now accepts any two distinct sides among bottom, top, left and
right, rather than only the bottom/top pair.

Both Case 3 branches are exposed through one typed witness: either two distinct
opposite-edge boundary chords, or one such chord together with half of the
dilated square's area in the inner rectangle. The witness implies score greater
than one for every side orientation. The remaining Case 3 task is therefore a
pure classification theorem deriving this witness from the paper's positional
hypotheses.

Case 5 is now fully proved for all four container corners and every frame.
Local quarter rotations normalize the frame signs without changing the
dilated region, coordinate swap handles either ordering of normalized sine and
cosine, and exact horizontal reflection transfers the point geometry across
the container. Container containment yields exact center half-extent bounds
even though the square region is open. Those bounds force the corresponding
two `Q` points and unit-corner point into the dilated square. Convexity supplies
the two intervening boundary chords, while openness supplies positive
inner-area measure. A final theorem performs the four-way corner-strip case
split and discharges the Case 5 score inequality without additional geometric
hypotheses.
