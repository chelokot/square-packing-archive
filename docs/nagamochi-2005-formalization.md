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
