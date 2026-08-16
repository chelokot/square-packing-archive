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
chords, and two distinct `Q` points imply total score greater than one. What is
not yet claimed is the geometric premise that every square whose center lies in
a corner region necessarily contains those resources.
