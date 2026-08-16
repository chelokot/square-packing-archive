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
