# Why 61 squares appear to need side 8

**Status:** computer-assisted proof proposal, not yet a Lean theorem or a green
archive result. The [canonical definition of `s(n) = x`](../../problem-definition.md)
is separate from this explanation. The [exact certificate and verifier](../../../experiments/s61-fractional-obstruction/README.md)
are reproducible.

The easy direction is to place 61 unit squares in an 8-by-8 grid, leaving three
spaces empty. The hard direction is ruling out _every_ arrangement in a square
even slightly smaller than 8, including tilted squares.

## The idea in four sentences

Place 5,344 weighted dots inside an 8-by-8 square. The proposed exact check
shows that **every** unit square that fits inside it, whatever its angle,
contains dots of total weight at least 1. Yet all dots together have weight
only **60.990002548**. If 61 squares fitted in side less than 8, enlarging the
packing would create 61 pairwise disjoint _closed_ unit-square cores inside the
8-by-8 square, so they would need at least 61 distinct units of dot weight: a
contradiction.

The computer does not search all 61-square packings. It checks the simpler
one-square statement. Rotational symmetry leaves angles from 0° to 45°; exact
event equations cut that interval into 6,871 cases. Within each case the
verifier checks every position using integer arithmetic and conservative
interval bounds. Its local and CI runs finish with zero unresolved cases, but
the geometric reduction and verifier still deserve independent review and
formalization in Lean.

## Why this differs from earlier work

Classical unavoidable-point arguments sought a small set of points that every
unit square must hit. This proposal lets points have fractional weights; one
square may collect several small contributions. That extra freedom produces a
certificate with a total just under 61, but it also makes the verification
too large for a short hand proof. Nagamochi's published general bound gives
`s(61) ≥ 1 + 4√3 ≈ 7.9282`; a later independent piercing result of Bašić and
Slivková gives the weaker, but case-specific, bound near 7.8906. Neither
reaches 8.
The explanation of _why_ no earlier proof reached 8 is an inference from the
published methods and bounds, not a claim about every unpublished attempt.

## Figure for a short post

Use three panels, with a large `61 > 60.990002548` in the last one:

1. **Can fit:** an 8-by-8 grid with exactly three pale empty cells.
2. **Cannot shrink:** the actual weighted-dot certificate as a restrained
   heatmap, with one translucent tilted unit square. Label it “every possible
   unit square collects at least 1,” not just the illustrated pose.
3. **Contradiction:** 61 separated unit-square cores each demand weight ≥1,
   but the whole container has weight <61.

Caption: “A computer-checked _candidate proof_ for `s(61)=8`: turn infinitely
many rotated-square placements into 6,871 exact angle cases. Lean
formalization and independent review remain.” A figure must be generated from
the actual certificate, not from decorative random dots.

## Sources and credit

- Erich Friedman, [“Packing Unit Squares in Squares: A Survey and New Results”](https://www.combinatorics.org/files/Surveys/ds7/ds7v4-2005/ds7-2005.html),
  _The Electronic Journal of Combinatorics_, Dynamic Survey 7 (updated
  survey). This develops the unavoidable-point viewpoint and historical
  context.
- Hiroshi Nagamochi, [“Packing Unit Squares in a Rectangle”](https://doi.org/10.37236/1934),
  _The Electronic Journal of Combinatorics_ **12** (2005), R37. This proves
  `s(m²−2)=m`, a nearby general threshold, and gives
  `s(61) ≥ 1 + 4√3 ≈ 7.9282`.
- Wolfram Bentz, [“Optimal Packings of 13 and 46 Unit Squares in a Square”](https://doi.org/10.37236/398),
  _The Electronic Journal of Combinatorics_ **17** (2010), R126. This proves
  `s(m²−3)=m` for `m=4,7`.
- Wolfram Bentz, [“Optimal Packings of 22 and 33 Unit Squares in a Square”](https://arxiv.org/abs/1606.03746),
  arXiv:1606.03746 (2016). This proves the `m=5,6` cases and describes the
  continuously moving unavoidable-set method.
- Bojan Bašić and Anna Slivková, [“On optimal piercing of a square”](https://doi.org/10.1016/j.dam.2018.03.048),
  _Discrete Applied Mathematics_ **247** (2018), 242–251, Theorem 10. Their
  piercing method independently gives an `s(61)` lower bound near 7.8906,
  weaker than Nagamochi's general bound but directly relevant to the method.

These authors are credited for their own results and methods, not for this
new certificate. The present candidate was developed in an AI-assisted
research session directed by chelokot on 2026-09-23; its correctness and
authorship should be reviewed before any archival exact-result claim.
