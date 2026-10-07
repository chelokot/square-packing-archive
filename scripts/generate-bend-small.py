#!/usr/bin/env python3
"""Write bend/Small.bend: two squares need side 2.

A unit square in first-quadrant normal form that fits [0, 2]^2 contains the
point (1, 1). A packing of two squares in side less than 2 scales to two
closed-disjoint squares fitting [0, 2]^2 (bend/Scaling.bend), which would
share that point. This follows NearSquare.lean.
"""
import importlib.util

from bend_proof import ROOT, expand, num

spec = importlib.util.spec_from_file_location('unavoidable', ROOT / 'scripts' / 'generate-bend-unavoidable.py')
U = importlib.util.module_from_spec(spec)
spec.loader.exec_module(U)

HEADER = U.HEADER + '''import ./bend-math/Natural.bend as N
import ./Packings.bend as Pk
'''

TPL = '~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>'
TC = '~F, ~field, ~count, ~side, ~packing'
ONE = 'R.FieldRing.of_nat(TC, 1n)'
TWO = 'R.FieldRing.of_nat(TC, 2n)'
CENTER = f'P.Point{{{ONE}, {ONE}}}'


def center():
    """A normal square fitting [0, 2]^2 contains (1, 1)."""
    return U.normal_lemma('center', [], lambda sq, v, side: ([], [(num(1), num(1))]), squares=[lambda q: q.c + q.s - 1],
                          module='Small', side=2)


def normal_args(square, side, fits):
    """A square's first-quadrant normal form with its corners in side `side` and its signs."""
    normal = f'Y.Symmetry.first_quadrant(TC, {square})'
    signs = f'Y.Symmetry.first_quadrant_signs(TC, {square})'
    kinds = f'LE(ZERO, P.Problem.cosine(F, field, {normal})), LE(ZERO, P.Problem.sine(F, field, {normal}))'
    corners = f'M.Membership.first_quadrant_corners(TC, {square}, {side}, M.Membership.corners_of(TC, {square}, {side}, {", ".join([fits] * 4)}))'
    return f'{normal}, {corners}, C.Certificate.first({kinds}, {signs}), C.Certificate.second({kinds}, {signs})'


def lower_bounds():
    nonempty = 'N.Natural.le_transitive(1n, 2n, count, Unit{}, two)'
    closed = lambda k: f'S.Scaling.closed_square({TC}, {TWO}, {k}n)'
    bounds = {0: nonempty, 1: 'two'}
    inside = lambda k: (f'Y.Symmetry.first_quadrant_contains_back(TC, {closed(k)}, {CENTER}, Small.center(TC, '
                        f'{normal_args(closed(k), TWO, f"S.Scaling.closed_fits({TC}, {TWO}, less, {nonempty}, {k}n, {bounds[k]})")}))')
    return f'''
def Small.lower_bound_two({TPL}, +two: N.Natural.Le(2n, count)) -> LE({TWO}, side):
  M.Membership.by_cases(TC, {TWO}, side, LE({TWO}, side), +enough => enough,
    +less => Empty.absurd(LE({TWO}, side), S.Scaling.closed_disjoint({TC}, {TWO}, less, {nonempty}, 0n, 1n, {nonempty}, two,
      same => N.Natural.zero_not_successor(0n, same))({CENTER}, {inside(0)}, {inside(1)})))
'''


if __name__ == '__main__':
    (ROOT / 'bend' / 'Small.bend').write_text(expand(HEADER + center() + lower_bounds()))
