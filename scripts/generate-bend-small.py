#!/usr/bin/env python3
"""Write bend/Small.bend: one square needs side 1, and two squares need side 2.

A unit square in first-quadrant normal form spans c + s >= 1 in each
coordinate, and one that fits [0, 2]^2 contains the point (1, 1). A packing of
two squares in side less than 2 scales to two closed-disjoint squares fitting
[0, 2]^2 (bend/Scaling.bend), which would share that point. This follows
NearSquare.lean.
"""
import importlib.util

from bend_proof import ROOT, SquareContext, expand, num

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


def width():
    """The corners of a normal square are c + s >= c^2 + s^2 = 1 apart."""
    ctx = SquareContext()
    h = ctx.half()
    side = ctx.var('side', 'side')
    ctx.nonnegative(ctx.c, 'cosine_sign')
    ctx.nonnegative(ctx.s, 'sine_sign')
    ctx.corner_facts(h, side)
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    proof = ctx.le(num(1), side)
    return f'''
def Small.width(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: M.Membership.Corners<F, field, square, side>,
  +cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square))) -> LE({ONE}, side):
  match square corners:
    case {ctx.square_pattern()} {ctx.corners_pattern()}:
{ctx.bindings(6)}      {proof}
'''


def center():
    """A normal square fitting [0, 2]^2 contains (1, 1)."""
    return U.normal_lemma('center', [], lambda sq, v: ([], [(num(1), num(1))]), squares=[lambda q: q.c + q.s - 1],
                          module='Small', side=2)


def normal_args(square, side, fits):
    """A square's first-quadrant normal form with its corners in side `side` and its signs."""
    normal = f'Y.Symmetry.first_quadrant(TC, {square})'
    signs = f'Y.Symmetry.first_quadrant_signs(TC, {square})'
    kinds = f'LE(ZERO, P.Problem.cosine(F, field, {normal})), LE(ZERO, P.Problem.sine(F, field, {normal}))'
    corners = f'M.Membership.first_quadrant_corners(TC, {square}, {side}, M.Membership.corners_of(TC, {square}, {side}, {", ".join([fits] * 4)}))'
    return f'{normal}, {corners}, C.Certificate.first({kinds}, {signs}), C.Certificate.second({kinds}, {signs})'


def lower_bounds():
    first = 'Pk.Packings.squares(F, field, count, side, packing)(0n)'
    fits = 'Pk.Packings.fits(F, field, count, side, packing)(0n, one)'
    nonempty = 'N.Natural.le_transitive(1n, 2n, count, Unit{}, two)'
    closed = lambda k: f'S.Scaling.closed_square({TC}, {TWO}, {k}n)'
    bounds = {0: nonempty, 1: 'two'}
    inside = lambda k: (f'Y.Symmetry.first_quadrant_contains_back(TC, {closed(k)}, {CENTER}, Small.center(TC, '
                        f'{normal_args(closed(k), TWO, f"S.Scaling.closed_fits({TC}, {TWO}, less, {nonempty}, {k}n, {bounds[k]})")}))')
    return f'''
def Small.lower_bound_one({TPL}, +one: N.Natural.Le(1n, count)) -> LE({ONE}, side):
  Small.width(TC, {normal_args(first, 'side', fits).replace(f'first_quadrant(TC, {first}), ', f'first_quadrant(TC, {first}), side, ', 1)})

def Small.lower_bound_two({TPL}, +two: N.Natural.Le(2n, count)) -> LE({TWO}, side):
  M.Membership.by_cases(TC, {TWO}, side, LE({TWO}, side), +enough => enough,
    +less => Empty.absurd(LE({TWO}, side), S.Scaling.closed_disjoint({TC}, {TWO}, less, {nonempty}, 0n, 1n, {nonempty}, two,
      same => N.Natural.zero_not_successor(0n, same))({CENTER}, {inside(0)}, {inside(1)})))
'''


if __name__ == '__main__':
    (ROOT / 'bend' / 'Small.bend').write_text(expand(HEADER + width() + center() + lower_bounds()))
