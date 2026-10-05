#!/usr/bin/env python3
"""Write bend/Singletons.bend: two squares that hold single adjacent key points meet (StromquistSixLemma8.lean).

The base case puts the corner square on (1, 1), away from (1, 3/2), and the
midpoint square on (3/2, 1), away from (1, 1), (2, 1) and (3/2, 3/2). The
midpoint square reaches the points (1 + g/s, 1) and (1, 1 - g/c) on its
boundary, and the corner square holds one of them.
"""
import importlib.util
from fractions import Fraction

from bend_proof import ROOT, Refuter, T, build, expand, gap, num, one_of

spec = importlib.util.spec_from_file_location('stromquist', ROOT / 'scripts' / 'generate-bend-stromquist.py')
ST = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ST)

HEADER = ST.HEADER + 'import ./Stromquist.bend as Q\n'
ST.SELF['name'] = 'Q.Stromquist.'
SQUARE_PARAMS = ST.SQUARE_PARAMS
H = ST.H


def outside_type(values):
    return f'B.Bits.Holds(Bool.not(M.Membership.inside(TC, square, {ST.point_term(values)})))'


def midpoint_context():
    """The midpoint square through (3/2, 1), with its missing neighbours."""
    ctx = ST.Square()
    k1 = ST.contained(ctx, (Fraction(3, 2), Fraction(1)), 'mid')
    missing = [ctx.local_point(v, f'm{k}') for k, v in enumerate([(Fraction(1), Fraction(1)), (Fraction(2), Fraction(1)), (Fraction(3, 2), Fraction(3, 2))])]
    return ctx, k1, missing


MISSING = [(Fraction(1), Fraction(1)), (Fraction(2), Fraction(1)), (Fraction(3, 2), Fraction(3, 2))]
MID = (Fraction(3, 2), Fraction(1))


def orientation(axis):
    """Lean's midpoint_orientation: (1 - c)/2 < H or (1 - s)/2 < V for the local coordinates (H, V) of (3/2, 1)."""
    ctx, k1, missing = midpoint_context()
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.freeze('known')
    lx, ly, _ = ctx.locals_of[(k1[0].text, k1[1].text)]
    low, high = ((1 - ctx.c) * H, lx) if axis == 'x' else ((1 - ctx.s) * H, ly)
    goal = f'O.FieldOrder.Strict(TC, {low.bend}, {high.bend})'
    steps = [('outside', 'square', point, f'out{k}') for k, point in enumerate(missing)] + [('lt', 'bound', low, high)]
    proof = build(ctx, steps, goal, Refuter(), lambda current, stricts: 'bound')
    outs = ', '.join(f'+out{k}: {outside_type(v)}' for k, v in enumerate(MISSING))
    return f'''
def Singletons.orientation_{axis}(TPL, {SQUARE_PARAMS}, +mid: {ST.local_type(k1)}, {outs}) -> {goal}:
  match mid:
    case {ST.local_pattern('mid')}:
{ctx.bindings(6)}      {proof}
'''


CORNERS_PATTERN = 'M.Corners{' + ', '.join(f'P.InContainer{{+{n}_left, +{n}_right, +{n}_bottom, +{n}_top}}'
                                            for n in ('low_low', 'low_high', 'high_low', 'high_high')) + '}'


def gaps_terms(ctx):
    lx, ly, _ = ctx.locals_of[(ST.KEYS[1][0].text, ST.KEYS[1][1].text)]
    inverse_s = ctx.var_term('is')
    inverse_c = ctx.var_term('ic')
    g = ly - H + ctx.s * H
    return lx, ly, g, g * inverse_s, g * inverse_c


def midpoint_gaps():
    """Lean's midpoint_gap_sum and midpoint_gap_endpoints."""
    ctx = ST.Square()
    k1 = ST.contained(ctx, MID, 'mid')
    ctx.corner_facts(['low_low'])
    ctx.var('is', 'INV(P.Problem.sine(F, field, square))')
    ctx.var('ic', 'INV(P.Problem.cosine(F, field, square))')
    lx, ly, g, right, down = gaps_terms(ctx)
    right_point = ctx.local_terms_point((num(1) + right, num(1)), 'right')
    down_point = ctx.local_terms_point((num(1), num(1) - down), 'down')
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.freeze('known')
    c, s = ctx.c, ctx.s
    inverse_s, inverse_c = ctx.var_term('is'), ctx.var_term('ic')
    orient = [((1 - c) * H, lx, 'orient_x'), ((1 - s) * H, ly, 'orient_y')]
    for a, b, name in orient:
        ctx.nonnegative(b - a, gap(a, b, name))
    inverse = lambda v, name: (f'AL.same_transitive(TC, MUL({v.bend}, INV({v.bend})), ONE, R.FieldRing.of_nat(TC, 1n), '
                               f'AL.mul_inverse(TC, {v.bend}, O.FieldOrder.lt_of(TC, ZERO, {v.bend}, {name})), S.Scaling.one_is_number(TC))')
    excess = lx - (1 - c) * H
    room = (1 - c) * (1 - s) - g * c
    steps = [('lt', 'c_pos', num(0), c), ('lt', 's_pos', num(0), s),
             ('equation', s * inverse_s, num(1), inverse(s, 's_pos')), ('equation', c * inverse_c, num(1), inverse(c, 'c_pos')),
             ('lt', 'excess', num(0), excess),
             ('given_lt', 'tilted', num(0), s * excess, f'M.Membership.strict_product(TC, {s.bend}, {excess.bend}, s_pos, excess)'),
             ('lt', 'room', num(0), room),
             ('le', 'product_bound', 2 * s * (c + s), (1 + c) * (1 + s), []),
             ('le', 'weighted', num(0), c * c * s * ((1 + c) * (1 + s) - 2 * s * (c + s)), [], {'products': 4, 'only': ['cosine_sign', 'sine_sign', 'product_bound']}),
             ('le_refute', 'frame', 2 * (1 - c) * (1 - s) * (c + s), c * c * s, {'products': 3, 'only': ['weighted', 'cosine_sign', 'sine_sign']}),
             ('lt', 'sum_pos', num(0), c + s),
             ('given_lt', 'multiplied', num(0), room * (c + s), f'M.Membership.strict_product(TC, {room.bend}, {(c + s).bend}, room, sum_pos)'),
             ('lt', 'desired', g * (c + s), c * s * H),
             ('lt', 'g_pos', num(0), g),
             ('lt', 'right_pos', num(0), right), ('lt', 'down_pos', num(0), down),
             ('lt', 'gap_sum', right + down, H, {'products': 3, 'only': ['desired', 'c_pos', 's_pos']})]
    kinds = [f'O.FieldOrder.Strict(TC, ZERO, {right.bend})', f'O.FieldOrder.Strict(TC, ZERO, {down.bend})',
             f'O.FieldOrder.Strict(TC, {(right + down).bend}, HALF)',
             f'P.Problem.Containment<F, field, square, P.Point{{{right_point[0].bend}, {right_point[1].bend}}}>',
             f'P.Problem.Containment<F, field, square, P.Point{{{down_point[0].bend}, {down_point[1].bend}}}>']
    goal = both_type(kinds)
    refuter = Refuter(squares=[1 - c, 1 - s])

    def finish(current, stricts):
        parts = ['right_pos', 'down_pos', 'gap_sum',
                 one_of(current, 'square', [right_point], refuter, stricts), one_of(current, 'square', [down_point], refuter, stricts)]
        return both_value(parts)
    proof = build(ctx, steps, goal, refuter, finish, [(a, b, name) for a, b, name in orient])
    return f'''
def Singletons.gaps(TPL, {SQUARE_PARAMS}, +mid: {ST.local_type(k1)},
  +orient_x: O.FieldOrder.Strict(TC, {orient[0][0].bend}, {orient[0][1].bend}), +orient_y: O.FieldOrder.Strict(TC, {orient[1][0].bend}, {orient[1][1].bend})) ->
  {goal}:
  match corners mid:
    case {CORNERS_PATTERN} {ST.local_pattern('mid')}:
{ctx.bindings(6)}      {proof}
'''


def both_type(kinds):
    out = kinds[-1]
    for kind in reversed(kinds[:-1]):
        out = f'C.Certificate.Both<{kind}, {out}>'
    return out


def both_value(parts):
    out = parts[-1]
    for part in reversed(parts[:-1]):
        out = f'C.Both{{{part}, {out}}}'
    return out


CORNER = (Fraction(1), Fraction(1))
ABOVE = (Fraction(1), Fraction(3, 2))


def corner_gap():
    """Lean's corner_square_contains_gap_endpoint for the square through (1, 1) that misses (1, 3/2)."""
    ctx = ST.Square()
    k0 = ST.contained(ctx, CORNER, 'corner')
    above = ctx.local_point(ABOVE, 'above')
    ctx.corner_facts(['low_high'])
    right_gap, down_gap = ctx.var('rg', 'rg'), ctx.var('dg', 'dg')
    ctx.var('is', 'INV(P.Problem.sine(F, field, square))')
    ctx.var('ic', 'INV(P.Problem.cosine(F, field, square))')
    right_point = ctx.local_terms_point((num(1) + right_gap, num(1)), 'right')
    down_point = ctx.local_terms_point((num(1), num(1) - down_gap), 'down')
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.derive('sum_at_least', num(1), ctx.c + ctx.s)
    ctx.derive('sum_at_most', ctx.c + ctx.s, num(1) + H, squares=[ctx.c - ctx.s])
    ctx.derive('frame_bound', ctx.c * ctx.s * H, ctx.c + ctx.s - 1)
    ctx.freeze('known')
    c, s = ctx.c, ctx.s
    inverse_s, inverse_c = ctx.var_term('is'), ctx.var_term('ic')
    given = [(num(0), right_gap, 'rg_pos'), (num(0), down_gap, 'dg_pos'), (right_gap + down_gap, H, 'gap_sum')]
    for a, b, name in given:
        ctx.nonnegative(b - a, gap(a, b, name), name)
    inverse = lambda v, name: (f'AL.same_transitive(TC, MUL({v.bend}, INV({v.bend})), ONE, R.FieldRing.of_nat(TC, 1n), '
                               f'AL.mul_inverse(TC, {v.bend}, O.FieldOrder.lt_of(TC, ZERO, {v.bend}, {name})), S.Scaling.one_is_number(TC))')
    positive = [('equation', s * inverse_s, num(1), inverse(s, 's_flat')), ('equation', c * inverse_c, num(1), inverse(c, 'c_flat')),
                ('le', 'ic_nonnegative', num(0), inverse_c, [inverse_c]), ('le', 'is_nonnegative', num(0), inverse_s, [inverse_s]),
                ('le', 'ic_large', num(1), inverse_c, []), ('le', 'is_large', num(1), inverse_s, []),
                ('le', 'cs_nonneg', num(0), c * s, []), ('le', 'inverse_product', num(0), inverse_s * inverse_c, [])]
    lx, ly, _ = ctx.locals_of[(ST.KEYS[0][0].text, ST.KEYS[0][1].text)]
    reach = [('reach_ad', c * H, 1 - lx + ly), ('reach_bc', s * H, 1 + lx + ly), ('reach_bd', c * s * H, (H + ly) * (c + s))]
    tries = [('try', [('le_refute', name, a, b, {'splits': [(s, c)], 'squares': [1 - c, 1 - s, c - s]}),
                      ('le_refute', name, a, b, {'splits': [(s, c)], 'squares': [1 - c, 1 - s, c - s], 'products': 3})])
             for name, a, b in reach]
    steps = [('outside', 'square', above, 'out')] + tries + [
             ('cases', 'c_flat', c, num(0), [], [('cases', 's_flat', s, num(0), [], positive)])]
    points = [right_point, down_point]
    goal = ST.or_containments([None, None]) if False else ST.containments('square', [f'P.Point{{{p[0].bend}, {p[1].bend}}}' for p in points], named=True)
    refuter = Refuter(squares=[1 - c, 1 - s], splits=[(c, s)])
    leaves = Refuter(squares=[1 - c, 1 - s], products=(2, 3),
                     only=['cosine_sign', 'sine_sign', 'cosine_at_most', 'sine_at_most', 'sum_at_least', 'reach_ad', 'reach_bc', 'reach_bd',
                           'ic_nonnegative', 'is_nonnegative', 'ic_large', 'is_large', 'cs_nonneg', 'inverse_product', 'c_flat', 's_flat'] +
                          [f'corner_{a}_{b}' for a in ('x', 'y') for b in ('at_most', 'at_least')])
    proof = build(ctx, steps, goal, refuter, lambda current, stricts: one_of(current, 'square', points, leaves, stricts), given)
    return f'''
def Singletons.corner_gap(TPL, {SQUARE_PARAMS}, +corner: {ST.local_type(k0)}, +out: {outside_type(ABOVE)},
  +rg: F, +dg: F, +rg_pos: O.FieldOrder.Strict(TC, ZERO, rg), +dg_pos: O.FieldOrder.Strict(TC, ZERO, dg),
  +gap_sum: O.FieldOrder.Strict(TC, ADD(rg, dg), HALF)) -> {goal}:
  match corners corner:
    case {CORNERS_PATTERN} {ST.local_pattern('corner')}:
{ctx.bindings(6)}      {proof}
'''


def meet_points():
    """The two boundary points of meet_base for a midpoint square written SQUARE_B."""
    ctx = ST.Square()
    ST.contained(ctx, MID, 'mid')
    ctx.var('is', 'INV(P.Problem.sine(F, field, square))')
    ctx.var('ic', 'INV(P.Problem.cosine(F, field, square))')
    lx, ly, g, right, down = gaps_terms(ctx)
    rename = lambda text: text.replace('square', 'SQUARE_B')
    return (f'P.Point{{{rename((num(1) + right).bend)}, {rename(num(1).bend)}}}', f'P.Point{{{rename(num(1).bend)}, {rename((num(1) - down).bend)}}}')


def meet_base():
    """Lean's adjacent_singletons_intersect_nonnegative_frames: both squares hold one boundary point of the midpoint square."""
    ctx = ST.Square()
    k1 = ST.contained(ctx, MID, 'mid')
    ctx.var('is', 'INV(P.Problem.sine(F, field, square))')
    ctx.var('ic', 'INV(P.Problem.cosine(F, field, square))')
    lx, ly, g, right, down = gaps_terms(ctx)
    rename = lambda text: text.replace('square', 'b')
    right_point = f'P.Point{{{rename((num(1) + right).bend)}, {rename(num(1).bend)}}}'
    down_point = f'P.Point{{{rename(num(1).bend)}, {rename((num(1) - down).bend)}}}'
    rg, dg = rename(right.bend), rename(down.bend)
    key = lambda k: f'Q.Stromquist.key{k}(TC)'
    contains = lambda square, point: f'P.Problem.Containment<F, field, {square}, {point}>'
    both = lambda point: f'C.Certificate.Both<{contains("a", point)}, {contains("b", point)}>'
    goal = f'Or({both(right_point)}, {both(down_point)})'
    strict_types = [f'O.FieldOrder.Strict(TC, ZERO, {rg})', f'O.FieldOrder.Strict(TC, ZERO, {dg})', f'O.FieldOrder.Strict(TC, ADD({rg}, {dg}), HALF)']
    kinds = strict_types + [contains('b', right_point), contains('b', down_point)]
    gaps_type = both_type(kinds)
    get = lambda i: ('C.Certificate.first' if i < 4 else 'C.Certificate.second')
    def part(i):
        out = 'gaps'
        for j in range(i):
            out = f'C.Certificate.second({kinds[j]}, {both_type(kinds[j + 1:])}, {out})'
        if i < len(kinds) - 1:
            out = f'C.Certificate.first({kinds[i]}, {both_type(kinds[i + 1:])}, {out})'
        return out
    square_a = lambda name: name.replace('square', 'a')
    params = ', '.join([f'+{p}: P.Problem.Square<F, field>' if False else '' for p in []])
    local = lambda square, k: f'G.Geometry.contains_local(TC, {square}, {key(k)}, {square}_in)'
    return f'''
def Singletons.meet_base(TPL, +a: P.Problem.Square<F, field>, +a_corners: M.Membership.Corners<F, field, a, {ST.THREE}>,
  +a_cosine: LE(ZERO, P.Problem.cosine(F, field, a)), +a_sine: LE(ZERO, P.Problem.sine(F, field, a)),
  +b: P.Problem.Square<F, field>, +b_corners: M.Membership.Corners<F, field, b, {ST.THREE}>,
  +b_cosine: LE(ZERO, P.Problem.cosine(F, field, b)), +b_sine: LE(ZERO, P.Problem.sine(F, field, b)),
  +a_in: {contains("a", key(0))}, +a_out: B.Bits.Holds(Bool.not(M.Membership.inside(TC, a, {key(3)}))),
  +b_in: {contains("b", key(1))}, +b_out0: B.Bits.Holds(Bool.not(M.Membership.inside(TC, b, {key(0)}))),
  +b_out2: B.Bits.Holds(Bool.not(M.Membership.inside(TC, b, {key(2)}))), +b_out4: B.Bits.Holds(Bool.not(M.Membership.inside(TC, b, {key(4)})))) ->
  {goal}:
  +b_mid: {rename(ST.local_type(k1))} = {local('b', 1)}
  +gaps: {gaps_type} = Singletons.gaps(TC, b, b_corners, b_cosine, b_sine, b_mid,
    Singletons.orientation_x(TC, b, b_corners, b_cosine, b_sine, b_mid, b_out0, b_out2, b_out4),
    Singletons.orientation_y(TC, b, b_corners, b_cosine, b_sine, b_mid, b_out0, b_out2, b_out4))
  M.Membership.either({contains("a", right_point)}, {contains("a", down_point)}, {goal},
    Singletons.corner_gap(TC, a, a_corners, a_cosine, a_sine, {local('a', 0)}, a_out, {rg}, {dg}, {part(0)}, {part(1)}, {part(2)}),
    +right => Inl{{C.Both{{right, {part(3)}}}}}, +down => Inr{{C.Both{{down, {part(4)}}}}})
'''


def main():
    parts = [HEADER, orientation('x'), orientation('y'), midpoint_gaps(), corner_gap(), meet_base()]
    (ROOT / 'bend' / 'Singletons.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
