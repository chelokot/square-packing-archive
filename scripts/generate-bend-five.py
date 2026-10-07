#!/usr/bin/env python3
"""Write bend/Five.bend: s(5) = 2 + r/2, where r is a square root of 2.

Four axis-aligned squares sit in the corners of the container and the fifth,
turned by 45 degrees, in its centre. For the lower bound, a square that fits
[0, 2 + r/2]^2 contains one of four points, and a packing in a smaller side
scales to five closed-disjoint squares that would share one, as in
Square5.lean. The statements hold in every ordered field for any r >= 0 with
r * r = 2.
"""
import importlib.util

from bend_proof import ROOT, Context, Refuter, T, build, expand, gap, num


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


U = load('unavoidable', 'generate-bend-unavoidable.py')
ST = load('stromquist', 'generate-bend-stromquist.py')
SM = load('small', 'generate-bend-small.py')

HEADER = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Certificate.bend as C
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Grid.bend as Q
import ./Scaling.bend as S
import ./Membership.bend as M
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Unavoidable.bend as U
'''

ROOT_T = T('root', 'root')
H = T('HALF', 'h')
GAP = ROOT_T * H
SIDE = 2 + GAP
ROOT_PARAMS = ('+root: F, +root_below: LE(MUL(root, root), R.FieldRing.of_nat(TC, 2n)), +root_above: LE(R.FieldRing.of_nat(TC, 2n), MUL(root, root)), '
               '+root_sign: LE(ZERO, root)')
ROOT_ARGS = 'root, root_below, root_above, root_sign'
COUNT = 5
POINTS = [(num(1), num(1)), (num(1), 1 + GAP), (1 + GAP, num(1)), (1 + GAP, 1 + GAP)]
PACKING = '~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>'
PACKED = '~F, ~field, ~count, ~side, ~packing'


def corners():
    """Centre and frame (cosine, sine) of each square."""
    low, high = H, SIDE - H
    return [(low, low, num(1), num(0)), (high, low, num(1), num(0)), (low, high, num(1), num(0)), (high, high, num(1), num(0)),
            (SIDE * H, SIDE * H, GAP, GAP)]


def root_context():
    ctx = Context()
    root = ctx.var('root', 'root')
    ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    ctx.equal(root * root, num(2), f'S.Scaling.pair(TC, {(root * root).bend}, {num(2).bend}, root_below, root_above)')
    ctx.nonnegative(root, 'root_sign')
    return ctx


def square_term(index):
    cx, cy, c, s = corners()[index]
    if index < 4:
        return f'Q.Grid.square(TC, {cx.bend}, {cy.bend})'
    return f'P.Square{{P.Point{{{cx.bend}, {cy.bend}}}, Five.frame(TC, {ROOT_ARGS})}}'


def by_index(name, leaf, overflow, depth=1):
    """Nested matches on `name` with the lines leaf(k, depth) for k < COUNT and overflow for larger values."""
    lines = []
    current = name
    for k in range(COUNT):
        pad = '  ' * (depth + 2 * k)
        lines += [f'{pad}match {current}:', f'{pad}  case 0n:'] + leaf(k, depth + 2 * k + 2) + [f'{pad}  case 1n+{name}{k}:']
        current = f'{name}{k}'
    lines.append(f'{"  " * (depth + 2 * COUNT)}{overflow}')
    return '\n'.join(lines) + '\n'


def frame():
    ctx = root_context()
    width = ctx.var('width', GAP.bend)
    ctx.equal(width, ctx.var_term('root') * ctx.var_term('h'), f'AL.same_reflexive(TC, {GAP.bend})')
    unit = width * width + width * width
    one = 'R.FieldRing.of_nat_one(TC)'
    below = (f'AX.le_transitive({unit.bend}, R.FieldRing.of_nat(TC, 1n), ONE, {ctx.le(unit, num(1))}, '
             f'O.FieldOrder.le_of_same(TC, R.FieldRing.of_nat(TC, 1n), ONE, {one}))')
    above = (f'AX.le_transitive(ONE, R.FieldRing.of_nat(TC, 1n), {unit.bend}, '
             f'O.FieldOrder.le_of_same(TC, ONE, R.FieldRing.of_nat(TC, 1n), AL.same_symmetric(TC, R.FieldRing.of_nat(TC, 1n), ONE, {one})), {ctx.le(num(1), unit)})')
    return f'''
def Five.frame(TPL, {ROOT_PARAMS}) -> P.Problem.Frame<F, field>:
  P.Frame{{{GAP.bend}, {GAP.bend}, {below}, {above}}}

def Five.square(TPL, {ROOT_PARAMS}, +index: Nat) -> P.Problem.Square<F, field>:
{by_index('index', lambda k, depth: ['  ' * depth + square_term(k)], square_term(0))}'''


def local_equations(ctx, k, tag, lx, ly, x, y):
    cx, cy, c, s = corners()[k]
    ox = cx + (lx * c - ly * s)
    oy = cy + (lx * s + ly * c)
    ctx.equal(x, ox, f'S.Scaling.pair(TC, x, {ox.bend}, {tag}x_is_below, {tag}x_is_above)')
    ctx.equal(y, oy, f'S.Scaling.pair(TC, y, {oy.bend}, {tag}y_is_below, {tag}y_is_above)')


def fits_leaf(k):
    ctx = root_context()
    x, y, lx, ly = (ctx.var(n, n) for n in ('x', 'y', 'lx', 'ly'))
    h = ctx.var_term('h')
    local_equations(ctx, k, '', lx, ly, x, y)
    for a, b, name in [(lx, h, 'x_at_most'), (-h, lx, 'x_at_least'), (ly, h, 'y_at_most'), (-h, ly, 'y_at_least')]:
        ctx.below(a, b, name)
    squares = [ctx.var_term('root') - 1]
    proofs = [ctx.le(0, x, squares), ctx.le(x, SIDE, squares), ctx.le(0, y, squares), ctx.le(y, SIDE, squares)]
    return f'P.InContainer{{{", ".join(proofs)}}}'


def disjoint_leaf(i, j):
    ctx = root_context()
    x, y = ctx.var('x', 'x'), ctx.var('y', 'y')
    h = ctx.var_term('h')
    steps = []
    for k, tag in ((i, 'first_'), (j, 'second_')):
        lx, ly = ctx.var(f'{tag}lx', f'{tag}lx'), ctx.var(f'{tag}ly', f'{tag}ly')
        local_equations(ctx, k, tag, lx, ly, x, y)
        for a, b, field in [(lx, h, 'x_below'), (-h, lx, 'x_above'), (ly, h, 'y_below'), (-h, ly, 'y_above')]:
            steps.append(('given_lt', f'{tag}{field}_strict', a, b, f'O.FieldOrder.strict_of(TC, {a.bend}, {b.bend}, {tag}{field})'))
    refuter = Refuter(squares=[ctx.var_term('root') - 1])

    def finish(current, stricts):
        refutation = refuter.refute(current, stricts)
        if refutation is None:
            raise SystemExit(f'squares {i} and {j} overlap')
        return refutation

    return build(ctx, steps, 'Empty', refuter, finish)


def interior_pattern(tag):
    fields = ['lx', 'ly', 'x_below', 'x_above', 'y_below', 'y_above', 'x_is_below', 'x_is_above', 'y_is_below', 'y_is_above']
    return 'P.InteriorContainment{' + ', '.join(f'+{tag}{f}' if f in ('lx', 'ly') or 'is' in f else f'{tag}{f}' for f in fields) + '}'


def side_nonnegative():
    ctx = root_context()
    return ctx.le(0, SIDE)


def packing():
    square = lambda name: f'Five.square(TC, {ROOT_ARGS}, {name})'
    absurd = lambda goal, bound: f'Empty.absurd({goal}, {bound})'
    contained = f'P.Problem.InContainer<F, field, {SIDE.bend}, P.Point{{x, y}}>'
    containment = ('match containment:', 'case P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, '
                   '+x_is_below, +x_is_above, +y_is_below, +y_is_above}:')
    fits = by_index('index', lambda k, depth: ['  ' * depth + containment[0], '  ' * (depth + 1) + containment[1], '  ' * (depth + 2) + fits_leaf(k)],
                    absurd(contained, 'bound'))
    interiors = ('match first second:', f'case {interior_pattern("first_")} {interior_pattern("second_")}:')
    disjoint = by_index('left', lambda i, depth: by_index('right', lambda j, inner: (
        ['  ' * inner + 'Empty.absurd(Empty, different({==}))'] if i == j else
        ['  ' * inner + interiors[0], '  ' * (inner + 1) + interiors[1], '  ' * (inner + 2) + disjoint_leaf(i, j)]),
        absurd('Empty', 'right_bound'), depth).rstrip('\n').split('\n'), absurd('Empty', 'left_bound'))
    return f'''
def Five.fits(TPL, {ROOT_PARAMS}, +index: Nat, +bound: N.Natural.Le(1n+index, 5n), +x: F, +y: F,
  +containment: P.Problem.Containment<F, field, {square('index')}, P.Point{{x, y}}>) -> {contained}:
{fits}
def Five.disjoint(TPL, {ROOT_PARAMS}, +left: Nat, +right: Nat, +left_bound: N.Natural.Le(1n+left, 5n), +right_bound: N.Natural.Le(1n+right, 5n),
  different: {{left == right : Nat}} -> Empty, +x: F, +y: F,
  first: P.Problem.InteriorContainment<F, field, {square('left')}, P.Point{{x, y}}>,
  second: P.Problem.InteriorContainment<F, field, {square('right')}, P.Point{{x, y}}>) -> Empty:
{disjoint}
def Five.fits_at(TPL, {ROOT_PARAMS}, +index: Nat, +bound: N.Natural.Le(1n+index, 5n), +point: P.Problem.Point<F>,
  +containment: P.Problem.Containment<F, field, {square('index')}, point>) -> P.Problem.InContainer<F, field, {SIDE.bend}, point>:
  match point:
    case P.Point{{+x, +y}}:
      Five.fits(TC, {ROOT_ARGS}, index, bound, x, y, containment)

def Five.disjoint_at(TPL, {ROOT_PARAMS}, +left: Nat, +right: Nat, +left_bound: N.Natural.Le(1n+left, 5n), +right_bound: N.Natural.Le(1n+right, 5n),
  different: {{left == right : Nat}} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, {square('left')}, point>,
  second: P.Problem.InteriorContainment<F, field, {square('right')}, point>) -> Empty:
  match point:
    case P.Point{{+x, +y}}:
      Five.disjoint(TC, {ROOT_ARGS}, left, right, left_bound, right_bound, different, x, y, first, second)

def Five.packing(TPL, {ROOT_PARAMS}) -> P.Problem.Packing<F, field, 5n, {SIDE.bend}>:
  P.Packing{{
    index => {square('index')},
    {side_nonnegative()},
    +index => +bound => point => containment => Five.fits_at(TC, {ROOT_ARGS}, index, bound, point, containment),
    +left => +right => +left_bound => +right_bound => different => point => first => second =>
      Five.disjoint_at(TC, {ROOT_ARGS}, left, right, left_bound, right_bound, different, point, first, second)
  }}
'''


def unavoidable():
    """Lean's unavoidable_points: a normal square fitting [0, 2 + g]^2 contains (1, 1), (1, 1 + g), (1 + g, 1) or (1 + g, 1 + g)."""
    ctx = ST.Square()
    root = ctx.var('root', 'root')
    ctx.equal(root * root, num(2), f'S.Scaling.pair(TC, {(root * root).bend}, {num(2).bend}, root_below, root_above)')
    ctx.nonnegative(root, 'root_sign')
    ctx.derive('root_small', 2 * root, num(3), squares=[root - 1])
    g = root * ctx.h
    total = ctx.c + ctx.s
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.derive('sum_at_least', num(1), total)
    ctx.derive('sum_at_most', 2 * total, num(3), squares=[ctx.c - ctx.s, 2 * total - 3])
    ctx.derive('weighted', g * (total + 1), num(2))
    side = 2 + g
    points = POINTS
    approximate = [(1, 1), (1, 1.7), (1.7, 1), (1.7, 1.7)]
    kinds = [f'P.Problem.Containment<F, field, square, P.Point{{{x.bend}, {y.bend}}}>' for x, y in points]
    goal = f'Or({kinds[0]}, Or({kinds[1]}, Or({kinds[2]}, {kinds[3]})))'
    contained = f'square, {side.bend}, corners, cosine_sign, sine_sign'

    def inject(k, proof):
        return [f'Inl{{{proof}}}', f'Inr{{Inl{{{proof}}}}}', f'Inr{{Inr{{Inl{{{proof}}}}}}}', f'Inr{{Inr{{Inr{{{proof}}}}}}}'][k]

    def split(current, a, b, name, yes, no):
        low, high = current.copy(), current.copy()
        low.below(a, b, name)
        high.nonnegative(a - b, gap(b, a, name), name)
        return f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {goal}, +{name} => {yes(low)}, +{name} => {no(high)})'

    def corner(name, k):
        def leaf(current):
            tx, ty = points[k]
            hyps, _ = U.corner_spec(name)(current, {'tx': tx, 'ty': ty}, side)
            return inject(k, f'U.Unavoidable.{name}_corner(TC, {contained}, {tx.bend}, {ty.bend}, {ST.lemma_hyps(current, hyps)})')
        return leaf

    def pair(orientation, first, second):
        def leaf(current):
            (px, py), (qx, qy) = points[first], points[second]
            values = {'px': px, 'py': py, 'qx': qx, 'qy': qy}
            hyps, _ = U.pair_spec(orientation)(current, values, side)
            args = ', '.join(values[n].bend for n in U.PAIR_PARAMS[orientation])
            call = f'U.Unavoidable.{orientation}_pair(TC, {contained}, {args}, {ST.lemma_hyps(current, hyps)})'
            return f'M.Membership.either({kinds[first]}, {kinds[second]}, {goal}, {call}, +a => {inject(first, "a")}, +b => {inject(second, "b")})'
        return leaf

    def triangle(*vertices):
        def leaf(current):
            ordered = ST.counterclockwise([approximate[k] for k in vertices])
            order = [vertices[[approximate[k] for k in vertices].index(v)] for v in ordered]
            return ST.triangle_points_call(current, goal, ordered, [points[k] for k in order],
                                           lambda index, name: inject(order[index], name))
        return leaf

    cx, cy = ctx.cx, ctx.cy
    low, high = num(1), 1 + g
    rows = lambda bottom, top, middle: lambda current: split(current, cy, low, 'cy_low', bottom, lambda c: split(
        c, high, cy, 'cy_high', top, middle))
    proof = split(ctx, cx, low, 'cx_low',
                  rows(corner('low_left', 0), corner('high_left', 1), pair('left', 0, 1)),
                  lambda current: split(current, high, cx, 'cx_high',
                                        rows(corner('low_right', 2), corner('high_right', 3), pair('right', 2, 3)),
                                        rows(pair('bottom', 0, 2), pair('top', 1, 3),
                                             lambda c: split(c, cy, cx, 'diagonal', triangle(0, 2, 3), triangle(0, 1, 3)))))
    return f'''
def Five.unavoidable(TPL, {ROOT_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE), +square: P.Problem.Square<F, field>,
  +corners: M.Membership.Corners<F, field, square, {SIDE.bend}>, +cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)),
  +sine_sign: LE(ZERO, P.Problem.sine(F, field, square))) -> {goal}:
{ctx.bindings(2)}  {proof}
'''


def different(left, right):
    """{left == right} -> Empty for distinct literals left < right."""
    same = 'same'
    for step in range(left):
        same = f'N.Natural.successor_injective({left - step - 1}n, {right - step - 1}n, {same})'
    return f'same => N.Natural.zero_not_successor({right - left - 1}n, {same})'


def lower_bound():
    side = SIDE.bend
    bound = lambda k: f'N.Natural.le_transitive(1n+{k}n, 5n, count, Unit{{}}, five)'
    nonempty = bound(0)
    closed = lambda k: f'S.Scaling.closed_square({PACKED}, {side}, {k}n)'
    fits = lambda k: f'S.Scaling.closed_fits({PACKED}, {side}, less, {nonempty}, {k}n, {bound(k)})'
    point = lambda p: f'P.Point{{{POINTS[p][0].bend}, {POINTS[p][1].bend}}}'
    normal = lambda k: f'Y.Symmetry.first_quadrant(TC, {closed(k)})'
    kind = lambda square, p: f'P.Problem.Containment<F, field, {square}, {point(p)}>'

    def pigeon(k, used):
        def chosen(p, name):
            found = f'Y.Symmetry.first_quadrant_contains_back(TC, {closed(k)}, {point(p)}, {name})'
            if p in used:
                j = used[p]
                return (f'S.Scaling.closed_disjoint({PACKED}, {side}, less, {nonempty}, {j}n, {k}n, {bound(j)}, {bound(k)}, {different(j, k)})'
                        f'({point(p)}, held{j}, {found})')
            rest = pigeon(k + 1, {**used, p: k})
            return f'M.Membership.bind({kind(closed(k), p)}, Empty, {found}, +held{k} => {rest})'

        def level(p, value):
            if p == 3:
                return chosen(3, value)
            rest = kind(normal(k), 3)
            for q in range(2, p, -1):
                rest = f'Or({kind(normal(k), q)}, {rest})'
            return (f'M.Membership.either({kind(normal(k), p)}, {rest}, Empty, {value}, +at{k}_{p} => {chosen(p, f"at{k}_{p}")}, '
                    f'other{k}_{p} => {level(p + 1, f"other{k}_{p}")})')
        return level(0, f'Five.unavoidable(TC, {ROOT_ARGS}, nontrivial, {SM.normal_args(closed(k), side, fits(k))})')

    ctx = Context()
    one = ctx.var('one', 'ONE')
    ctx.equal(one, num(1), 'S.Scaling.one_is_number(TC)')
    ctx.below(one, num(0), 'collapsed')
    broken = ctx.le(num(0), -num(1))
    goal = f'LE({side}, side)'
    return f'''
def Five.nontrivial(TPL, {PACKING}, {ROOT_PARAMS}, +less: O.FieldOrder.Strict(TC, side, {side})) -> O.FieldOrder.Strict(TC, ZERO, ONE):
  M.Membership.by_cases(TC, ONE, ZERO, O.FieldOrder.Strict(TC, ZERO, ONE),
    +collapsed => Empty.absurd(O.FieldOrder.Strict(TC, ZERO, ONE),
      O.FieldOrder.lt_of(TC, side, {side}, less)(S.Scaling.anything(TC, {side}, side, {broken}))),
    +positive => positive)

def Five.lower_bound(TPL, {PACKING}, {ROOT_PARAMS}, +five: N.Natural.Le(5n, count)) -> {goal}:
  M.Membership.by_cases(TC, {side}, side, {goal}, +enough => enough,
    +less => Empty.absurd({goal}, M.Membership.bind(O.FieldOrder.Strict(TC, ZERO, ONE), Empty, Five.nontrivial(TC, ~count, ~side, ~packing, {ROOT_ARGS}, less),
      +nontrivial => {pigeon(0, {})})))
'''


def main():
    (ROOT / 'bend' / 'Five.bend').write_text(expand(HEADER + frame() + packing() + unavoidable() + lower_bound()))


if __name__ == '__main__':
    main()
