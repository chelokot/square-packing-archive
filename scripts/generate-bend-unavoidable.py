#!/usr/bin/env python3
"""Write bend/Unavoidable.bend: points that a square fitting the container [0, 3]^2 must contain.

Ports the single-square lemmas of Unavoidable.lean, Friedman.lean and
FriedmanStrip.lean that Stromquist's s(6) argument uses. Every lemma is stated
for a square whose frame has nonnegative cosine and sine, the first-quadrant
normal form; since such a lemma is about the square as a set, each orientation
of the container gets its own statement instead of a reflection.
"""
from types import SimpleNamespace

from bend_proof import ROOT, Context, Refuter, SquareContext, T, containments, expand, gap, num, one_of

HEADER = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Certificate.bend as C
import ./Problem.bend as P
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Scaling.bend as S
import ./Membership.bend as M
'''

THREE = 'R.FieldRing.of_nat(TC, 3n)'
SIGNATURE = SimpleNamespace(
    cx=T('P.Problem.center_x(F, field, square)', 'cx'), cy=T('P.Problem.center_y(F, field, square)', 'cy'),
    c=T('P.Problem.cosine(F, field, square)', 'c'), s=T('P.Problem.sine(F, field, square)', 's'))

ORIENTATIONS = {
    'bottom': (lambda x, y: (x, y), lambda x, y: (x, y)),
    'top': (lambda x, y: (x, 3 - y), lambda x, y: (x, 3 - y)),
    'left': (lambda x, y: (y, x), lambda x, y: (y, x)),
    'right': (lambda x, y: (3 - y, x), lambda x, y: (y, 3 - x)),
}


def normal_lemma(name, params, spec, squares=(), splits=(), derive=True, module='Unavoidable', side=3):
    """Emit a lemma for a normal square fitting [0, side]^2: hypotheses `a <= b` from spec(square, params) give one of its points."""
    signature_params = {p: T(p, p) for p in params}
    hyps, points = spec(SIGNATURE, signature_params)
    ctx = SquareContext()
    h = ctx.half()
    values = {p: ctx.var(p, p) for p in params}
    ctx.nonnegative(ctx.c, 'cosine_sign')
    ctx.nonnegative(ctx.s, 'sine_sign')
    ctx.corner_facts(h, num(side))
    proof_hyps, proof_points = spec(ctx, values)
    for k, (a, b) in enumerate(proof_hyps):
        ctx.below(a, b, f'hyp{k}')
    q = ctx.bind_square()
    for k, point in enumerate(proof_points):
        ctx.local_vars(point, k, q)
    ctx.freeze('base')
    if derive:
        ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
        ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
        ctx.derive('sum_at_least', num(1), ctx.c + ctx.s)
        ctx.freeze('known')
    refuter = Refuter(squares=[spl(ctx) for spl in squares], splits=[(a(ctx), b(ctx)) for a, b in splits])
    proof = one_of(ctx, q, proof_points, refuter)
    param_text = ''.join(f', +{p}: F' for p in params)
    hyp_text = ''.join(f',\n  +hyp{k}: LE({a.bend}, {b.bend})' for k, (a, b) in enumerate(hyps))
    return f'''
def {module}.{name}(TPL, +square: P.Problem.Square<F, field>, +corners: M.Membership.Corners<F, field, square, R.FieldRing.of_nat(TC, {side}n)>,
  +cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square)){param_text}{hyp_text}) ->
  {containments('square', points)}:
  match square corners:
    case {ctx.square_pattern()} {ctx.corners_pattern()}:
{ctx.bindings(6)}      {proof}
'''


CORNERS = {
    'low_left': lambda x, y: (x, y),
    'low_right': lambda x, y: (3 - x, y),
    'high_left': lambda x, y: (x, 3 - y),
    'high_right': lambda x, y: (3 - x, 3 - y),
}


def corner_spec(name):
    back = CORNERS[name]

    def spec(sq, v):
        cx, cy = back(sq.cx, sq.cy)
        tx, ty = back(v['tx'], v['ty'])
        return [(tx, num(1)), (ty, num(1)), (cx, tx), (cy, ty)], [(v['tx'], v['ty'])]
    return spec


def corner(name):
    """Lean's contains_cornerPoint at one corner of the container."""
    return normal_lemma(f'{name}_corner', ['tx', 'ty'], corner_spec(name), squares=[lambda q: q.c + q.s - 1])


PAIR_PARAMS = {'bottom': ['px', 'py', 'qx'], 'top': ['px', 'py', 'qx'], 'left': ['px', 'py', 'qy'], 'right': ['px', 'py', 'qy']}


def pair_spec(orientation):
    place, back = ORIENTATIONS[orientation]
    along_x = orientation in ('bottom', 'top')

    def spec(sq, v):
        cx, cy = back(sq.cx, sq.cy)
        first = (v['px'], v['py'])
        second = (v['qx'], v['py']) if along_x else (v['px'], v['qy'])
        left, height = back(*first)
        gap = v['qx'] - v['px'] if along_x else v['qy'] - v['py']
        return ([(height, num(1)), (num(0), gap), (gap, num(1)), (height + gap * (sq.c * sq.s), sq.c + sq.s),
                 (left, cx), (cx, left + gap), (cy, height)], [first, second])
    return spec


def pair(orientation):
    """Lean's contains_bottomPairWith along one side: the square holds the first or the second point."""
    return normal_lemma(f'{orientation}_pair', PAIR_PARAMS[orientation], pair_spec(orientation),
                        squares=[lambda q: 1 - q.s, lambda q: 1 - q.c], splits=[(lambda q: q.c, lambda q: q.s)])


DIRECTIONS = {
    'right': (('le', 'y', 'x'), ('le', '-x', 'y'), ('h', 'x')),
    'bottom': (('le', 'y', 'x'), ('lt', 'y', '-x'), ('y', '-h')),
    'top': (('lt', 'x', 'y'), ('le', '-x', 'y'), ('h', 'y')),
    'left': (('lt', 'x', 'y'), ('lt', 'y', '-x'), ('x', '-h')),
}


def direction(name):
    """A vertex outside the unit square, in one of the four regions cut by the diagonals, leaves it on that side."""
    first, second, (low, high) = DIRECTIONS[name]
    ctx = Context()
    terms = {'x': ctx.var('x', 'x'), 'y': ctx.var('y', 'y'), 'h': ctx.var('h', 'HALF')}
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    terms['-x'] = -terms['x']
    terms['-h'] = -terms['h']
    params = []
    stricts = []
    for k, (kind, a, b) in enumerate((first, second)):
        u, v = terms[a], terms[b]
        if kind == 'le':
            ctx.below(u, v, f'region{k}')
            params.append(f'+region{k}: LE({u.bend}, {v.bend})')
        else:
            ctx.nonnegative(v - u, gap(u, v, f'region{k}'))
            stricts.append((u, v, f'region{k}'))
            params.append(f'+region{k}: O.FieldOrder.Strict(TC, {u.bend}, {v.bend})')
    u, v = terms[low], terms[high]
    x, y, h = terms['x'], terms['y'], terms['h']
    refuter = Refuter()
    leaves = []
    for k, (a, b) in enumerate([(h, x), (x, -h), (h, y), (y, -h)]):
        leaf = ctx.copy()
        leaf.nonnegative(b - a, gap(a, b, f'miss{k}'))
        leaf.below(v, u, 'bad')
        proof = refuter.refute(leaf, stricts + [(a, b, f'miss{k}')])
        assert proof is not None, (name, k)
        leaves.append(f'+miss{k} => O.FieldOrder.strict_of(TC, {u.bend}, {v.bend}, +bad => {proof})')
    goal = f'O.FieldOrder.Strict(TC, {u.bend}, {v.bend})'
    return f'''
def Unavoidable.{name}_side(TPL, +x: F, +y: F, {", ".join(params)}, missing: M.Membership.Missing(TC, x, y)) -> {goal}:
  M.Membership.cases_missing(TC, x, y, {goal}, missing, {", ".join(leaves)})
'''


def triangle_core():
    """Lean's triangle_coordinate_core: a unit square centred at a convex combination of three
    vertices at mutual distance at most one contains one of them."""
    ctx = Context()
    xs = [ctx.var(f'x{i}', f'x{i}') for i in range(3)]
    ys = [ctx.var(f'y{i}', f'y{i}') for i in range(3)]
    ws = [ctx.var(f'w{i}', f'w{i}') for i in range(3)]
    h = ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    params = [f'+{v}: F' for v in [f'x{i}' for i in range(3)] + [f'y{i}' for i in range(3)] + [f'w{i}' for i in range(3)]]
    for i in range(3):
        ctx.nonnegative(ws[i], f'weight{i}')
        params.append(f'+weight{i}: LE(ZERO, w{i})')
    sums = [(ws[0] + ws[1] + ws[2], num(1), 'sum'), (ws[0] * xs[0] + ws[1] * xs[1] + ws[2] * xs[2], num(0), 'balance_x'),
            (ws[0] * ys[0] + ws[1] * ys[1] + ws[2] * ys[2], num(0), 'balance_y')]
    for a, b, name in sums:
        ctx.equal(a, b, f'S.Scaling.pair(TC, {a.bend}, {b.bend}, {name}_below, {name}_above)')
        params.append(f'+{name}_below: LE({a.bend}, {b.bend}), +{name}_above: LE({b.bend}, {a.bend})')
    pairs = [(0, 1), (0, 2), (1, 2)]
    for i, j in pairs:
        d = (xs[i] - xs[j]) * (xs[i] - xs[j]) + (ys[i] - ys[j]) * (ys[i] - ys[j])
        ctx.below(d, num(1), f'distance{i}{j}')
        params.append(f'+distance{i}{j}: LE({d.bend}, {num(1).bend})')
    ctx.freeze('base')
    squares = []
    for i, j in pairs:
        squares += [ys[i] - ys[j], xs[i] - xs[j], 1 - xs[i] + xs[j], 1 + xs[i] - xs[j], 1 - ys[i] + ys[j], 1 + ys[i] - ys[j]]
    refuter = Refuter(squares=squares, splits=[(num(1), 3 * ws[0]), (num(1), 3 * ws[1])])
    sides = {'right': (h, None), 'bottom': None, 'top': None, 'left': None}
    goal = 'Or(G.Geometry.Local<F, field, x0, y0>, Or(G.Geometry.Local<F, field, x1, y1>, G.Geometry.Local<F, field, x2, y2>))'

    def inject(i, proof):
        return [f'Inl{{{proof}}}', f'Inr{{Inl{{{proof}}}}}', f'Inr{{Inr{{{proof}}}}}'][i]

    def vertex(i, current, stricts):
        if i == 3:
            proof = refuter.refute(current, stricts)
            if proof is None:
                raise SystemExit(f'triangle leaf failed: {[(u.text, v.text) for u, v, _ in stricts]}')
            return f'Empty.absurd({goal}, {proof})'
        if len(stricts) >= 2:
            early = refuter.refute(current, stricts, splits=[])
            if early is not None:
                return f'Empty.absurd({goal}, {early})'
        x, y = xs[i], ys[i]
        out = {}
        for first in (True, False):
            for second in (True, False):
                branch = current.copy()
                found = list(stricts)
                if first:
                    branch.below(y, x, f'a{i}')
                else:
                    branch.nonnegative(y - x, gap(x, y, f'a{i}'))
                if second:
                    branch.below(-x, y, f'b{i}')
                else:
                    branch.nonnegative(-x - y, gap(y, -x, f'b{i}'))
                name = {(True, True): 'right', (True, False): 'bottom', (False, True): 'top', (False, False): 'left'}[(first, second)]
                low, high = {'right': (h, x), 'bottom': (y, -h), 'top': (h, y), 'left': (x, -h)}[name]
                branch.nonnegative(high - low, gap(low, high, f'side{i}'))
                found.append((low, high, f'side{i}'))
                inner = vertex(i + 1, branch, found)
                out[(first, second)] = (f'M.Membership.when_local(TC, x{i}, y{i}, {goal}, +local{i} => {inject(i, f"local{i}")}, '
                                        f'missing{i} => M.Membership.bind(O.FieldOrder.Strict(TC, {low.bend}, {high.bend}), {goal}, '
                                        f'Unavoidable.{name}_side(TC, x{i}, y{i}, a{i}, b{i}, missing{i}), +side{i} => {inner}))')

        def second_split(first):
            return (f'M.Membership.by_cases(TC, NEG(x{i}), y{i}, {goal}, +b{i} => {out[(first, True)]}, '
                    f'+b{i} => {out[(first, False)]})')
        return f'M.Membership.by_cases(TC, y{i}, x{i}, {goal}, +a{i} => {second_split(True)}, +a{i} => {second_split(False)})'

    return f'''
def Unavoidable.triangle(TPL, {", ".join(params)}) -> {goal}:
{ctx.bindings(2)}  {vertex(0, ctx, [])}
'''


def cross(a, b, c):
    """Twice the oriented area of the triangle a, b, c."""
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def triangle_points():
    """The triangle lemma for a square and three points in container coordinates, with the centre's
    barycentric weights written as oriented areas."""
    ctx = Context()
    cx = ctx.var('cx', 'P.Problem.center_x(F, field, square)')
    cy = ctx.var('cy', 'P.Problem.center_y(F, field, square)')
    c = ctx.var('c', 'P.Problem.cosine(F, field, square)')
    s = ctx.var('s', 'P.Problem.sine(F, field, square)')
    ctx.raw_equation(((c * c + s * s) - 1).text, 'G.Geometry.square_unit(TC, square)')
    px = [ctx.var(f'px{i}', f'px{i}') for i in range(3)]
    py = [ctx.var(f'py{i}', f'py{i}') for i in range(3)]
    points = list(zip(px, py))
    centre = (cx, cy)
    areas = [cross(centre, points[1], points[2]), cross(centre, points[2], points[0]), cross(centre, points[0], points[1])]
    total = cross(points[0], points[1], points[2])
    inverse = ctx.var('i', f'INV({total.bend})')
    ctx.equal(total * inverse, num(1), f'AL.same_transitive(TC, MUL({total.bend}, INV({total.bend})), ONE, R.FieldRing.of_nat(TC, 1n), '
              f'AL.mul_inverse(TC, {total.bend}, O.FieldOrder.lt_of(TC, ZERO, {total.bend}, positive)), S.Scaling.one_is_number(TC))')
    params = [f'+{v}: F' for v in [f'px{i}' for i in range(3)] + [f'py{i}' for i in range(3)]]
    for i in range(3):
        ctx.nonnegative(areas[i], f'weight{i}')
        params.append(f'+weight{i}: LE(ZERO, {areas[i].bend})')
    ctx.nonnegative(total, f'O.FieldOrder.le_of_lt(TC, ZERO, {total.bend}, O.FieldOrder.lt_of(TC, ZERO, {total.bend}, positive))')
    params.append(f'+positive: O.FieldOrder.Strict(TC, ZERO, {total.bend})')
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        d = (px[i] - px[j]) * (px[i] - px[j]) + (py[i] - py[j]) * (py[i] - py[j])
        ctx.below(d, num(1), f'distance{i}{j}')
        params.append(f'+distance{i}{j}: LE({d.bend}, {num(1).bend})')
    ws = [area * inverse for area in areas]
    xs = [T(f'G.Geometry.local_x(TC, square, P.Point{{px{i}, py{i}}})', ((px[i] - cx) * c + (py[i] - cy) * s).text) for i in range(3)]
    ys = [T(f'G.Geometry.local_y(TC, square, P.Point{{px{i}, py{i}}})', ((-(px[i] - cx)) * s + (py[i] - cy) * c).text) for i in range(3)]
    ctx.derive('inverse_nonnegative', num(0), inverse, squares=[inverse])
    facts = [ctx.le(num(0), w) for w in ws]
    weight_sum = ws[0] + ws[1] + ws[2]
    facts += [ctx.le(weight_sum, num(1), products=0), ctx.le(num(1), weight_sum, products=0)]
    for coordinates in (xs, ys):
        balance = ws[0] * coordinates[0] + ws[1] * coordinates[1] + ws[2] * coordinates[2]
        facts += [ctx.le(balance, num(0), products=0), ctx.le(num(0), balance, products=0)]
    for k, (i, j) in enumerate([(0, 1), (0, 2), (1, 2)]):
        d = (xs[i] - xs[j]) * (xs[i] - xs[j]) + (ys[i] - ys[j]) * (ys[i] - ys[j])
        facts.append(ctx.le(d, num(1), products=1, using=[3 + k + 1]))
    goal = containments('square', [f'P.Point{{px{i}, py{i}}}' for i in range(3)], named=True)
    locals_ = [f'G.Geometry.Local<F, field, {xs[i].bend}, {ys[i].bend}>' for i in range(3)]
    found = lambda i, name: f'G.Geometry.local_contains(TC, square, P.Point{{px{i}, py{i}}}, {name})'
    call = f'Unavoidable.triangle(TC, {", ".join(t.bend for t in xs + ys + ws)}, {", ".join(facts)})'
    inner = f'M.Membership.either({locals_[1]}, {locals_[2]}, {goal}, rest, +second => Inr{{Inl{{{found(1, "second")}}}}}, +third => Inr{{Inr{{{found(2, "third")}}}}})'
    return f'''
def Unavoidable.triangle_points(TPL, +square: P.Problem.Square<F, field>, {", ".join(params)}) -> {goal}:
{ctx.bindings(2)}  M.Membership.either({locals_[0]}, Or({locals_[1]}, {locals_[2]}), {goal}, {call}, +first => Inl{{{found(0, "first")}}}, rest => {inner})
'''


def main():
    parts = [HEADER] + [corner(o) for o in CORNERS] + [pair(o) for o in ORIENTATIONS] + [direction(d) for d in DIRECTIONS] + [triangle_core(), triangle_points()]
    (ROOT / 'bend' / 'Unavoidable.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
