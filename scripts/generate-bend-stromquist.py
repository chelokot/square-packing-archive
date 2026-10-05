#!/usr/bin/env python3
"""Write bend/Stromquist.bend: the single-square facts of Stromquist's s(6) argument as bits.

For a square in first-quadrant normal form that fits [0, 3]^2, `Stromquist.row`
records which of the nine key points (1 + i/2, 1 + j/2) it contains. The
lemmas here give the facts that bend/Incidence.bend consumes, following
StromquistSixPoints.lean, StromquistSixAdjacency.lean and StromquistSixCenter.lean.
"""
import importlib.util
from fractions import Fraction

from bend_proof import ROOT, Context, Refuter, T, build, containments, expand, gap, lift, num, one_of

spec = importlib.util.spec_from_file_location('unavoidable', ROOT / 'scripts' / 'generate-bend-unavoidable.py')
U = importlib.util.module_from_spec(spec)
spec.loader.exec_module(U)

HEADER = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Certificate.bend as C
import ./bend-math/Bits.bend as B
import ./Problem.bend as P
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Scaling.bend as S
import ./Membership.bend as M
import ./Unavoidable.bend as U
import ./Incidence.bend as I
'''

H = T('HALF', 'h')
COORDINATES = [num(1), num(1) + H, num(2)]
KEYS = [(COORDINATES[k % 3], COORDINATES[k // 3]) for k in range(9)]
CENTER = 4
THREE = 'R.FieldRing.of_nat(TC, 3n)'
SELF = {'name': 'Stromquist.'}
SQUARE_PARAMS = (f'+square: P.Problem.Square<F, field>, +corners: M.Membership.Corners<F, field, square, {THREE}>, '
                 '+cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square))')
SQUARE_ARGS = 'square, corners, cosine_sign, sine_sign'


def key(k):
    return f"{SELF['name']}key{k}(TC)"


def basics():
    out = ''.join(f'''
def Stromquist.key{k}(TPL) -> P.Problem.Point<F>:
  P.Point{{{x.bend}, {y.bend}}}
''' for k, (x, y) in enumerate(KEYS))
    out += f'''
def Stromquist.row(TPL, +square: P.Problem.Square<F, field>) -> List<&2, Bool>:
  I.Incidence.row({", ".join(f"M.Membership.inside(TC, square, {key(k)})" for k in range(9))})

def Stromquist.unit(TPL, +square: P.Problem.Square<F, field>) ->
  C.Certificate.Both<LE(ADD(ADD(MUL(P.Problem.cosine(F, field, square), P.Problem.cosine(F, field, square)),
    MUL(P.Problem.sine(F, field, square), P.Problem.sine(F, field, square))), NEG(R.FieldRing.of_nat(TC, 1n))), ZERO),
    LE(ZERO, ADD(ADD(MUL(P.Problem.cosine(F, field, square), P.Problem.cosine(F, field, square)),
    MUL(P.Problem.sine(F, field, square), P.Problem.sine(F, field, square))), NEG(R.FieldRing.of_nat(TC, 1n))))>:
  match square:
    case P.Square{{+center, P.Frame{{+c, +s, +ub, +ua}}}}:
      G.Geometry.unit(TC, c, s, ub, ua)
'''
    order = [k for k in range(9) if k != CENTER]
    for position, k in enumerate(order):
        bits = [f'M.Membership.inside(TC, square, {key(j)})' for j in order]
        proof = 'holds'
        tail = bits[position + 1:]
        if tail:
            rest = tail[-1]
            for b in reversed(tail[:-1]):
                rest = f'Bool.or({b}, {rest})'
            proof = f'B.Bits.first({bits[position]}, {rest}, holds)'
        for j in reversed(range(position)):
            rest = bits[-1]
            for b in reversed(bits[j + 1:-1]):
                rest = f'Bool.or({b}, {rest})'
            proof = f'B.Bits.second({bits[j]}, {rest}, {proof})'
        out += f'''
def Stromquist.noncenter_at{k}(TPL, +square: P.Problem.Square<F, field>,
  +holds: B.Bits.Holds(M.Membership.inside(TC, square, {key(k)}))) -> B.Bits.Holds(I.Incidence.noncenter(Stromquist.row(TC, square))):
  {proof}
'''
    return out


class Square(Context):
    """A context about `square` through its accessors, with the unit circle, the signs and the half."""

    def __init__(self, square='square', signs=('cosine_sign', 'sine_sign')):
        super().__init__()
        self.cx = self.var('cx', f'P.Problem.center_x(F, field, {square})')
        self.cy = self.var('cy', f'P.Problem.center_y(F, field, {square})')
        self.c = self.var('c', f'P.Problem.cosine(F, field, {square})')
        self.s = self.var('s', f'P.Problem.sine(F, field, {square})')
        self.h = self.var('h', 'HALF')
        self.raw_equation(((self.c * self.c + self.s * self.s) - 1).text, f"{SELF['name']}unit(TC, {square})")
        self.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
        self.nonnegative(self.c, signs[0])
        self.nonnegative(self.s, signs[1])
        self.fresh = 0

    def name(self, stem):
        self.fresh += 1
        return f'{stem}{self.fresh}'

    def use_fractions(self, values):
        """Declare the fraction variables of these values, with their defining equations."""
        for value in sorted({Fraction(v) for v in values}):
            term = constant(value)
            if term.text != fraction_name(value) or term.text in self.names:
                continue
            FRACTIONS.add(value)
            self.var(term.text, term.bend)
            self.equal(num(value.denominator) * term, num(value.numerator), f"{SELF['name']}{fraction_name(value)}(TC, nontrivial)")

    def corner_facts(self, names):
        """Facts from a matched Corners record whose fields are named <corner>_<side>."""
        signs = {'low_low': (-1, -1), 'low_high': (-1, 1), 'high_low': (1, -1), 'high_high': (1, 1)}
        for name in names:
            a, b = signs[name]
            lx = self.h if a > 0 else -self.h
            ly = self.h if b > 0 else -self.h
            x = self.cx + (lx * self.c - ly * self.s)
            y = self.cy + (lx * self.s + ly * self.c)
            self.nonnegative(x, f'{name}_left')
            self.below(x, num(3), f'{name}_right')
            self.nonnegative(y, f'{name}_bottom')
            self.below(y, num(3), f'{name}_top')

    def local_terms_point(self, point, tag):
        """Variables for the local coordinates of a point given by terms."""
        x, y = point
        polynomial_x = (x - self.cx) * self.c + (y - self.cy) * self.s
        polynomial_y = (-(x - self.cx)) * self.s + (y - self.cy) * self.c
        bend_point = f'P.Point{{{x.bend}, {y.bend}}}'
        lx = self.var(f'lx{tag}', f'G.Geometry.local_x(TC, square, {bend_point})')
        ly = self.var(f'ly{tag}', f'G.Geometry.local_y(TC, square, {bend_point})')
        self.equal(lx, polynomial_x, f'S.Scaling.pair(TC, {lx.bend}, {polynomial_x.bend}, AX.le_reflexive({lx.bend}), AX.le_reflexive({lx.bend}))')
        self.equal(ly, polynomial_y, f'S.Scaling.pair(TC, {ly.bend}, {polynomial_y.bend}, AX.le_reflexive({ly.bend}), AX.le_reflexive({ly.bend}))')
        self.locals_of[(x.text, y.text)] = (lx, ly, bend_point)
        return point

    def local_point(self, values, tag):
        """Variables for the local coordinates of a rational point."""
        point = point_of(values)
        x, y = point
        polynomial_x = (x - self.cx) * self.c + (y - self.cy) * self.s
        polynomial_y = (-(x - self.cx)) * self.s + (y - self.cy) * self.c
        bend_point = f'P.Point{{{x.bend}, {y.bend}}}'
        lx = self.var(f'lx{tag}', f'G.Geometry.local_x(TC, square, {bend_point})')
        ly = self.var(f'ly{tag}', f'G.Geometry.local_y(TC, square, {bend_point})')
        self.equal(lx, polynomial_x, f'S.Scaling.pair(TC, {lx.bend}, {polynomial_x.bend}, AX.le_reflexive({lx.bend}), AX.le_reflexive({lx.bend}))')
        self.equal(ly, polynomial_y, f'S.Scaling.pair(TC, {ly.bend}, {polynomial_y.bend}, AX.le_reflexive({ly.bend}), AX.le_reflexive({ly.bend}))')
        self.locals_of[(x.text, y.text)] = (lx, ly, bend_point)
        return point

    def point(self, p):
        return (p[0].text if isinstance(p[0], T) else p[0], p[1].text)


def fraction_name(value):
    return f'r{value.numerator}_{value.denominator}'


def constant(value):
    """The canonical field term for a rational coordinate; fractions other than halves are certificate variables."""
    value = Fraction(value)
    for k, term in enumerate(COORDINATES):
        if value == Fraction(2 + k, 2):
            return term
    if value.denominator == 1:
        return num(value.numerator)
    assert value > 0, value
    return T(f'MUL(R.FieldRing.of_nat(TC, {value.numerator}n), INV(R.FieldRing.of_nat(TC, {value.denominator}n)))', fraction_name(value))


FRACTIONS = set()


def fraction_lemma(value):
    ctx = Context()
    i = ctx.var('i', f'INV(R.FieldRing.of_nat(TC, {value.denominator}n))')
    ctx.equal(num(value.denominator) * i, num(1), f'Stromquist.inverse{value.denominator}(TC, nontrivial)')
    term = num(value.numerator) * i
    same = ctx.same(num(value.denominator) * term, num(value.numerator))
    return f'''
def Stromquist.{fraction_name(value)}(TPL, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)) ->
  SAME(MUL(R.FieldRing.of_nat(TC, {value.denominator}n), {constant(value).bend}), R.FieldRing.of_nat(TC, {value.numerator}n)):
  {same}
'''


def point_of(values):
    return (constant(values[0]), constant(values[1]))


def inverse_lemma(m):
    ctx = Context()
    bad_value = ctx.var('unused', 'ZERO')
    ctx.below(num(m), num(0), 'bad')
    contradiction = ctx.le(num(1), num(0))
    return f'''
def Stromquist.inverse{m}(TPL, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)) ->
  SAME(MUL(R.FieldRing.of_nat(TC, {m}n), INV(R.FieldRing.of_nat(TC, {m}n))), R.FieldRing.of_nat(TC, 1n)):
  AL.same_transitive(TC, MUL(R.FieldRing.of_nat(TC, {m}n), INV(R.FieldRing.of_nat(TC, {m}n))), ONE, R.FieldRing.of_nat(TC, 1n),
    AL.mul_inverse(TC, R.FieldRing.of_nat(TC, {m}n), +bad => O.FieldOrder.lt_of(TC, ZERO, ONE, nontrivial)(
      AL.le_respects(TC, R.FieldRing.of_nat(TC, 1n), ZERO, ONE, ZERO, {contradiction},
        AL.same_symmetric(TC, ONE, R.FieldRing.of_nat(TC, 1n), S.Scaling.one_is_number(TC)), AL.same_reflexive(TC, ZERO)))),
    S.Scaling.one_is_number(TC))
'''


def rational(value):
    value = Fraction(value)
    if value == 0:
        return num(0)
    power = 0
    denominator = value.denominator
    while denominator % 2 == 0:
        denominator //= 2
        power += 1
    assert denominator == 1, value
    out = num(abs(value.numerator))
    for _ in range(power):
        out = out * H
    return out if value > 0 else -out


def coefficient(value):
    value = Fraction(value)
    term = constant(abs(value))
    return term if value > 0 else -term


def affine(free, x_coefficient, y_coefficient, cx, cy):
    out = coefficient(free) if free else None
    for c, v in ((x_coefficient, cx), (y_coefficient, cy)):
        if c:
            out = coefficient(c) * v if out is None else out + coefficient(c) * v
    return out if out is not None else num(0)


def value(t):
    return Fraction(t.text.replace('h', '(1/2)')) if False else None


KEY_VALUES = [(Fraction(1) + Fraction(k % 3, 2), Fraction(1) + Fraction(k // 3, 2)) for k in range(9)]


def barycentric(points):
    """Affine weights (constant, cx, cy) of the centre in the triangle of the given key values."""
    (x0, y0), (x1, y1), (x2, y2) = points
    area = (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)
    out = []
    for (ax, ay), (bx, by) in [((x1, y1), (x2, y2)), ((x2, y2), (x0, y0)), ((x0, y0), (x1, y1))]:
        constant = (ax * by - ay * bx) / area
        out.append((constant, (ay - by) / area, (bx - ax) / area))
    return out


class Leaves:
    """Calls of the lemmas in bend/Unavoidable.bend that end in a fact about the bits of `square`."""

    def __init__(self, goal, convert):
        self.goal = goal
        self.convert = convert

    def finish(self, results, call):
        """`call` proves Or(C(square, p0), Or(...)); `results` are key indices; convert each to the goal."""
        def chain(i):
            containment = f'P.Problem.Containment<F, field, square, {results[i][1]}>'
            if i == len(results) - 1:
                return None, containment
            rest_type = chain(i + 1)[1]
            return None, f'Or({containment}, {rest_type})'

        def eliminate(i, term):
            if i == len(results) - 1:
                return f'M.Membership.bind({chain(i)[1]}, {self.goal}, {term}, +found{i} => {self.convert(results[i], f"found{i}")})'
            left = f'P.Problem.Containment<F, field, square, {results[i][1]}>'
            right = chain(i + 1)[1]
            return (f'M.Membership.either({left}, {right}, {self.goal}, {term}, +found{i} => {self.convert(results[i], f"found{i}")}, '
                    f'+rest{i} => {eliminate(i + 1, f"rest{i}") if i + 1 < len(results) - 1 else self.convert(results[i + 1], f"rest{i}")})')
        if len(results) == 1:
            return self.convert(results[0], call)
        return eliminate(0, call)


def lemma_hyps(ctx, hyps):
    """Certificates for the hypotheses of a lemma call; the frame bounds may need squares near the diagonal."""
    out = []
    for a, b in hyps:
        proof = ctx.le(a, b, required=False)
        if proof is None:
            proof = ctx.le(a, b, squares=[ctx.c - ctx.s])
        out.append(proof)
    return ', '.join(out)


def corner_call(ctx, leaves, name, k):
    tx, ty = KEYS[k]
    hyps, _ = U.corner_spec(name)(ctx, {'tx': tx, 'ty': ty})
    call = f'U.Unavoidable.{name}_corner(TC, {SQUARE_ARGS}, {tx.bend}, {ty.bend}, {lemma_hyps(ctx, hyps)})'
    return leaves.finish([(k, key(k))], call)


def pair_call(ctx, leaves, side, first, second):
    (px, py), (qx, qy) = KEYS[first], KEYS[second]
    names = U.PAIR_PARAMS[side]
    values = {'px': px, 'py': py, 'qx': qx, 'qy': qy}
    hyps, _ = U.pair_spec(side)(ctx, values)
    args = ', '.join(values[n].bend for n in names)
    call = f'U.Unavoidable.{side}_pair(TC, {SQUARE_ARGS}, {args}, {lemma_hyps(ctx, hyps)})'
    return leaves.finish([(first, key(first)), (second, key(second))], call)


def cross(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def triangle_points_call(ctx, goal, vertices, terms, convert):
    """U.Unavoidable.triangle_points for vertices given as values and terms; found vertices go to convert(index, containment)."""
    centre = (ctx.cx, ctx.cy)
    points = list(terms)
    if cross(*[(Fraction(v[0]), Fraction(v[1])) for v in vertices]) < 0:
        raise ValueError(f'clockwise triangle {vertices}')
    areas = [cross(centre, points[1], points[2]), cross(centre, points[2], points[0]), cross(centre, points[0], points[1])]
    total = cross(points[0], points[1], points[2])
    facts = [ctx.le(num(0), area) for area in areas]
    bad = ctx.copy()
    bad.below(total, num(0), 'not_positive')
    facts.append(f'O.FieldOrder.strict_of(TC, ZERO, {total.bend}, +not_positive => O.FieldOrder.lt_of(TC, ZERO, ONE, nontrivial)('
                 f'AL.le_respects(TC, R.FieldRing.of_nat(TC, 1n), ZERO, ONE, ZERO, {bad.le(num(1), num(0))}, '
                 f'AL.same_symmetric(TC, ONE, R.FieldRing.of_nat(TC, 1n), S.Scaling.one_is_number(TC)), AL.same_reflexive(TC, ZERO))))')
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        d = (points[i][0] - points[j][0]) * (points[i][0] - points[j][0]) + (points[i][1] - points[j][1]) * (points[i][1] - points[j][1])
        facts.append(ctx.le(d, num(1)))
    coordinates = [p[0].bend for p in points] + [p[1].bend for p in points]
    call = f'U.Unavoidable.triangle_points(TC, square, {", ".join(coordinates)}, {", ".join(facts)})'
    kinds = [f'P.Problem.Containment<F, field, square, P.Point{{{p[0].bend}, {p[1].bend}}}>' for p in points]
    inner = (f'M.Membership.either({kinds[1]}, {kinds[2]}, {goal}, rest, +second => {convert(1, "second")}, '
             f'+third => {convert(2, "third")})')
    return f'M.Membership.either({kinds[0]}, Or({kinds[1]}, {kinds[2]}), {goal}, {call}, +first => {convert(0, "first")}, rest => {inner})'


def counterclockwise(vertices):
    values = [(Fraction(v[0]), Fraction(v[1])) for v in vertices]
    return list(vertices) if cross(*values) > 0 else [vertices[0], vertices[2], vertices[1]]


def triangle_call(ctx, leaves, vertices):
    vertices = counterclockwise(vertices) if False else vertices
    order = counterclockwise([KEY_VALUES[k] for k in vertices])
    vertices = [KEY_VALUES.index(v) for v in order]
    results = [(k, key(k)) for k in vertices]
    return triangle_points_call(ctx, leaves.goal, [KEY_VALUES[k] for k in vertices], [KEYS[k] for k in vertices],
                                lambda i, name: leaves.convert(results[i], name))


REFLECT = {
    'id': (lambda x, y: (x, y), lambda k: k),
    'rx': (lambda x, y: (3 - x, y), lambda k: 3 * (k // 3) + 2 - k % 3),
    'ry': (lambda x, y: (x, 3 - y), lambda k: 3 * (2 - k // 3) + k % 3),
    'rxy': (lambda x, y: (3 - x, 3 - y), lambda k: 8 - k),
}
CORNER_OF = {0: 'low_left', 2: 'low_right', 6: 'high_left', 8: 'high_right'}


def side_of(first, second):
    a, b = sorted((first, second))
    if a // 3 == b // 3:
        return ('bottom' if a // 3 == 0 else 'top'), a, b
    return ('left' if a % 3 == 0 else 'right'), a, b


def emit(node, reflection, ctx, leaves):
    place, relabel = REFLECT[reflection]
    kind = node[0]
    if kind == 'split':
        _, condition, yes, no = node
        bx, by = place(ctx.cx, ctx.cy)
        a, b = condition(bx, by)
        name = ctx.name('case')
        low = ctx.copy()
        low.below(a, b, name)
        high = ctx.copy()
        high.nonnegative(a - b, gap(b, a, name))
        return (f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {leaves.goal}, +{name} => {emit(yes, reflection, low, leaves)}, '
                f'+{name} => {emit(no, reflection, high, leaves)})')
    if kind == 'corner':
        k = relabel(node[1])
        return corner_call(ctx, leaves, CORNER_OF[k], k)
    if kind == 'pair':
        side, first, second = side_of(relabel(node[1]), relabel(node[2]))
        return pair_call(ctx, leaves, side, first, second)
    if kind == 'triangle':
        return triangle_call(ctx, leaves, [relabel(k) for k in node[1]])
    raise ValueError(kind)


def split(condition, yes, no):
    return ('split', condition, yes, no)


LOWER_LEFT = split(lambda x, y: (x, num(1)),
                   split(lambda x, y: (y, num(1)), ('corner', 0), ('pair', 0, 3)),
                   split(lambda x, y: (y, num(1)), ('pair', 0, 1),
                         split(lambda x, y: (x + y, num(2) + H), ('triangle', [0, 1, 3]), ('triangle', [3, 1, 7]))))


def perimeter():
    goal = 'B.Bits.Holds(I.Incidence.noncenter(Stromquist.row(TC, square)))'

    def convert(result, containment):
        k, point = result
        return f'Stromquist.noncenter_at{k}(TC, square, M.Membership.inside_of(TC, square, {point}, {containment}))'
    ctx = Square()
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.derive('sum_at_least', num(1), ctx.c + ctx.s)
    ctx.derive('sum_at_most', ctx.c + ctx.s, num(1) + H, squares=[ctx.c - ctx.s])
    ctx.freeze('known')
    leaves = Leaves(goal, convert)
    quarter = num(1) + H
    tree = split(lambda x, y: (x, quarter),
                 split(lambda x, y: (y, quarter), ('quadrant', 'id'), ('quadrant', 'ry')),
                 split(lambda x, y: (y, quarter), ('quadrant', 'rx'), ('quadrant', 'rxy')))

    def outer(node, current):
        if node[0] == 'quadrant':
            return emit(LOWER_LEFT, node[1], current, leaves)
        _, condition, yes, no = node
        a, b = condition(current.cx, current.cy)
        name = current.name('half')
        low = current.copy()
        low.below(a, b, name)
        high = current.copy()
        high.nonnegative(a - b, gap(b, a, name))
        return f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {goal}, +{name} => {outer(yes, low)}, +{name} => {outer(no, high)})'
    body = outer(tree, ctx)
    return f'''
def Stromquist.perimeter(TPL, {SQUARE_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)) -> {goal}:
{ctx.bindings(2)}  {body}
'''


spec = importlib.util.spec_from_file_location('incidence', ROOT / 'scripts' / 'generate-bend-incidence.py')
INCIDENCE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(INCIDENCE)


def local_terms(ctx, k, tag):
    """Variables for the local coordinates of key k in `square`."""
    x, y = KEYS[k]
    polynomial_x = (x - ctx.cx) * ctx.c + (y - ctx.cy) * ctx.s
    polynomial_y = (-(x - ctx.cx)) * ctx.s + (y - ctx.cy) * ctx.c
    lx = ctx.var(f'lx{tag}', f'G.Geometry.local_x(TC, square, {key(k)})')
    ly = ctx.var(f'ly{tag}', f'G.Geometry.local_y(TC, square, {key(k)})')
    ctx.equal(lx, polynomial_x, f'S.Scaling.pair(TC, {lx.bend}, {polynomial_x.bend}, AX.le_reflexive({lx.bend}), AX.le_reflexive({lx.bend}))')
    ctx.equal(ly, polynomial_y, f'S.Scaling.pair(TC, {ly.bend}, {polynomial_y.bend}, AX.le_reflexive({ly.bend}), AX.le_reflexive({ly.bend}))')
    ctx.locals_of[(KEYS[k][0].text, KEYS[k][1].text)] = (lx, ly, key(k))
    return lx, ly


def clause(first, second, others):
    """A square holding keys `first` and `second` holds one of `others` (StromquistSixAdjacency.lean)."""
    ctx = Square()
    for tag, k in (('a', first), ('b', second)):
        lx, ly = local_terms(ctx, k, tag)
        ctx.below(lx, ctx.h, f'{tag}_x_at_most')
        ctx.below(-ctx.h, lx, f'{tag}_x_at_least')
        ctx.below(ly, ctx.h, f'{tag}_y_at_most')
        ctx.below(-ctx.h, ly, f'{tag}_y_at_least')
    for k in others:
        local_terms(ctx, k, f'o{k}')
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.freeze('known')
    points = [KEYS[k] for k in others]
    proof = one_of(ctx, 'square', points, Refuter(squares=[1 - ctx.s, 1 - ctx.c]))
    local = lambda k: f'G.Geometry.Local<F, field, G.Geometry.local_x(TC, square, {key(k)}), G.Geometry.local_y(TC, square, {key(k)})>'
    goal = containments('square', [key(k) for k in others], named=True)
    return f'''
def Stromquist.clause{first}_{second}(TPL, {SQUARE_PARAMS}, +first: {local(first)}, +second: {local(second)}) -> {goal}:
  match first second:
    case G.Local{{+a_x_at_most, +a_x_at_least, +a_y_at_most, +a_y_at_least}} G.Local{{+b_x_at_most, +b_x_at_least, +b_y_at_most, +b_y_at_least}}:
{ctx.bindings(6)}      {proof}
'''


def inside(k):
    return f'M.Membership.inside(TC, square, {key(k)})'


def ors(bits):
    out = bits[-1]
    for b in reversed(bits[:-1]):
        out = f'Bool.or({b}, {out})'
    return out


def ands(bits):
    out = bits[-1]
    for b in reversed(bits[:-1]):
        out = f'Bool.and({b}, {out})'
    return out


def holds_one(others, containment_choice):
    """From Or(C(x0), Or(...)) to Holds of the or-chain of their bits."""
    bits = [inside(k) for k in others]
    goal = f'B.Bits.Holds({ors(bits)})'

    def go(i, term):
        here = f'M.Membership.inside_of(TC, square, {key(others[i])}, {term})'
        if i == len(others) - 1:
            return here
        rest = ors(bits[i + 1:])
        left = f'P.Problem.Containment<F, field, square, {key(others[i])}>'
        right = containments('square', [key(k) for k in others[i + 1:]], named=True)
        return (f'M.Membership.either({left}, {right}, {goal}, {term}, +found => B.Bits.first({bits[i]}, {rest}, {here.replace(term, "found")}), '
                f'+later => B.Bits.second({bits[i]}, {rest}, {go(i + 1, "later")}))')
    return go(0, containment_choice)


def pair_ok():
    clauses = []
    for (a, b), xs in INCIDENCE.PAIRS.items():
        local = lambda k, holds: (f'G.Geometry.contains_local(TC, square, {key(k)}, '
                                  f'M.Membership.contains(TC, square, {key(k)}, {holds}))')
        call = f'Stromquist.clause{a}_{b}(TC, {SQUARE_ARGS}, {local(a, "first")}, {local(b, "second")})'
        conclude = f'+first => +second => {holds_one(xs, call)}'
        clauses.append((f'Bool.or(Bool.not(Bool.and({inside(a)}, {inside(b)})), {ors([inside(k) for k in xs])})',
                        f'B.Bits.implies({inside(a)}, {inside(b)}, {ors([inside(k) for k in xs])}, {conclude})'))
    proof = clauses[-1][1]
    for i in reversed(range(len(clauses) - 1)):
        proof = f'B.Bits.both({clauses[i][0]}, {ands([c for c, _ in clauses[i + 1:]])}, {clauses[i][1]}, {proof})'
    return f'''
def Stromquist.pair_ok(TPL, {SQUARE_PARAMS}) -> B.Bits.Holds(I.Incidence.pair_ok(Stromquist.row(TC, square))):
  {proof}
'''


def contained(ctx, values, tag):
    """Facts that a point with local variables lies in the unit square around the centre."""
    point = ctx.local_point(values, tag)
    lx, ly, _ = ctx.locals_of[(point[0].text, point[1].text)]
    ctx.below(lx, ctx.h, f'{tag}_x_at_most')
    ctx.below(-ctx.h, lx, f'{tag}_x_at_least')
    ctx.below(ly, ctx.h, f'{tag}_y_at_most')
    ctx.below(-ctx.h, ly, f'{tag}_y_at_least')
    return point


def local_type(point):
    p = f'P.Point{{{point[0].bend}, {point[1].bend}}}'
    return f'G.Geometry.Local<F, field, G.Geometry.local_x(TC, square, {p}), G.Geometry.local_y(TC, square, {p})>'


def local_pattern(tag):
    return f'G.Local{{+{tag}_x_at_most, +{tag}_x_at_least, +{tag}_y_at_most, +{tag}_y_at_least}}'


NORTH = {'center': (Fraction(3, 2), Fraction(3, 2)), 'neighbour': (Fraction(3, 2), Fraction(2)),
         'missing': [(Fraction(1), Fraction(3, 2)), (Fraction(2), Fraction(3, 2)), (Fraction(1), Fraction(2)), (Fraction(2), Fraction(2))],
         'extra': [(Fraction(1), Fraction(17, 10)), (Fraction(2), Fraction(17, 10))]}


def center_base(index):
    """StromquistSixCenter.lean for the north neighbour: the square holds an extra point near the top."""
    ctx = Square()
    ctx.use_fractions([Fraction(3, 5), Fraction(4, 5)] + [v for point in NORTH['extra'] for v in point])
    center = contained(ctx, NORTH['center'], 'center')
    neighbour = contained(ctx, NORTH['neighbour'], 'neighbour')
    missing = [ctx.local_point(values, f'm{k}') for k, values in enumerate(NORTH['missing'])]
    target = ctx.local_point(NORTH['extra'][index], 'target')
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.freeze('known')
    c, s = ctx.c, ctx.s
    fifth = lambda n: constant(Fraction(n, 5))
    outside = [('outside', 'square', point, f'out{k}') for k, point in enumerate(missing)]
    ordered = outside + [('lt', 'large', num(2), c + 2 * s), ('le_refute', 'lower', fifth(3), s),
                         ('le', 'tangent', fifth(4) * c + fifth(3) * s, num(1), [c - fifth(4), s - fifth(3)])]
    swapped = outside + [('lt', 'large', num(2), s + 2 * c), ('le_refute', 'lower', fifth(3), c),
                         ('le', 'tangent', fifth(3) * c + fifth(4) * s, num(1), [c - fifth(3), s - fifth(4)])]
    goal = f'P.Problem.Containment<F, field, square, P.Point{{{target[0].bend}, {target[1].bend}}}>'
    refuter = Refuter(squares=[1 - c, 1 - s])
    finish = lambda current, stricts: one_of(current, 'square', [target], refuter, stricts)
    proof = build(ctx, [('cases', 'ordered', s, c, ordered, swapped)], goal, refuter, finish)
    outs = ', '.join(f'+out{k}: B.Bits.Holds(Bool.not(M.Membership.inside(TC, square, P.Point{{{p[0].bend}, {p[1].bend}}})))'
                     for k, p in enumerate(missing))
    return f'''
def Stromquist.center_base{index}(TPL, {SQUARE_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE),
  +center: {local_type(center)}, +neighbour: {local_type(neighbour)}, {outs}) -> {goal}:
  match center neighbour:
    case {local_pattern('center')} {local_pattern('neighbour')}:
{ctx.bindings(6)}      {proof}
'''


OPS = {
    'swap': {'square': lambda q: f'Y.Symmetry.swap(TC, {q})', 'values': lambda x, y: (y, x), 'terms': lambda x, y: (y, x),
             'point': lambda p: f'Y.Symmetry.swap_point(F, {p})',
             'contains': lambda q, p, c: f'Y.Symmetry.swap_contains(TC, {q}, {p}, {c})',
             'back': lambda q, p, c: f'Y.Symmetry.swap_contains_back(TC, {q}, {p}, {c})',
             'corners': lambda q, k: f'M.Membership.swap_corners(TC, {q}, {THREE}, {k})'},
    'reflect_x': {'square': lambda q: f'Y.Symmetry.reflect_x(TC, {THREE}, {q})', 'values': lambda x, y: (3 - x, y),
                  'terms': lambda x, y: (num(3) - x, y), 'point': lambda p: f'Y.Symmetry.reflect_x_point(TC, {THREE}, {p})',
                  'contains': lambda q, p, c: f'Y.Symmetry.reflect_x_contains(TC, {THREE}, {q}, {p}, {c})',
                  'back': lambda q, p, c: f'Y.Symmetry.reflect_x_contains_back(TC, {THREE}, {q}, {p}, {c})',
                  'corners': lambda q, k: f'M.Membership.reflect_x_corners(TC, {q}, {THREE}, {k})'},
    'reflect_y': {'square': lambda q: f'Y.Symmetry.reflect_y(TC, {THREE}, {q})', 'values': lambda x, y: (x, 3 - y),
                  'terms': lambda x, y: (x, num(3) - y), 'point': lambda p: f'Y.Symmetry.reflect_y_point(TC, {THREE}, {p})',
                  'contains': lambda q, p, c: f'Y.Symmetry.reflect_y_contains(TC, {THREE}, {q}, {p}, {c})',
                  'back': lambda q, p, c: f'Y.Symmetry.reflect_y_contains_back(TC, {THREE}, {q}, {p}, {c})',
                  'corners': lambda q, k: f'M.Membership.reflect_y_corners(TC, {q}, {THREE}, {k})'},
}


def point_term(values):
    x, y = point_of(values)
    return f'P.Point{{{x.bend}, {y.bend}}}'


class Transport:
    """Move facts about `square` along a chain of symmetries of [0, 3]^2 and into first-quadrant normal form."""

    def __init__(self, ops, ctx, square='square', corners='corners'):
        self.ops = ops
        self.ctx = ctx
        self.base = square
        squares = [square]
        for op in ops:
            squares.append(OPS[op]['square'](squares[-1]))
        self.squares = squares
        self.moved = squares[-1]
        self.normal = f'Y.Symmetry.first_quadrant(TC, {self.moved})'
        for q, op in zip(squares, ops):
            corners = OPS[op]['corners'](q, corners)
        self.base_corners = corners
        self.corners = f'M.Membership.first_quadrant_corners(TC, {self.moved}, {THREE}, {corners})'
        signs = f'Y.Symmetry.first_quadrant_signs(TC, {self.moved})'
        cosine = f'LE(ZERO, P.Problem.cosine(F, field, {self.normal}))'
        sine = f'LE(ZERO, P.Problem.sine(F, field, {self.normal}))'
        self.signs = (f'C.Certificate.first({cosine}, {sine}, {signs})', f'C.Certificate.second({cosine}, {sine}, {signs})')

    def image(self, values):
        for op in self.ops:
            values = OPS[op]['values'](*values)
        return values

    def preimage(self, values):
        for op in reversed(self.ops):
            values = OPS[op]['values'](*values)
        return values

    def move(self, square, source, target, containment):
        """Containment(square, source) to Containment(square, target) for points with equal coordinates."""
        (sx, sy), (tx, ty) = source, target
        proofs = [self.ctx.le(sx, tx), self.ctx.le(tx, sx), self.ctx.le(sy, ty), self.ctx.le(ty, sy)]
        return (f'M.Membership.moved(TC, {square}, P.Point{{{sx.bend}, {sy.bend}}}, P.Point{{{tx.bend}, {ty.bend}}}, '
                f'{", ".join(proofs)}, {containment})')

    def forward(self, values, containment):
        """Containment(square, point) to Containment(normal, image point)."""
        terms = point_of(values)
        current = containment
        for q, op in zip(self.squares, self.ops):
            current = OPS[op]['contains'](q, f'P.Point{{{terms[0].bend}, {terms[1].bend}}}', current)
            terms = OPS[op]['terms'](*terms)
        current = f'Y.Symmetry.first_quadrant_contains(TC, {self.moved}, P.Point{{{terms[0].bend}, {terms[1].bend}}}, {current})'
        return self.move(self.normal, terms, point_of(self.image(values)), current)

    def backward(self, values, containment):
        """Containment(normal, point) to Containment(square, preimage point)."""
        terms = point_of(values)
        current = f'Y.Symmetry.first_quadrant_contains_back(TC, {self.moved}, P.Point{{{terms[0].bend}, {terms[1].bend}}}, {containment})'
        for q, op in reversed(list(zip(self.squares, self.ops))):
            current = OPS[op]['back'](q, f'P.Point{{{terms[0].bend}, {terms[1].bend}}}', current)
            terms = OPS[op]['terms'](*terms)
        return self.move(self.base, terms, point_of(self.preimage(values)), current)

    def backward_any(self, point, containment):
        """Containment(normal, point) to Containment(base square, preimage of point) for any point term."""
        current = f'Y.Symmetry.first_quadrant_contains_back(TC, {self.moved}, {point}, {containment})'
        for q, op in reversed(list(zip(self.squares, self.ops))):
            current = OPS[op]['back'](q, point, current)
            point = OPS[op]['point'](point)
        return current, point

    def outside(self, values, out):
        """Holds(not inside(square, point)) to Holds(not inside(normal, image point))."""
        image = self.image(values)
        back = self.backward(image, 'moved_inside')
        return (f'M.Membership.outside_of(TC, {self.base}, {point_term(values)}, {self.normal}, {point_term(image)}, '
                f'moved_inside => {back}, {out})')


CENTER_ORIENTATIONS = {'north': [], 'south': ['reflect_y'], 'east': ['swap'], 'west': ['swap', 'reflect_y']}


def center_transport(orientation, index):
    ops = CENTER_ORIENTATIONS[orientation]
    ctx = Square()
    transport = Transport(ops, ctx)
    ctx.use_fractions([v for point in NORTH['extra'] for v in point + transport.preimage(point)])
    actual = {key: transport.preimage(NORTH[key]) for key in ('center', 'neighbour')}
    missing = [transport.preimage(values) for values in NORTH['missing']]
    extra = transport.preimage(NORTH['extra'][index])
    goal = f'P.Problem.Containment<F, field, square, {point_term(extra)}>'
    local = lambda values, c: f'G.Geometry.contains_local(TC, {transport.normal}, {point_term(transport.image(values))}, {c})'
    arguments = [transport.normal, transport.corners, transport.signs[0], transport.signs[1], 'nontrivial',
                 local(actual['center'], transport.forward(actual['center'], 'center')),
                 local(actual['neighbour'], transport.forward(actual['neighbour'], 'neighbour'))]
    arguments += [transport.outside(values, f'out{k}') for k, values in enumerate(missing)]
    call = f'Stromquist.center_base{index}(TC, {", ".join(arguments)})'
    outs = ', '.join(f'+out{k}: B.Bits.Holds(Bool.not(M.Membership.inside(TC, square, {point_term(v)})))' for k, v in enumerate(missing))
    return f'''
def Stromquist.center_{orientation}{index}(TPL, {SQUARE_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE),
  +center: P.Problem.Containment<F, field, square, {point_term(actual['center'])}>,
  +neighbour: P.Problem.Containment<F, field, square, {point_term(actual['neighbour'])}>, {outs}) -> {goal}:
  {transport.backward(NORTH['extra'][index], call)}
'''


EXTRA = [(1, 2), (Fraction(3, 2), 2), (2, 2), (1, Fraction(17, 10)), (2, Fraction(17, 10)), (Fraction(3, 2), Fraction(3, 2)),
         (1, Fraction(9, 10)), (2, Fraction(9, 10))]
EXTRA = [(Fraction(x), Fraction(y)) for x, y in EXTRA]


def mirror(values):
    return (3 - values[0], values[1])


def below_line(first, second):
    """The condition that the centre lies on or below the line through two points with different x."""
    a, b = sorted((first, second))
    return lambda x, y: (cross(point_of(a), point_of(b), (x, y)), num(0))


def extra_tree(flip):
    """Lean's extraPoints_unavoidable_left, mirrored to the right half when `flip`."""
    e = [mirror(v) if flip else v for v in EXTRA]
    inner_x = (lambda x: num(3) - x) if flip else (lambda x: x)
    return split(lambda x, y: (y, constant(Fraction(9, 10))),
                 split(lambda x, y: (inner_x(x), num(1)), ('corner', e[6]), ('pair', e[6], e[7])),
                 split(lambda x, y: (num(2), y),
                       split(lambda x, y: (inner_x(x), num(1)), ('corner', e[0]), ('pair', e[0], e[1])),
                       split(lambda x, y: (inner_x(x), num(1)),
                             split(lambda x, y: (y, constant(Fraction(17, 10))), ('pair', e[6], e[3]), ('pair', e[3], e[0])),
                             split(below_line(e[6], e[5]), ('triangle', [e[6], e[7], e[5]]),
                                   split(below_line(e[3], e[5]), ('triangle', [e[6], e[5], e[3]]),
                                         split(below_line(e[3], e[1]), ('triangle', [e[3], e[5], e[1]]), ('triangle', [e[3], e[1], e[0]])))))))


def side_of_values(first, second):
    if first[1] == second[1]:
        a, b = sorted((first, second))
        return ('bottom' if a[1] <= Fraction(3, 2) else 'top'), a, b
    a, b = sorted((first, second), key=lambda v: v[1])
    return ('left' if a[0] <= Fraction(3, 2) else 'right'), a, b


def corner_name(values):
    return {(True, True): 'low_left', (False, True): 'low_right', (True, False): 'high_left', (False, False): 'high_right'}[
        (values[0] <= Fraction(3, 2), values[1] <= Fraction(3, 2))]


def point_leaf(node, ctx, goal, convert):
    """A corner, pair or triangle lemma for rational points, each found point passed to convert(values, containment)."""
    kind = node[0]
    if kind == 'corner':
        values = node[1]
        tx, ty = point_of(values)
        name = corner_name(values)
        hyps, _ = U.corner_spec(name)(ctx, {'tx': tx, 'ty': ty})
        return convert(values, f'U.Unavoidable.{name}_corner(TC, {SQUARE_ARGS}, {tx.bend}, {ty.bend}, {lemma_hyps(ctx, hyps)})')
    if kind == 'pair':
        side, first, second = side_of_values(node[1], node[2])
        (px, py), (qx, qy) = point_of(first), point_of(second)
        values = {'px': px, 'py': py, 'qx': qx, 'qy': qy}
        hyps, _ = U.pair_spec(side)(ctx, values)
        args = ', '.join(values[n].bend for n in U.PAIR_PARAMS[side])
        call = f'U.Unavoidable.{side}_pair(TC, {SQUARE_ARGS}, {args}, {lemma_hyps(ctx, hyps)})'
        a, b = point_term(first), point_term(second)
        return (f'M.Membership.either(P.Problem.Containment<F, field, square, {a}>, P.Problem.Containment<F, field, square, {b}>, {goal}, '
                f'{call}, +first => {convert(first, "first")}, +second => {convert(second, "second")})')
    if kind == 'triangle':
        vertices = counterclockwise(node[1])
        return triangle_points_call(ctx, goal, vertices, [point_of(v) for v in vertices], lambda i, name: convert(vertices[i], name))
    raise ValueError(kind)


def emit_points(node, ctx, goal, convert):
    if node[0] != 'split':
        return point_leaf(node, ctx, goal, convert)
    _, condition, yes, no = node
    a, b = condition(ctx.cx, ctx.cy)
    name = ctx.name('case')
    low = ctx.copy()
    low.below(a, b, name)
    high = ctx.copy()
    high.nonnegative(a - b, gap(b, a, name))
    return (f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {goal}, +{name} => {emit_points(yes, low, goal, convert)}, '
            f'+{name} => {emit_points(no, high, goal, convert)})')


def or_containments(points):
    return containments('square', [point_term(v) for v in points], named=True)


def inject(index, count, proof):
    out = proof if index == count - 1 else f'Inl{{{proof}}}'
    for _ in range(index):
        out = f'Inr{{{out}}}'
    return out


def extra_base():
    ctx = Square()
    ctx.use_fractions([v for point in EXTRA for v in point + mirror(point)] + [Fraction(17, 12)])
    ctx.freeze('base')
    ctx.derive('cosine_at_most', ctx.c, num(1), squares=[ctx.s, 1 - ctx.c])
    ctx.derive('sine_at_most', ctx.s, num(1), squares=[ctx.c, 1 - ctx.s])
    ctx.derive('sum_at_least', num(1), ctx.c + ctx.s)
    ctx.derive('sum_at_most', ctx.c + ctx.s, num(1) + H, squares=[ctx.c - ctx.s])
    ctx.derive('sum_below_root', ctx.c + ctx.s, constant(Fraction(17, 12)), squares=[ctx.c - ctx.s, ctx.c + ctx.s - constant(Fraction(17, 12))])
    ctx.freeze('known')
    goal = or_containments(EXTRA)

    def convert(values, containment):
        index = EXTRA.index(values) if values in EXTRA else EXTRA.index(mirror(values))
        return inject(EXTRA.index(values), len(EXTRA), containment)
    half = constant(Fraction(3, 2))
    body = emit_points(split(lambda x, y: (x, half), extra_tree(False), extra_tree(True)), ctx, goal, convert)
    return f'''
def Stromquist.extra_base(TPL, {SQUARE_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)) -> {goal}:
{ctx.bindings(2)}  {body}
'''


def extra_points(orientation):
    """The extra points of an orientation, in the order of EXTRA."""
    transport = Transport(CENTER_ORIENTATIONS[orientation], None)
    return [transport.preimage(values) for values in EXTRA]


def extra_rows():
    out = ''
    for orientation in CENTER_ORIENTATIONS:
        bits = ', '.join(f'M.Membership.inside(TC, square, {point_term(v)})' for v in extra_points(orientation))
        out += f'''
def Stromquist.extra_row_{orientation}(TPL, +square: P.Problem.Square<F, field>) -> List<&2, Bool>:
  I.Incidence.row8({bits})
'''
    return out


def or_at(bits, position, proof):
    """Holds of the or-chain of bits from Holds of one of them."""
    tail = bits[position + 1:]
    if tail:
        proof = f'B.Bits.first({bits[position]}, {ors(tail)}, {proof})'
    for j in reversed(range(position)):
        proof = f'B.Bits.second({bits[j]}, {ors(bits[j + 1:])}, {proof})'
    return proof


def extra_transport(orientation):
    ops = CENTER_ORIENTATIONS[orientation]
    ctx = Square()
    transport = Transport(ops, ctx)
    actual = extra_points(orientation)
    ctx.use_fractions([v for point in EXTRA + actual for v in point])
    bits = [f'M.Membership.inside(TC, square, {point_term(v)})' for v in actual]
    goal = f'B.Bits.Holds({ors(bits)})'
    call = f'Stromquist.extra_base(TC, {transport.normal}, {transport.corners}, {transport.signs[0]}, {transport.signs[1]}, nontrivial)'

    def convert(k, containment):
        back = transport.backward(EXTRA[k], containment)
        return or_at(bits, k, f'M.Membership.inside_of(TC, square, {point_term(actual[k])}, {back})')

    def eliminate(k, term):
        if k == len(EXTRA) - 1:
            return convert(k, term)
        left = f'P.Problem.Containment<F, field, {transport.normal}, {point_term(EXTRA[k])}>'
        right = containments(transport.normal, [point_term(v) for v in EXTRA[k + 1:]], named=True)
        return f'M.Membership.either({left}, {right}, {goal}, {term}, +found{k} => {convert(k, f"found{k}")}, rest{k} => {eliminate(k + 1, f"rest{k}")})'
    return f'''
def Stromquist.extra_{orientation}(TPL, {SQUARE_PARAMS}, +nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)) ->
  B.Bits.Holds(I.Incidence.any8(Stromquist.extra_row_{orientation}(TC, square))):
  {eliminate(0, call)}
'''


def main():
    parts = [basics(), perimeter()] + [clause(a, b, xs) for (a, b), xs in INCIDENCE.PAIRS.items()] + [pair_ok()] + [center_base(0), center_base(1)] + [center_transport(o, i) for o in CENTER_ORIENTATIONS for i in (0, 1)] + [extra_base(), extra_rows()] + [extra_transport(o) for o in CENTER_ORIENTATIONS]
    denominators = sorted({v.denominator for v in FRACTIONS})
    parts = [HEADER] + [inverse_lemma(m) for m in denominators] + [fraction_lemma(v) for v in sorted(FRACTIONS)] + parts
    (ROOT / 'bend' / 'Stromquist.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
