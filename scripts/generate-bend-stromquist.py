#!/usr/bin/env python3
"""Write bend/Stromquist.bend: the single-square facts of Stromquist's s(6) argument as bits.

For a square in first-quadrant normal form that fits [0, 3]^2, `Stromquist.row`
records which of the nine key points (1 + i/2, 1 + j/2) it contains. The
lemmas here give the facts that bend/Incidence.bend consumes, following
StromquistSixPoints.lean, StromquistSixAdjacency.lean and StromquistSixCenter.lean.
"""
import importlib.util
from fractions import Fraction

from bend_proof import ROOT, Context, Refuter, T, containments, expand, gap, num, one_of

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
SQUARE_PARAMS = (f'+square: P.Problem.Square<F, field>, +corners: M.Membership.Corners<F, field, square, {THREE}>, '
                 '+cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square))')
SQUARE_ARGS = 'square, corners, cosine_sign, sine_sign'


def key(k):
    return f'Stromquist.key{k}(TC)'


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

    def __init__(self):
        super().__init__()
        self.cx = self.var('cx', 'P.Problem.center_x(F, field, square)')
        self.cy = self.var('cy', 'P.Problem.center_y(F, field, square)')
        self.c = self.var('c', 'P.Problem.cosine(F, field, square)')
        self.s = self.var('s', 'P.Problem.sine(F, field, square)')
        self.h = self.var('h', 'HALF')
        self.raw_equation(((self.c * self.c + self.s * self.s) - 1).text, 'Stromquist.unit(TC, square)')
        self.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
        self.nonnegative(self.c, 'cosine_sign')
        self.nonnegative(self.s, 'sine_sign')
        self.fresh = 0

    def name(self, stem):
        self.fresh += 1
        return f'{stem}{self.fresh}'

    def point(self, p):
        return (p[0].text if isinstance(p[0], T) else p[0], p[1].text)


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


def affine(constant, x_coefficient, y_coefficient, cx, cy):
    out = rational(constant)
    if x_coefficient:
        out = out + rational(x_coefficient) * cx
    if y_coefficient:
        out = out + rational(y_coefficient) * cy
    return out


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
    return ', '.join(ctx.le(a, b) for a, b in hyps)


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


def triangle_call(ctx, leaves, vertices):
    weights = [affine(*w, ctx.cx, ctx.cy) for w in barycentric([KEY_VALUES[k] for k in vertices])]
    xs, ys = [], []
    for k in vertices:
        x, y = KEYS[k]
        xs.append(T(f'G.Geometry.local_x(TC, square, {key(k)})', ((x - ctx.cx) * ctx.c + (y - ctx.cy) * ctx.s).text))
        ys.append(T(f'G.Geometry.local_y(TC, square, {key(k)})', ((-(x - ctx.cx)) * ctx.s + (y - ctx.cy) * ctx.c).text))
    facts = [ctx.le(0, w) for w in weights]
    total = weights[0] + weights[1] + weights[2]
    facts += [ctx.le(total, num(1)), ctx.le(num(1), total)]
    for coordinates in (xs, ys):
        balance = weights[0] * coordinates[0] + weights[1] * coordinates[1] + weights[2] * coordinates[2]
        facts += [ctx.le(balance, num(0)), ctx.le(num(0), balance)]
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        d = (xs[i] - xs[j]) * (xs[i] - xs[j]) + (ys[i] - ys[j]) * (ys[i] - ys[j])
        facts.append(ctx.le(d, num(1)))
    terms = ', '.join(t.bend for t in xs + ys + weights)
    call = f'U.Unavoidable.triangle(TC, {terms}, {", ".join(facts)})'
    locals_ = [f'G.Geometry.Local<F, field, {xs[i].bend}, {ys[i].bend}>' for i in range(3)]
    results = [(k, key(k)) for k in vertices]

    def as_containment(i, name):
        return f'G.Geometry.local_contains(TC, square, {key(vertices[i])}, {name})'
    goal = leaves.goal
    inner = f'M.Membership.either({locals_[1]}, {locals_[2]}, {goal}, rest, +second => {leaves.convert(results[1], as_containment(1, "second"))}, +third => {leaves.convert(results[2], as_containment(2, "third"))})'
    return (f'M.Membership.either({locals_[0]}, Or({locals_[1]}, {locals_[2]}), {goal}, {call}, '
            f'+first => {leaves.convert(results[0], as_containment(0, "first"))}, rest => {inner})')


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
def Stromquist.perimeter(TPL, {SQUARE_PARAMS}) -> {goal}:
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


def main():
    parts = [HEADER, basics(), perimeter()] + [clause(a, b, xs) for (a, b), xs in INCIDENCE.PAIRS.items()] + [pair_ok()]
    (ROOT / 'bend' / 'Stromquist.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
