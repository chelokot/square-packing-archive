#!/usr/bin/env python3
"""Write bend/Chords.bend: the vertical chord of a square in first-quadrant normal form.

For the square with centre (cx, cy), cosine c >= 0 and sine s >= 0, and an
abscissa x with u = x - cx, the open chord is empty unless u lies strictly
between -(c + s)/2 and (c + s)/2. Inside, its ends are
lo = cy + (-1/2 - c u)/s when u <= (s - c)/2, else cy + (-1/2 + s u)/c, and
hi = cy + (1/2 - c u)/s when u >= (c - s)/2, else cy + (1/2 + s u)/c.
The four thresholds are the abscissae of the vertices. Every point strictly
inside the chord lies in the interior of the square, and the chord of a
square fitting [0, side]^2 lies in [0, side], so the chords of a packing fit
[0, side]. The area of the square left of x is piecewise quadratic with the
same breakpoints, and between breakpoints it grows by the chord length at the
midpoint; sweeping all breakpoints gives n <= side^2 for n squares.
"""
import itertools
from types import SimpleNamespace

from bend_proof import ROOT, Context, Refuter, SquareContext, T, build, expand, num

HEADER = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Certificate.bend as C
import ./bend-math/Intervals.bend as I
import ./bend-math/Natural.bend as N
import ./bend-math/Sweep.bend as W
import ./Problem.bend as P
import ./Packings.bend as Pk
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Scaling.bend as S
import ./Membership.bend as M
'''

SQUARE = '+square: P.Problem.Square<F, field>'
H = T('HALF', 'h')


def accessors():
    return {name: T(f'P.Problem.{field}(F, field, square)', name)
            for name, field in [('cx', 'center_x'), ('cy', 'center_y'), ('c', 'cosine'), ('s', 'sine')]}


def thresholds_of(v):
    cx, c, s = v['cx'], v['c'], v['s']
    return {'left': cx - (c + s) * H, 'right': cx + (c + s) * H, 'low': cx + (s - c) * H, 'high': cx + (c - s) * H}


def chord_ends(v, x, sides, inverses):
    """The scalars whose inverses the chord uses and its ends, for the decisions low and high of a nonempty chord."""
    cy, c, s = v['cy'], v['c'], v['s']
    u = x - v['cx']
    low, high = sides
    used = ['s' if low == 'Inl' else 'c', 's' if high == 'Inl' else 'c']
    lo = cy + (((-H) - c * u) if low == 'Inl' else ((-H) + s * u)) * inverses[used[0]]
    hi = cy + ((H - c * u) if high == 'Inl' else (H + s * u)) * inverses[used[1]]
    return used, lo, hi


def comparisons(x, thresholds):
    """The four decisions the chord reads: x <= left, right <= x, x <= low, high <= x."""
    return [('left', x, thresholds['left']), ('right', thresholds['right'], x),
            ('low', x, thresholds['low']), ('high', thresholds['high'], x)]


def dispatch(leaf, depth):
    """Nested matches on the four decisions with leaf('before') or leaf('after') for an empty chord and leaf((low, high)) otherwise."""
    lines = [(0, 'match left:'), (1, 'case Inl{+left}:'), (2, leaf('before')), (1, 'case Inr{left}:'), (2, 'match right:'),
             (3, 'case Inl{+right}:'), (4, leaf('after')), (3, 'case Inr{right}:'), (4, 'match low:')]
    for low in ('Inl', 'Inr'):
        lines += [(5, f'case {low}{{{"+" if low == "Inl" else ""}low}}:'), (6, 'match high:')]
        for high in ('Inl', 'Inr'):
            lines += [(7, f'case {high}{{{"+" if high == "Inl" else ""}high}}:'), (8, leaf((low, high)))]
    return ''.join(f'{"  " * (depth + level)}{text}\n' for level, text in lines)


X = T('x', 'x')
THRESHOLDS = {name: T(f'Chords.{name}_end(TC, square)', name) for name in ('left', 'right', 'low', 'high')}
DECISIONS = ', '.join(f'{name}: Or(LE({a.bend}, {b.bend}), LE({a.bend}, {b.bend}) -> Empty)' for name, a, b in comparisons(X, THRESHOLDS))
CHORD = 'Chords.chord_by(TC, square, x, left, right, low, high)'
SIGNS = '+cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square))'
SIGNS_BOTH = 'LE(ZERO, P.Problem.cosine(F, field, square)), LE(ZERO, P.Problem.sine(F, field, square))'
PACKING = '~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>'
PACKED = '~count, ~side, ~packing'
CLEANS = ', '.join(f'+{name}_clean: Either<&2, &2, LE({t.bend}, a), LE(b, {t.bend})>' for name, t in THRESHOLDS.items())


REGIONS = {'before': 'before', 'after': 'after', ('Inl', 'Inr'): 'rising', ('Inr', 'Inl'): 'falling',
           ('Inl', 'Inl'): 'sine', ('Inr', 'Inr'): 'cosine'}


def swept(v, x, region, inverses):
    """The area of the square left of x and the length of its chord, as polynomials valid on the closure of a region."""
    c, s = v['c'], v['s']
    u = x - v['cx']
    reach = (c + s) * H
    both = inverses['s'] * inverses['c']
    return {'before': (num(0), num(0)), 'after': (num(1), num(0)),
            ('Inl', 'Inr'): (both * (u + reach) * (u + reach) * H, both * (u + reach)),
            ('Inr', 'Inl'): (1 - both * (reach - u) * (reach - u) * H, both * (reach - u)),
            ('Inl', 'Inl'): (inverses['s'] * (u + s * H), inverses['s']),
            ('Inr', 'Inr'): (inverses['c'] * (u + c * H), inverses['c'])}[region]


def region_facts(v, x, region):
    """The conditions on x for a region, as (name, lower, upper): closed for the area, strict for the chord length."""
    thresholds = thresholds_of(v)
    if region == 'before':
        return [('region_left', x, thresholds['left'])]
    if region == 'after':
        return [('region_right', thresholds['right'], x)]
    low, high = region
    return [('region_left', thresholds['left'], x), ('region_right', x, thresholds['right']),
            ('region_low', *((x, thresholds['low']) if low == 'Inl' else (thresholds['low'], x))),
            ('region_high', *((thresholds['high'], x) if high == 'Inl' else (x, thresholds['high'])))]


def chord_defs():
    v = accessors()
    inverses = {key: T(f'INV({v[key].bend})', 'i' + key) for key in ('s', 'c')}
    thresholds = ''.join(f'''
def Chords.{name}_end(TPL, {SQUARE}) -> F:
  {term.bend}
''' for name, term in thresholds_of(v).items())

    def leaf(sides):
        if not isinstance(sides, tuple):
            return 'I.Interval{ZERO, ZERO}'
        _, lo, hi = chord_ends(v, X, sides, inverses)
        return f'I.Interval{{{lo.bend}, {hi.bend}}}'

    def area(sides):
        return swept(v, X, sides, inverses)[0].bend

    decide = ', '.join(f'K.Field.le_decidable(F, field)({a.bend}, {b.bend})' for _, a, b in comparisons(X, THRESHOLDS))
    return thresholds + f'''
def Chords.chord_by(TPL, {SQUARE}, +x: F, {DECISIONS}) -> I.Intervals.Interval<F>:
{dispatch(leaf, 1)}
def Chords.chord(TPL, {SQUARE}, +x: F) -> I.Intervals.Interval<F>:
  Chords.chord_by(TC, square, x, {decide})

def Chords.area_by(TPL, {SQUARE}, +x: F, {DECISIONS}) -> F:
{dispatch(area, 1)}
def Chords.area(TPL, {SQUARE}, +x: F) -> F:
  Chords.area_by(TC, square, x, {decide})
'''


def absurd(goal, refuter):
    """A finish that refutes the case from its strict facts."""
    def finish(current, stricts):
        refutation = refuter.refute(current, stricts)
        if refutation is None:
            raise SystemExit(f'no refutation of {[(u.text, v.text) for u, v, _ in stricts]}')
        return f'Empty.absurd({goal}, {refutation})'
    return finish


def accessor_context():
    """A context for the square `square` through its accessors, with its unit equation and one half."""
    ctx = Context()
    v = {name: ctx.var(name, term.bend) for name, term in accessors().items()}
    ctx.raw_equation(((v['c'] * v['c'] + v['s'] * v['s']) - 1).text, 'G.Geometry.square_unit(TC, square)')
    h = ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    return ctx, v, h


def signs(ctx, v):
    ctx.nonnegative(v['c'], 'cosine_sign')
    ctx.nonnegative(v['s'], 'sine_sign')


def inverse_vars(ctx, v):
    return {key: ctx.var('i' + key, f'INV({v[key].bend})') for key in ('s', 'c')}


def positivity(v, inverses, key):
    """Steps proving that the scalar `key` is positive and binding its inverse."""
    positive = f'{key}_positive'
    return [('lt', positive, num(0), v[key]),
            ('equation', v[key] * inverses[key], num(1),
             f'AL.same_transitive(TC, MUL({v[key].bend}, INV({v[key].bend})), ONE, R.FieldRing.of_nat(TC, 1n), '
             f'AL.mul_inverse(TC, {v[key].bend}, O.FieldOrder.lt_of(TC, ZERO, {v[key].bend}, {positive})), S.Scaling.one_is_number(TC))'),
            ('le', f'{key}_inverse_nonnegative', num(0), inverses[key], [inverses[key]])]


def nonempty(ctx, v, x, low, high):
    """Add the decisions of a nonempty chord to ctx; return the steps for its strict facts and inverses, and its ends."""
    steps, gaps = [], []
    for (name, a, b), choice in zip(comparisons(x, thresholds_of(v)), ('Inr', 'Inr', low, high)):
        if choice == 'Inl':
            ctx.below(a, b, name)
            gaps.append(b - a)
        else:
            steps.append(('given_lt', name, b, a, f'O.FieldOrder.strict_of(TC, {b.bend}, {a.bend}, {name})'))
            gaps.append(a - b)
    inverses = inverse_vars(ctx, v)
    used, lo, hi = chord_ends(v, x, (low, high), inverses)
    for key in dict.fromkeys(used):
        steps += positivity(v, inverses, key)
    return SimpleNamespace(steps=steps, gaps=gaps, lo=lo, hi=hi, used=used, inverses=inverses)


def interior_leaf(sides):
    """The point (x, y) strictly inside the chord lies in the interior of the square."""
    ctx, v, h = accessor_context()
    cx, cy, c, s = v['cx'], v['cy'], v['c'], v['s']
    x, y = ctx.var('x', 'x'), ctx.var('y', 'y')
    signs(ctx, v)
    point = 'P.Point{x, y}'
    goal = f'P.Problem.InteriorContainment<F, field, square, {point}>'
    if not isinstance(sides, tuple):
        empty = [('given_lt', 'above', num(0), y, 'above'), ('given_lt', 'below', y, num(0), 'below')]
        return build(ctx, empty, goal, Refuter(), absurd(goal, Refuter()))
    chord = nonempty(ctx, v, x, *sides)
    lx = T(f'G.Geometry.local_x(TC, square, {point})', ((x - cx) * c + (y - cy) * s).text)
    ly = T(f'G.Geometry.local_y(TC, square, {point})', ((-(x - cx)) * s + (y - cy) * c).text)
    steps = chord.steps + [('given_lt', 'above', chord.lo, y, 'above'), ('given_lt', 'below', y, chord.hi, 'below')]
    bounds = {'lx_upper': (lx, h), 'lx_lower': (-h, lx), 'ly_upper': (ly, h), 'ly_lower': (-h, ly)}
    low, high = sides
    direct = ['lx_lower' if low == 'Inl' else 'ly_lower', 'lx_upper' if high == 'Inl' else 'ly_upper']
    steps += [('lt', name, *bounds[name]) for name in direct]

    def products(key, positive):
        rooms = [(f'{name}_room', num(0), bounds[name][1] - bounds[name][0]) for name in direct]
        scalar = v[key]
        return ([('lt', *room) for room in rooms] +
                [('given_lt', f'{room[0]}_{key}', num(0), scalar * room[2],
                  f'M.Membership.strict_product(TC, {scalar.bend}, {room[2].bend}, {positive}, {room[0]})') for room in rooms])

    def finish(current, stricts):
        fields = [f'O.FieldOrder.lt_of(TC, {bounds[name][0].bend}, {bounds[name][1].bend}, {name})'
                  for name in ('lx_upper', 'lx_lower', 'ly_upper', 'ly_lower')]
        return f'G.Geometry.local_interior(TC, square, {point}, G.StrictLocal{{{", ".join(fields)}}})'

    plain = [('lt', name, *bounds[name]) for name in bounds if name not in direct]
    other = [key for key in ('s', 'c') if key not in chord.used]
    if other:
        key = other[0]
        attempts = [plain, [('cases', f'{key}_sign', v[key], num(0), plain, products(key, f'{key}_sign') + plain)]]
    else:
        attempts = [plain] + [products(key, f'{key}_positive') + plain for key in dict.fromkeys(chord.used)]
    for attempt in attempts:
        try:
            return build(ctx, steps + attempt, goal, Refuter(), finish)
        except SystemExit:
            continue
    raise SystemExit(f'no interior proof for {sides}')


def inside_leaf(sides):
    """The chord of a square whose corners fit [0, side]^2 lies in [0, side]."""
    if not isinstance(sides, tuple):
        return 'C.Both{AX.le_reflexive(ZERO), C.Both{AX.le_reflexive(ZERO), side_nonnegative}}'
    ctx = SquareContext()
    h = ctx.half()
    side = ctx.var('side', 'side')
    v = {'cx': ctx.cx, 'cy': ctx.cy, 'c': ctx.c, 's': ctx.s}
    signs(ctx, v)
    ctx.corner_facts(h, side)
    chord = nonempty(ctx, v, ctx.var('x', 'x'), *sides)
    steps = list(chord.steps)
    for key in dict.fromkeys(chord.used):
        steps += [('le', f'{key}_weight{k}', num(0), chord.inverses[key] * g, []) for k, g in enumerate(chord.gaps)]
    if len(set(chord.used)) == 2:
        steps.append(('le', 'inverses', num(0), chord.inverses['s'] * chord.inverses['c'], []))

    lo, hi = chord.lo, chord.hi
    goal = f'I.Intervals.Inside(TC, ZERO, side, I.Interval{{{lo.bend}, {hi.bend}}})'
    return build(ctx, steps, goal, Refuter(), lambda current, stricts: (
        f'C.Both{{{current.le(0, lo)}, C.Both{{{current.le(lo, hi)}, {current.le(hi, side)}}}}}'))


def flat_leaf(sides):
    """A chord whose ends do not increase is the empty chord at zero."""
    if not isinstance(sides, tuple):
        return 'AX.le_reflexive(ZERO)'
    ctx, v, _ = accessor_context()
    signs(ctx, v)
    x = ctx.var('x', 'x')
    chord = nonempty(ctx, v, x, *sides)
    ctx.below(chord.hi, chord.lo, 'flat')
    goal = f'LE({chord.hi.bend}, ZERO)'
    refuter = Refuter(squares=[v['s'], v['c']])
    steps = chord.steps + [('le', 'scale', num(0), v['s'] * v['c'], [])]
    return build(ctx, steps, goal, refuter, absurd(goal, refuter))


def meet_leaf(lows, highs):
    """Two overlapping proper intervals share the midpoint of the larger low end and the smaller high end."""
    ctx = Context()
    a1, b1, a2, b2 = (ctx.var(name, f'I.Intervals.{end}(F, {interval})') for name, end, interval in
                      [('a1', 'lo', 'first'), ('b1', 'hi', 'first'), ('a2', 'lo', 'second'), ('b2', 'hi', 'second')])
    h = ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    steps = [('given_lt', name, a, b, f'O.FieldOrder.strict_of(TC, {a.bend}, {b.bend}, {name})')
             for name, a, b in [('overlap_right', a2, b1), ('overlap_left', a1, b2), ('first_proper', a1, b1), ('second_proper', a2, b2)]]
    for name, a, b, choice in [('lows', a1, a2, lows), ('highs', b1, b2, highs)]:
        if choice == 'Inl':
            ctx.below(a, b, name)
        else:
            steps.append(('given_lt', name, b, a, f'O.FieldOrder.strict_of(TC, {b.bend}, {a.bend}, {name})'))
    y = ((a2 if lows == 'Inl' else a1) + (b1 if highs == 'Inl' else b2)) * h
    steps += [('lt', 'first_above', a1, y), ('lt', 'first_below', y, b1), ('lt', 'second_above', a2, y), ('lt', 'second_below', y, b2)]
    goal = 'I.Intervals.Apart(TC, first, second)'
    return build(ctx, steps, goal, Refuter(), lambda current, stricts:
                 f'Empty.absurd({goal}, clash({y.bend}, first_above, first_below, second_above, second_below))')


def meet():
    lo, hi = (lambda interval: f'I.Intervals.lo(F, {interval})'), (lambda interval: f'I.Intervals.hi(F, {interval})')
    orders = [('right', hi('first'), lo('second')), ('left', hi('second'), lo('first')), ('first_flat', hi('first'), lo('first')),
              ('second_flat', hi('second'), lo('second')), ('lows', lo('first'), lo('second')), ('highs', hi('first'), hi('second'))]
    decisions = ', '.join(f'{name}_order: Or(LE({a}, {b}), LE({a}, {b}) -> Empty)' for name, a, b in orders)
    decide = ', '.join(f'K.Field.le_decidable(F, field)({a}, {b})' for _, a, b in orders)
    clash = (f'@y: F -> O.FieldOrder.Strict(TC, {lo("first")}, y) -> O.FieldOrder.Strict(TC, y, {hi("first")}) -> '
             f'O.FieldOrder.Strict(TC, {lo("second")}, y) -> O.FieldOrder.Strict(TC, y, {hi("second")}) -> Empty')
    params = (f'+first: I.Intervals.Interval<F>, +second: I.Intervals.Interval<F>, +first_low: LE(ZERO, {lo("first")}), '
              f'+second_low: LE(ZERO, {lo("second")}),\n  first_flat: LE({hi("first")}, {lo("first")}) -> LE({hi("first")}, ZERO), '
              f'second_flat: LE({hi("second")}, {lo("second")}) -> LE({hi("second")}, ZERO),\n  clash: {clash}')
    leaves = ''.join(f'''
                    case {lows}{{{"+" if lows == "Inl" else ""}lows}} {highs}{{{"+" if highs == "Inl" else ""}highs}}:
                      {meet_leaf(lows, highs)}''' for lows in ('Inl', 'Inr') for highs in ('Inl', 'Inr'))
    return f'''
def Chords.meet_by(TPL, {params},
  {decisions}) -> I.Intervals.Apart(TC, first, second):
  match right_order:
    case Inl{{apart}}:
      Inl{{apart}}
    case Inr{{overlap_right}}:
      match left_order:
        case Inl{{apart}}:
          Inr{{apart}}
        case Inr{{overlap_left}}:
          match first_flat_order:
            case Inl{{+flat}}:
              Inl{{I.Intervals.le_trans(TC, {hi("first")}, ZERO, {lo("second")}, first_flat(flat), second_low)}}
            case Inr{{first_proper}}:
              match second_flat_order:
                case Inl{{+flat}}:
                  Inr{{I.Intervals.le_trans(TC, {hi("second")}, ZERO, {lo("first")}, second_flat(flat), first_low)}}
                case Inr{{second_proper}}:
                  match lows_order highs_order:{leaves}

def Chords.meet(TPL, {params}) -> I.Intervals.Apart(TC, first, second):
  Chords.meet_by(TC, first, second, first_low, second_low, first_flat, second_flat, clash, {decide})
'''


def pair(current, a, b):
    return f'S.Scaling.pair(TC, {a.bend}, {b.bend}, {current.le(a, b)}, {current.le(b, a)})'


def degenerate(ctx, v, inverses, steps):
    """Steps for the boundary cases of a region: a scalar that vanishes, a collapsed field, an inverse that exists."""
    steps = list(steps)
    used = {step[1] for step in steps if step[0] == 'lt'}
    candidates = [[('le', f'{key}_nonpositive', v[key], num(0), []),
                   ('equation', v[key], num(0), f'S.Scaling.pair(TC, {v[key].bend}, ZERO, {key}_nonpositive, {"cosine" if key == "c" else "sine"}_sign)')]
                  for key in ('s', 'c')]
    collapse = [('le', 'collapsed', num(1), num(0), []),
                ('equation', num(1), num(0), f'S.Scaling.pair(TC, {num(1).bend}, ZERO, collapsed, O.FieldOrder.zero_le_of_nat(TC, 1n))')]
    candidates.append(collapse)
    for key in ('s', 'c'):
        if f'{key}_positive' not in used:
            candidates += [positivity(v, inverses, key),
                           [('cases', f'{key}_split', v[key], num(0), collapse,
                             [('given_lt', f'{key}_positive', num(0), v[key], f'{key}_split')] + positivity(v, inverses, key)[1:])]]
    for candidate in candidates:
        try:
            build(ctx, steps + candidate, 'Empty', Refuter(), lambda current, stricts: 'probe')
        except SystemExit:
            continue
        steps += candidate
    return steps


def region_leaf(region, measure, sides):
    """At an x in the closure of `region`, the area is the region's polynomial; strictly inside it, so is the chord length."""
    ctx, v, h = accessor_context()
    signs(ctx, v)
    x = ctx.var('x', 'x')
    thresholds = thresholds_of(v)
    if isinstance(sides, tuple):
        chord = nonempty(ctx, v, x, *sides)
        inverses, steps, lo, hi = chord.inverses, chord.steps, chord.lo, chord.hi
        decided = [(name, a, b) for (name, a, b), choice in zip(comparisons(x, thresholds), ('Inr', 'Inr', *sides)) if choice == 'Inl']
    else:
        inverses, steps, lo, hi = inverse_vars(ctx, v), [], num(0), num(0)
        decided = [('left', x, thresholds['left']) if sides == 'before' else ('right', thresholds['right'], x)]
        ctx.below(*decided[0][1:], decided[0][0])
    facts = region_facts(v, x, region)
    if measure == 'length':
        steps += [('given_lt', name, a, b, name) for name, a, b in facts]
    else:
        for name, a, b in facts:
            ctx.below(a, b, name)
        steps += [('equation', a, b, f'S.Scaling.pair(TC, {a.bend}, {b.bend}, {first}, {second})')
                  for first, a, b in decided for second, a2, b2 in facts if (a2.text, b2.text) == (b.text, a.text)]
    area = swept(v, x, sides, inverses)[0]
    polynomial, slope = swept(v, x, region, inverses)
    left, right = (area, polynomial) if measure == 'area' else (hi - lo, slope)
    goal = f'SAME({left.bend}, {right.bend})'

    def finish(current, stricts):
        refutation = Refuter().refute(current, stricts)
        if refutation is not None:
            return f'Empty.absurd({goal}, {refutation})'
        return pair(current, left, right)

    try:
        return build(ctx, steps, goal, Refuter(), finish)
    except SystemExit:
        return build(ctx, degenerate(ctx, v, inverses, steps), goal, Refuter(), finish)


def regions():
    out = ''
    v = accessors()
    inverses = {key: T(f'INV({v[key].bend})', 'i' + key) for key in ('s', 'c')}
    decide = ', '.join(f'K.Field.le_decidable(F, field)({a.bend}, {b.bend})' for _, a, b in comparisons(X, THRESHOLDS))
    for region, name in REGIONS.items():
        polynomial, slope = swept(v, X, region, inverses)
        facts = region_facts(v, X, region)
        closed = ', '.join(f'+{fact}: LE({a.bend}, {b.bend})' for fact, a, b in facts)
        strict = ', '.join(f'+{fact}: O.FieldOrder.Strict(TC, {a.bend}, {b.bend})' for fact, a, b in facts)
        given = ', '.join(fact for fact, _, _ in facts)
        out += f'''
def Chords.{name}_area_by(TPL, {SQUARE}, {SIGNS}, +x: F, {closed}, {DECISIONS}) ->
  SAME(Chords.area_by(TC, square, x, left, right, low, high), {polynomial.bend}):
{dispatch(lambda sides: region_leaf(region, 'area', sides), 1)}
def Chords.{name}_area(TPL, {SQUARE}, {SIGNS}, +x: F, {closed}) -> SAME(Chords.area(TC, square, x), {polynomial.bend}):
  Chords.{name}_area_by(TC, square, cosine_sign, sine_sign, x, {given}, {decide})

def Chords.{name}_length_by(TPL, {SQUARE}, {SIGNS}, +x: F, {strict}, {DECISIONS}) ->
  SAME(I.Intervals.length(TC, {CHORD}), {slope.bend}):
{dispatch(lambda sides: region_leaf(region, 'length', sides), 1)}
def Chords.{name}_length(TPL, {SQUARE}, {SIGNS}, +x: F, {strict}) -> SAME(I.Intervals.length(TC, Chords.chord(TC, square, x)), {slope.bend}):
  Chords.{name}_length_by(TC, square, cosine_sign, sine_sign, x, {given}, {decide})
'''
    return out


def strip_leaf(cleans):
    """Area gained between a and b with no vertex abscissa strictly between: (b - a) times the chord length at the midpoint."""
    ctx, v, h = accessor_context()
    a, b = ctx.var('a', 'a'), ctx.var('b', 'b')
    inverses = inverse_vars(ctx, v)
    thresholds = thresholds_of(v)
    names = ('left', 'right', 'low', 'high')
    sides = dict(zip(names, cleans))
    if sides['left'] == 'Inr':
        region = 'before'
    elif sides['right'] == 'Inl':
        region = 'after'
    else:
        region = ('Inl' if sides['low'] == 'Inr' else 'Inr', 'Inl' if sides['high'] == 'Inl' else 'Inr')
    name = REGIONS[region]
    ctx.below(a, b, 'order')
    for threshold in names:
        t = thresholds[threshold]
        ctx.below(*((t, a) if sides[threshold] == 'Inl' else (b, t)), f'{threshold}_clean')

    def closed_at(x):
        proofs = []
        for fact, lower, upper in region_facts(v, x, region):
            threshold = fact.removeprefix('region_')
            t = thresholds[threshold]
            clean = f'{threshold}_clean'
            if sides[threshold] == 'Inl':
                proofs.append(clean if x is a else f'I.Intervals.le_trans(TC, {t.bend}, a, b, {clean}, order)')
            else:
                proofs.append(clean if x is b else f'I.Intervals.le_trans(TC, a, b, {t.bend}, order, {clean})')
        return ', '.join(proofs)

    area_a, area_b = (ctx.var(f'area_{p}', f'Chords.area(TC, square, {p})') for p in ('a', 'b'))
    middle = (a + b) * h
    length = ctx.var('length', f'I.Intervals.length(TC, Chords.chord(TC, square, {middle.bend}))')
    polynomial = lambda x: swept(v, x, region, inverses)[0]
    slope = swept(v, middle, region, inverses)[1]
    sign_args = 'cosine_sign, sine_sign'
    steps = [('equation', area_a, polynomial(a), f'Chords.{name}_area(TC, square, {sign_args}, a, {closed_at(a)})'),
             ('equation', area_b, polynomial(b), f'Chords.{name}_area(TC, square, {sign_args}, b, {closed_at(b)})')]
    stricts = [(f'middle_{fact}', lower, upper) for fact, lower, upper in region_facts(v, middle, region)]
    proper = ([('lt', fact, lower, upper) for fact, lower, upper in stricts] +
              [('equation', length, slope, f'Chords.{name}_length(TC, square, {sign_args}, {middle.bend}, {", ".join(f for f, _, _ in stricts)})')])
    flat = [('equation', b, a, f'S.Scaling.pair(TC, b, a, flat, order)')]
    steps.append(('cases', 'flat', b, a, flat, proper))
    lhs, rhs = area_b - area_a, (b - a) * length
    goal = f'SAME({lhs.bend}, {rhs.bend})'
    return build(ctx, steps, goal, Refuter(), lambda current, stricts: pair(current, lhs, rhs))


def strip():
    leaves = ''.join(f'''
    case {" ".join(f"{side}{{+{name}_clean}}" for side, name in zip(sides, THRESHOLDS))}:
      {strip_leaf(sides)}''' for sides in itertools.product(('Inl', 'Inr'), repeat=4))
    middle = 'MUL(ADD(a, b), HALF)'
    return f'''
def Chords.strip(TPL, {SQUARE}, {SIGNS}, +a: F, +b: F, +order: LE(a, b), {CLEANS}) ->
  SAME(ADD(Chords.area(TC, square, b), NEG(Chords.area(TC, square, a))),
    MUL(ADD(b, NEG(a)), I.Intervals.length(TC, Chords.chord(TC, square, {middle})))):
  match left_clean right_clean low_clean high_clean:{leaves}
'''


def combined(terms, equations, lhs, rhs):
    """Same(lhs, rhs) for terms named by their Bend source, from equations (left, right, proof of Same)."""
    ctx = Context()
    named = {name: ctx.var(name, bend) for name, bend in terms}
    ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    for left, right, proof in equations(named):
        ctx.equal(left, right, proof)
    left, right = lhs(named), rhs(named)
    return pair(ctx, left, right)


def endpoint(name, region, x):
    """The area of a fitting square in normal form at the container's edge x."""
    ctx = SquareContext()
    h = ctx.half()
    side = ctx.var('side', 'side')
    v = {'cx': ctx.cx, 'cy': ctx.cy, 'c': ctx.c, 's': ctx.s}
    ctx.corner_facts(h, side)
    point = {'ZERO': num(0), 'side': side}[x]
    proofs = ', '.join(ctx.le(lower, upper) for _, lower, upper in region_facts(v, point, region))
    value = swept(v, point, region, inverse_vars(ctx, v))[0]
    return f'''
def Chords.{name}(TPL, {SQUARE}, +side: F, +corners: M.Membership.Corners<F, field, square, side>,
  +signs: C.Certificate.Both<{SIGNS_BOTH}>) -> SAME(Chords.area(TC, square, {x}), {value.bend}):
  match square corners signs:
    case {ctx.square_pattern()} {ctx.corners_pattern()} C.Both{{+cosine_sign, +sine_sign}}:
      Chords.{REGIONS[region]}_area(TC, {ctx.square()}, cosine_sign, sine_sign, {point.bend}, {proofs})
'''


def area_bound():
    square = lambda index: f'Pk.Packings.squares(F, field, count, side, packing)({index})'
    normal = lambda index: f'Chords.normal(TC, {PACKED}, {index})'
    signs = lambda index: f'Y.Symmetry.first_quadrant_signs(TC, {square(index)})'
    mass = lambda x, n: f'Chords.mass(TC, {PACKED}, {x}, {n})'
    area = lambda index, x: f'Chords.area(TC, {normal(index)}, {x})'
    middle = 'MUL(ADD(a, b), HALF)'
    total = lambda n: f'I.Intervals.total(TC, Chords.chords(TC, {PACKED}, {middle}, {n}))'
    length = lambda index: f'I.Intervals.length(TC, Chords.at(TC, {PACKED}, {middle}, {index}))'
    clean_names = ', '.join(f'{name}_clean' for name in THRESHOLDS)
    gained_step = combined(
        [('area_b', area('p', 'b')), ('area_a', area('p', 'a')), ('mass_b', mass('b', 'p')), ('mass_a', mass('a', 'p')),
         ('length', length('p')), ('total', total('p')), ('a', 'a'), ('b', 'b')],
        lambda t: [(t['area_b'] - t['area_a'], (t['b'] - t['a']) * t['length'],
                    f'Chords.strip_signed(TC, {normal("p")}, {signs("p")}, a, b, order, {clean_names})'),
                   (t['mass_b'] - t['mass_a'], (t['b'] - t['a']) * t['total'], f'Chords.gained(TC, {PACKED}, a, b, order, p, rest)')],
        lambda t: (t['area_b'] + t['mass_b']) - (t['area_a'] + t['mass_a']), lambda t: (t['b'] - t['a']) * (t['length'] + t['total']))
    gained_zero = combined([('a', 'a'), ('b', 'b')], lambda t: [], lambda t: num(0) - num(0), lambda t: (t['b'] - t['a']) * num(0))
    potential = lambda x: f'Chords.potential(TC, {PACKED}, {x})'
    vertices = f'Chords.vertices(TC, {PACKED}, count)'
    descent = Context()
    terms = {name: descent.var(name, bend) for name, bend in
             [('mass_b', mass('b', 'count')), ('mass_a', mass('a', 'count')), ('total', total('count')), ('a', 'a'), ('b', 'b'), ('side', 'side')]}
    descent.below(terms['a'], terms['b'], 'order')
    descent.below(terms['total'], terms['side'] - num(0), f'Chords.covered(TC, {PACKED}, {middle})')
    descent.equal(terms['mass_b'] - terms['mass_a'], (terms['b'] - terms['a']) * terms['total'], f'Chords.gained(TC, {PACKED}, a, b, order, count, clean)')
    descent_proof = descent.le(terms['mass_b'] - terms['side'] * terms['b'], terms['mass_a'] - terms['side'] * terms['a'])
    start_step = combined([('area', area('p', 'ZERO')), ('mass', mass('ZERO', 'p'))],
                          lambda t: [(t['area'], num(0), f'Chords.start(TC, {normal("p")}, side, Chords.corners_at(TC, {PACKED}, p, bound), {signs("p")})'),
                                     (t['mass'], num(0), f'Chords.mass_start(TC, {PACKED}, p, N.Natural.le_transitive(p, 1n+p, count, Chords.le_successor(p), bound))')],
                          lambda t: t['area'] + t['mass'], lambda t: num(0))
    finish_step = combined([('area', area('p', 'side')), ('mass', mass('side', 'p')), ('count', 'R.FieldRing.of_nat(TC, 1n+p)'), ('previous', 'R.FieldRing.of_nat(TC, p)')],
                           lambda t: [(t['area'], num(1), f'Chords.finish(TC, {normal("p")}, side, Chords.corners_at(TC, {PACKED}, p, bound), {signs("p")})'),
                                      (t['mass'], t['previous'], f'Chords.mass_finish(TC, {PACKED}, p, N.Natural.le_transitive(p, 1n+p, count, Chords.le_successor(p), bound))'),
                                      (t['count'], num(1) + t['previous'], 'R.FieldRing.of_nat_add(TC, 1n, p)')],
                           lambda t: t['area'] + t['mass'], lambda t: t['count'])
    bound = Context()
    terms = {name: bound.var(name, bend) for name, bend in
             [('mass_side', mass('side', 'count')), ('mass_zero', mass('ZERO', 'count')), ('count', 'R.FieldRing.of_nat(TC, count)'), ('side', 'side')]}
    bound.below(terms['mass_side'] - terms['side'] * terms['side'], terms['mass_zero'] - terms['side'] * num(0), f'Chords.swept(TC, {PACKED})')
    bound.equal(terms['mass_side'], terms['count'], f'Chords.mass_finish(TC, {PACKED}, count, N.Natural.le_reflexive(count))')
    bound.equal(terms['mass_zero'], num(0), f'Chords.mass_start(TC, {PACKED}, count, N.Natural.le_reflexive(count))')
    bound_proof = bound.le(terms['count'], terms['side'] * terms['side'])
    return endpoint('start', 'before', 'ZERO') + endpoint('finish', 'after', 'side') + f'''
def Chords.strip_signed(TPL, {SQUARE}, +signs: C.Certificate.Both<{SIGNS_BOTH}>, +a: F, +b: F, +order: LE(a, b), {CLEANS}) ->
  SAME(ADD(Chords.area(TC, square, b), NEG(Chords.area(TC, square, a))),
    MUL(ADD(b, NEG(a)), I.Intervals.length(TC, Chords.chord(TC, square, {middle})))):
  match signs:
    case C.Both{{+cosine_sign, +sine_sign}}:
      Chords.strip(TC, square, cosine_sign, sine_sign, a, b, order, {clean_names})

def Chords.vertices(TPL, {PACKING}, +n: Nat) -> List<&2, F>:
  match n:
    case 0n:
      Nil{{}}
    case 1n+p:
      {" <> ".join(f"Chords.{name}_end(TC, {normal('p')})" for name in THRESHOLDS)} <> Chords.vertices(TC, {PACKED}, p)

def Chords.mass(TPL, {PACKING}, +x: F, +n: Nat) -> F:
  match n:
    case 0n:
      ZERO
    case 1n+p:
      ADD({area('p', 'x')}, {mass('x', 'p')})

def Chords.gained(TPL, {PACKING}, +a: F, +b: F, +order: LE(a, b), +n: Nat, +clean: W.Sweep.Clean(F, field, a, b, Chords.vertices(TC, {PACKED}, n))) ->
  SAME(ADD({mass('b', 'n')}, NEG({mass('a', 'n')})), MUL(ADD(b, NEG(a)), {total('n')})):
  match n clean:
    case 0n Unit{{}}:
      {gained_zero}
    case 1n+p C.Both{{+left_clean, C.Both{{+right_clean, C.Both{{+low_clean, C.Both{{+high_clean, +rest}}}}}}}}:
      {gained_step}

def Chords.potential(TPL, {PACKING}, +x: F) -> F:
  ADD({mass('x', 'count')}, NEG(MUL(side, x)))

def Chords.descent(TPL, {PACKING}, +a: F, +b: F, +order: LE(a, b), +clean: W.Sweep.Clean(F, field, a, b, Chords.vertices(TC, {PACKED}, count))) ->
  LE({potential('b')}, {potential('a')}):
  {descent_proof}

def Chords.sweep(TPL, {PACKING}, +pending: List<&2, F>, +a: F, +b: F, +order: LE(a, b),
  +marked: W.Sweep.Marked(F, field, a, b, pending, {vertices})) -> LE({potential('b')}, {potential('a')}):
  match pending:
    case Nil{{}}:
      Chords.descent(TC, {PACKED}, a, b, order, W.Sweep.clean(TC, a, b, {vertices}, marked))
    case +split <> rest:
      W.Sweep.cases_of(TC, split, a, LE({potential('b')}, {potential('a')}), K.Field.le_decidable(F, field)(split, a),
        +left => Chords.sweep(TC, {PACKED}, rest, a, b, order, W.Sweep.skip(TC, a, b, split, rest, {vertices}, Inl{{left}}, marked)),
        +inside_left => W.Sweep.cases_of(TC, b, split, LE({potential('b')}, {potential('a')}), K.Field.le_decidable(F, field)(b, split),
          +right => Chords.sweep(TC, {PACKED}, rest, a, b, order, W.Sweep.skip(TC, a, b, split, rest, {vertices}, Inr{{right}}, marked)),
          +inside_right => AX.le_transitive({potential('b')}, {potential('split')}, {potential('a')},
            Chords.sweep(TC, {PACKED}, rest, split, b, inside_right, W.Sweep.right(TC, a, b, split, rest, {vertices}, inside_left, marked)),
            Chords.sweep(TC, {PACKED}, rest, a, split, inside_left, W.Sweep.left(TC, a, b, split, rest, {vertices}, inside_right, marked)))))

def Chords.swept(TPL, {PACKING}) -> LE({potential('side')}, {potential('ZERO')}):
  Chords.sweep(TC, {PACKED}, {vertices}, ZERO, side, Pk.Packings.side_nonnegative(F, field, count, side, packing),
    W.Sweep.marked_members(TC, ZERO, side, {vertices}, {vertices}, W.Sweep.members_self(TC, {vertices})))

def Chords.mass_start(TPL, {PACKING}, +n: Nat, +bound: N.Natural.Le(n, count)) -> SAME({mass('ZERO', 'n')}, ZERO):
  match n:
    case 0n:
      AL.same_reflexive(TC, ZERO)
    case 1n+p:
      {start_step}

def Chords.mass_finish(TPL, {PACKING}, +n: Nat, +bound: N.Natural.Le(n, count)) -> SAME({mass('side', 'n')}, R.FieldRing.of_nat(TC, n)):
  match n:
    case 0n:
      AL.same_reflexive(TC, ZERO)
    case 1n+p:
      {finish_step}

def Chords.count_bound(TPL, {PACKING}) -> LE(R.FieldRing.of_nat(TC, count), MUL(side, side)):
  {bound_proof}
'''


def lemmas():
    interior = f'''
def Chords.interior_by(TPL, {SQUARE}, +x: F, +y: F, {SIGNS}, {DECISIONS},
  +above: O.FieldOrder.Strict(TC, I.Intervals.lo(F, {CHORD}), y), +below: O.FieldOrder.Strict(TC, y, I.Intervals.hi(F, {CHORD}))) ->
  P.Problem.InteriorContainment<F, field, square, P.Point{{x, y}}>:
{dispatch(interior_leaf, 1)}'''
    square = SquareContext()
    inside = f'''
def Chords.inside_by(TPL, {SQUARE}, +side: F, +corners: M.Membership.Corners<F, field, square, side>, +side_nonnegative: LE(ZERO, side),
  {SIGNS}, +x: F, {DECISIONS}) ->
  I.Intervals.Inside(TC, ZERO, side, {CHORD}):
  match square corners:
    case {square.square_pattern()} {square.corners_pattern()}:
{dispatch(inside_leaf, 3)}'''
    flat = f'''
def Chords.flat_by(TPL, {SQUARE}, {SIGNS}, +x: F, {DECISIONS},
  +flat: LE(I.Intervals.hi(F, {CHORD}), I.Intervals.lo(F, {CHORD}))) ->
  LE(I.Intervals.hi(F, {CHORD}), ZERO):
{dispatch(flat_leaf, 1)}'''
    return interior + inside + flat


def assembly():
    decide = ', '.join(f'K.Field.le_decidable(F, field)({a.bend}, {b.bend})' for _, a, b in comparisons(X, THRESHOLDS))
    signed = f'+signs: C.Certificate.Both<{SIGNS_BOTH}>'
    chord = lambda square: f'Chords.chord(TC, {square}, x)'
    square = lambda index: f'Pk.Packings.squares(F, field, count, side, packing)({index})'
    normal = lambda index: f'Chords.normal(TC, {PACKED}, {index})'
    at = lambda index: f'Chords.at(TC, {PACKED}, x, {index})'
    chords = lambda n: f'Chords.chords(TC, {PACKED}, x, {n})'
    fits = f'Pk.Packings.fits(F, field, count, side, packing)(index, bound)'
    step = lambda n: f'N.Natural.le_transitive({n}, 1n+{n}, count, Chords.le_successor({n}), bound)'
    return f'''
def Chords.interior(TPL, {SQUARE}, +x: F, +y: F, {signed},
  +above: O.FieldOrder.Strict(TC, I.Intervals.lo(F, {chord('square')}), y), +below: O.FieldOrder.Strict(TC, y, I.Intervals.hi(F, {chord('square')}))) ->
  P.Problem.InteriorContainment<F, field, square, P.Point{{x, y}}>:
  match signs:
    case C.Both{{+cosine_sign, +sine_sign}}:
      Chords.interior_by(TC, square, x, y, cosine_sign, sine_sign, {decide}, above, below)

def Chords.inside(TPL, {SQUARE}, +side: F, +corners: M.Membership.Corners<F, field, square, side>, +side_nonnegative: LE(ZERO, side),
  {signed}, +x: F) -> I.Intervals.Inside(TC, ZERO, side, {chord('square')}):
  match signs:
    case C.Both{{+cosine_sign, +sine_sign}}:
      Chords.inside_by(TC, square, side, corners, side_nonnegative, cosine_sign, sine_sign, x, {decide})

def Chords.flat(TPL, {SQUARE}, {signed}, +x: F, +flat: LE(I.Intervals.hi(F, {chord('square')}), I.Intervals.lo(F, {chord('square')}))) ->
  LE(I.Intervals.hi(F, {chord('square')}), ZERO):
  match signs:
    case C.Both{{+cosine_sign, +sine_sign}}:
      Chords.flat_by(TC, square, cosine_sign, sine_sign, x, {decide}, flat)

def Chords.apart(TPL, +first: P.Problem.Square<F, field>, +second: P.Problem.Square<F, field>, +side: F, +x: F,
  +first_signs: C.Certificate.Both<{SIGNS_BOTH.replace('square', 'first')}>, +second_signs: C.Certificate.Both<{SIGNS_BOTH.replace('square', 'second')}>,
  +first_inside: I.Intervals.Inside(TC, ZERO, side, {chord('first')}), +second_inside: I.Intervals.Inside(TC, ZERO, side, {chord('second')}),
  disjoint: @point: P.Problem.Point<F> -> P.Problem.InteriorContainment<F, field, first, point> -> P.Problem.InteriorContainment<F, field, second, point> -> Empty) ->
  I.Intervals.Apart(TC, {chord('first')}, {chord('second')}):
  match first_inside second_inside:
    case C.Both{{+first_low, first_rest}} C.Both{{+second_low, second_rest}}:
      Chords.meet(TC, {chord('first')}, {chord('second')}, first_low, second_low,
        +flat => Chords.flat(TC, first, first_signs, x, flat), +flat => Chords.flat(TC, second, second_signs, x, flat),
        +y => +first_above => +first_below => +second_above => +second_below => disjoint(P.Point{{x, y}},
          Chords.interior(TC, first, x, y, first_signs, first_above, first_below), Chords.interior(TC, second, x, y, second_signs, second_above, second_below)))

def Chords.le_successor(n: Nat) -> N.Natural.Le(n, 1n+n):
  match n:
    case 0n:
      Unit{{}}
    case 1n+p:
      Chords.le_successor(p)

def Chords.normal(TPL, {PACKING}, +index: Nat) -> P.Problem.Square<F, field>:
  Y.Symmetry.first_quadrant(TC, {square('index')})

def Chords.at(TPL, {PACKING}, +x: F, +index: Nat) -> I.Intervals.Interval<F>:
  {chord(normal('index'))}

def Chords.chords(TPL, {PACKING}, +x: F, +n: Nat) -> List<&2, I.Intervals.Interval<F>>:
  match n:
    case 0n:
      Nil{{}}
    case 1n+p:
      {at('p')} <> {chords('p')}

def Chords.corners_at(TPL, {PACKING}, +index: Nat, +bound: N.Natural.Le(1n+index, count)) -> M.Membership.Corners<F, field, {normal('index')}, side>:
  M.Membership.first_quadrant_corners(TC, {square('index')}, side, M.Membership.corners_of(TC, {square('index')}, side, {fits}, {fits}, {fits}, {fits}))

def Chords.inside_at(TPL, {PACKING}, +x: F, +index: Nat, +bound: N.Natural.Le(1n+index, count)) ->
  I.Intervals.Inside(TC, ZERO, side, {at('index')}):
  Chords.inside(TC, {normal('index')}, side, Chords.corners_at(TC, {PACKED}, index, bound),
    Pk.Packings.side_nonnegative(F, field, count, side, packing), Y.Symmetry.first_quadrant_signs(TC, {square('index')}), x)

def Chords.apart_at(TPL, {PACKING}, +x: F, +left: Nat, +right: Nat, +left_bound: N.Natural.Le(1n+left, count), +right_bound: N.Natural.Le(1n+right, count),
  different: {{left == right : Nat}} -> Empty) -> I.Intervals.Apart(TC, {at('left')}, {at('right')}):
  Chords.apart(TC, {normal('left')}, {normal('right')}, side, x,
    Y.Symmetry.first_quadrant_signs(TC, {square('left')}), Y.Symmetry.first_quadrant_signs(TC, {square('right')}),
    Chords.inside_at(TC, {PACKED}, x, left, left_bound), Chords.inside_at(TC, {PACKED}, x, right, right_bound),
    +point => first => second => Pk.Packings.disjoint(F, field, count, side, packing)(left, right, left_bound, right_bound, different, point,
      Y.Symmetry.first_quadrant_interior_back(TC, {square('left')}, point, first), Y.Symmetry.first_quadrant_interior_back(TC, {square('right')}, point, second)))

def Chords.within(TPL, {PACKING}, +x: F, +n: Nat, +bound: N.Natural.Le(n, count)) -> I.Intervals.Within(TC, ZERO, side, {chords('n')}):
  match n:
    case 0n:
      Unit{{}}
    case 1n+p:
      C.Both{{Chords.inside_at(TC, {PACKED}, x, p, bound), Chords.within(TC, {PACKED}, x, p, {step('p')})}}

def Chords.apart_all(TPL, {PACKING}, +x: F, +p: Nat, +p_bound: N.Natural.Le(1n+p, count), +m: Nat, +m_bound: N.Natural.Le(m, p)) ->
  I.Intervals.ApartAll(TC, {at('p')}, {chords('m')}):
  match m:
    case 0n:
      Unit{{}}
    case 1n+q:
      C.Both{{Chords.apart_at(TC, {PACKED}, x, p, q, p_bound,
        N.Natural.le_transitive(1n+q, p, count, m_bound, N.Natural.le_transitive(p, 1n+p, count, Chords.le_successor(p), p_bound)),
        same => N.Natural.not_successor_le_self(q, N.Natural.le_congruent(1n+q, p, 1n+q, q, m_bound, {{==}}, same))),
        Chords.apart_all(TC, {PACKED}, x, p, p_bound, q, N.Natural.le_transitive(q, 1n+q, p, Chords.le_successor(q), m_bound))}}

def Chords.pairwise(TPL, {PACKING}, +x: F, +n: Nat, +bound: N.Natural.Le(n, count)) -> I.Intervals.Pairwise(TC, {chords('n')}):
  match n:
    case 0n:
      Unit{{}}
    case 1n+p:
      C.Both{{Chords.apart_all(TC, {PACKED}, x, p, bound, p, N.Natural.le_reflexive(p)), Chords.pairwise(TC, {PACKED}, x, p, {step('p')})}}

def Chords.covered(TPL, {PACKING}, +x: F) -> LE(I.Intervals.total(TC, {chords('count')}), I.Intervals.minus(TC, side, ZERO)):
  I.Intervals.packed(TC, ZERO, side, {chords('count')}, Pk.Packings.side_nonnegative(F, field, count, side, packing),
    Chords.within(TC, {PACKED}, x, count, N.Natural.le_reflexive(count)), Chords.pairwise(TC, {PACKED}, x, count, N.Natural.le_reflexive(count)))
'''


def main():
    parts = [HEADER, chord_defs(), lemmas(), meet(), assembly(), regions(), strip(), area_bound()]
    (ROOT / 'bend' / 'Chords.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
