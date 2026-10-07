#!/usr/bin/env python3
"""Write bend/Chords.bend: the vertical chord of a square in first-quadrant normal form.

For the square with centre (cx, cy), cosine c >= 0 and sine s >= 0, and an
abscissa x with u = x - cx, the open chord is empty unless u lies strictly
between -(c + s)/2 and (c + s)/2. Inside, its ends are
lo = cy + (-1/2 - c u)/s when u <= (s - c)/2, else cy + (-1/2 + s u)/c, and
hi = cy + (1/2 - c u)/s when u >= (c - s)/2, else cy + (1/2 + s u)/c.
The four thresholds are the abscissae of the vertices. Every point strictly
inside the chord lies in the interior of the square, and the chord of a
square fitting [0, side]^2 lies in [0, side].
"""
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
    """Nested matches on the four decisions with leaf(None) for an empty chord and leaf((low, high)) otherwise."""
    lines = [(0, 'match left:'), (1, 'case Inl{+left}:'), (2, leaf(None)), (1, 'case Inr{left}:'), (2, 'match right:'),
             (3, 'case Inl{+right}:'), (4, leaf(None)), (3, 'case Inr{right}:'), (4, 'match low:')]
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


def chord_defs():
    v = accessors()
    inverses = {key: T(f'INV({v[key].bend})', 'i' + key) for key in ('s', 'c')}
    thresholds = ''.join(f'''
def Chords.{name}_end(TPL, {SQUARE}) -> F:
  {term.bend}
''' for name, term in thresholds_of(v).items())

    def leaf(sides):
        if sides is None:
            return 'I.Interval{ZERO, ZERO}'
        _, lo, hi = chord_ends(v, X, sides, inverses)
        return f'I.Interval{{{lo.bend}, {hi.bend}}}'

    decide = ', '.join(f'K.Field.le_decidable(F, field)({a.bend}, {b.bend})' for _, a, b in comparisons(X, THRESHOLDS))
    return thresholds + f'''
def Chords.chord_by(TPL, {SQUARE}, +x: F, {DECISIONS}) -> I.Intervals.Interval<F>:
{dispatch(leaf, 1)}
def Chords.chord(TPL, {SQUARE}, +x: F) -> I.Intervals.Interval<F>:
  Chords.chord_by(TC, square, x, {decide})
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
    inverses = {key: ctx.var('i' + key, f'INV({v[key].bend})') for key in ('s', 'c')}
    used, lo, hi = chord_ends(v, x, (low, high), inverses)
    for key in dict.fromkeys(used):
        positive = f'{key}_positive'
        steps += [('lt', positive, num(0), v[key]),
                  ('equation', v[key] * inverses[key], num(1),
                   f'AL.same_transitive(TC, MUL({v[key].bend}, INV({v[key].bend})), ONE, R.FieldRing.of_nat(TC, 1n), '
                   f'AL.mul_inverse(TC, {v[key].bend}, O.FieldOrder.lt_of(TC, ZERO, {v[key].bend}, {positive})), S.Scaling.one_is_number(TC))'),
                  ('le', f'{key}_inverse_nonnegative', num(0), inverses[key], [inverses[key]])]
    return SimpleNamespace(steps=steps, gaps=gaps, lo=lo, hi=hi, used=used, inverses=inverses)


def interior_leaf(sides):
    """The point (x, y) strictly inside the chord lies in the interior of the square."""
    ctx, v, h = accessor_context()
    cx, cy, c, s = v['cx'], v['cy'], v['c'], v['s']
    x, y = ctx.var('x', 'x'), ctx.var('y', 'y')
    signs(ctx, v)
    point = 'P.Point{x, y}'
    goal = f'P.Problem.InteriorContainment<F, field, square, {point}>'
    if sides is None:
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
    if sides is None:
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
    if sides is None:
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

def Chords.inside_at(TPL, {PACKING}, +x: F, +index: Nat, +bound: N.Natural.Le(1n+index, count)) ->
  I.Intervals.Inside(TC, ZERO, side, {at('index')}):
  Chords.inside(TC, {normal('index')}, side,
    M.Membership.first_quadrant_corners(TC, {square('index')}, side, M.Membership.corners_of(TC, {square('index')}, side, {fits}, {fits}, {fits}, {fits})),
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
    parts = [HEADER, chord_defs(), lemmas(), meet(), assembly()]
    (ROOT / 'bend' / 'Chords.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
