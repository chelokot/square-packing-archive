#!/usr/bin/env python3
"""Write bend/StromquistSix.bend: no six squares fit in a container of side less than 3.

A packing of at least six squares in side `side < 3` scales to six squares that fit [0, 3]^2 with
pairwise disjoint closed sets (bend/Scaling.bend). The facts about their key
points from bend/Stromquist.bend and bend/Singletons.bend feed the counting
core of bend/Incidence.bend, following StromquistSix.lean and Square6Exact.lean.
"""
import importlib.util

from bend_proof import ROOT, Context, expand, num


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ST = load('stromquist', 'generate-bend-stromquist.py')
IN = ST.INCIDENCE
ROWS = range(6)
THREE = ST.THREE
TPL6 = '~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>'
TC6 = '~F, ~field, ~count, ~side, ~packing'

HEADER = ST.HEADER + '''import ./bend-math/Natural.bend as N
import ./Stromquist.bend as Q
import ./Packings.bend as Pk
import ./Singletons.bend as L
'''


def index(i):
    return f'{i}n' if isinstance(i, int) else i


def index_bound(i):
    return 'Unit{}' if isinstance(i, int) else f'{i}_bound'


def normal(i):
    return f'StromquistSix.normal({TC6}, six, less, {index(i)})'


def square(i):
    return f'StromquistSix.square({TC6}, six, less, {index(i)})'


def args(i):
    """Square, corners and signs of the normal form of square i (a number or the name of a Nat)."""
    return (f'{normal(i)}, StromquistSix.corners({TC6}, six, less, {index(i)}, {index_bound(i)}), StromquistSix.cosine({TC6}, six, less, {index(i)}), '
            f'StromquistSix.sine({TC6}, six, less, {index(i)})')


def bit(i, point):
    return f'M.Membership.inside(TC, {normal(i)}, {point})'


def key(k):
    return f'Q.Stromquist.key{k}(TC)'


def disjoint(i, j, point, first, second):
    """Empty from containments of `point` in the normal forms of squares i and j, named a and b with a proof `apart`."""
    back = lambda k, c: f'Y.Symmetry.first_quadrant_contains_back(TC, {square(k)}, {point}, {c})'
    return (f'StromquistSix.disjoint({TC6}, six, less, {index(i)}, {index(j)}, {index_bound(i)}, {index_bound(j)}, '
            f'same => StromquistSix.different({index(i)}, {index(j)}, apart, same))({point}, {back(i, first)}, {back(j, second)})')


CLOSED = TC6
NONEMPTY = 'N.Natural.le_transitive(1n, 6n, count, Unit{}, six)'


def widen(index, bound):
    return f'N.Natural.le_transitive(1n+{index}, 6n, count, {bound}, six)'


ACCESSORS = f'''
def StromquistSix.square({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +index: Nat) -> P.Problem.Square<F, field>:
  S.Scaling.closed_square({CLOSED}, {THREE}, index)

def StromquistSix.normal({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +index: Nat) -> P.Problem.Square<F, field>:
  Y.Symmetry.first_quadrant(TC, S.Scaling.closed_square({CLOSED}, {THREE}, index))

def StromquistSix.corners({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +index: Nat, +bound: N.Natural.Le(1n+index, 6n)) ->
  M.Membership.Corners<F, field, StromquistSix.normal({TC6}, six, less, index), {THREE}>:
  M.Membership.first_quadrant_corners(TC, S.Scaling.closed_square({CLOSED}, {THREE}, index), {THREE},
    M.Membership.corners_of(TC, S.Scaling.closed_square({CLOSED}, {THREE}, index), {THREE},
      {', '.join([f"S.Scaling.closed_fits({CLOSED}, {THREE}, less, {NONEMPTY}, index, {widen('index', 'bound')})"] * 4)}))

def StromquistSix.cosine({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +index: Nat) ->
  LE(ZERO, P.Problem.cosine(F, field, StromquistSix.normal({TC6}, six, less, index))):
  C.Certificate.first(LE(ZERO, P.Problem.cosine(F, field, StromquistSix.normal({TC6}, six, less, index))),
    LE(ZERO, P.Problem.sine(F, field, StromquistSix.normal({TC6}, six, less, index))),
    Y.Symmetry.first_quadrant_signs(TC, S.Scaling.closed_square({CLOSED}, {THREE}, index)))

def StromquistSix.sine({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +index: Nat) ->
  LE(ZERO, P.Problem.sine(F, field, StromquistSix.normal({TC6}, six, less, index))):
  C.Certificate.second(LE(ZERO, P.Problem.cosine(F, field, StromquistSix.normal({TC6}, six, less, index))),
    LE(ZERO, P.Problem.sine(F, field, StromquistSix.normal({TC6}, six, less, index))),
    Y.Symmetry.first_quadrant_signs(TC, S.Scaling.closed_square({CLOSED}, {THREE}, index)))

def StromquistSix.disjoint({TPL6}, +six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE}), +left: Nat, +right: Nat,
  +left_bound: N.Natural.Le(1n+left, 6n), +right_bound: N.Natural.Le(1n+right, 6n), different: {{left == right : Nat}} -> Empty) ->
  @point: P.Problem.Point<F> -> P.Problem.Containment<F, field, StromquistSix.square({TC6}, six, less, left), point> ->
  P.Problem.Containment<F, field, StromquistSix.square({TC6}, six, less, right), point> -> Empty:
  S.Scaling.closed_disjoint({CLOSED}, {THREE}, less, {NONEMPTY}, left, right, {widen('left', 'left_bound')}, {widen('right', 'right_bound')}, different)
'''

LESS = f'+six: N.Natural.Le(6n, count), +less: O.FieldOrder.Strict(TC, side, {THREE})'
NONTRIVIAL = '+nontrivial: O.FieldOrder.Strict(TC, ZERO, ONE)'


def row(i):
    return f'Q.Stromquist.row(TC, {normal(i)})'


def apart_chain(i, j, points):
    """Holds(not(meet(...))) for two rows over the given point terms from closed disjointness."""
    def one(point):
        a, b = bit(i, point), bit(j, point)
        return (f'B.Bits.never_both({a}, {b}, +first => +second => '
                f'{disjoint(i, j, point, f"M.Membership.contains(TC, {normal(i)}, {point}, first)", f"M.Membership.contains(TC, {normal(j)}, {point}, second)")})')
    terms = [f'Bool.and({bit(i, p)}, {bit(j, p)})' for p in points]
    proof = 'Unit{}'
    rest = 'False{}'
    for p, t in reversed(list(zip(points, terms))):
        proof = f'B.Bits.neither({t}, {rest}, {one(p)}, {proof})'
        rest = f'Bool.or({t}, {rest})'
    return proof


PAIR = '+a: Nat, +b: Nat, +a_bound: N.Natural.Le(1n+a, 6n), +b_bound: N.Natural.Le(1n+b, 6n), +apart: B.Bits.Holds(Bool.not(Nat.is_eq(a, b)))'


def key_apart():
    return f'''
def StromquistSix.key_apart({TPL6}, {LESS}, {PAIR}) -> B.Bits.Holds(Bool.not(B.Bits.meet({row('a')}, {row('b')}))):
  {apart_chain('a', 'b', [key(k) for k in range(9)])}
'''


def extra_apart(orientation):
    points = [ST.point_term(v) for v in ST.extra_points(orientation)]
    rows = lambda name: f'Q.Stromquist.extra_row_{orientation}(TC, {normal(name)})'
    return f'''
def StromquistSix.extra_apart_{orientation}({TPL6}, {LESS}, {PAIR}) -> B.Bits.Holds(Bool.not(B.Bits.meet({rows('a')}, {rows('b')}))):
  {apart_chain('a', 'b', points)}
'''


def lefts(items, proof):
    """Holds of each conjunct of the and-chain of items from Holds of the chain."""
    out = []
    rest = proof
    for n, item in enumerate(items[:-1]):
        tail = IN.ands(items[n + 1:])
        out.append(f'B.Bits.left({item}, {tail}, {rest})')
        rest = f'B.Bits.right({item}, {tail}, {rest})'
    out.append(rest)
    return out


def bits_of(i):
    return ', '.join(bit(i, key(k)) for k in range(9))


def perimeter(i):
    return f'Q.Stromquist.perimeter(TC, {args(i)}, nontrivial)'


from fractions import Fraction

SG = load('singletons', 'generate-bend-singletons.py')
ST.SELF['name'] = 'Q.Stromquist.'
KEY_VALUES = ST.KEY_VALUES
CORNER_KEYS = (0, 2, 6, 8)
D4 = [[], ['reflect_x'], ['reflect_y'], ['reflect_x', 'reflect_y'], ['swap'], ['swap', 'reflect_x'], ['swap', 'reflect_y'],
      ['swap', 'reflect_x', 'reflect_y']]


def symmetry_to_base(corner, middle):
    """The symmetry that moves the given corner and middle keys to the base pair (1, 1), (3/2, 1)."""
    for ops in D4:
        transport = ST.Transport(ops, None)
        if transport.image(KEY_VALUES[corner]) == KEY_VALUES[0] and transport.image(KEY_VALUES[middle]) == KEY_VALUES[1]:
            return ops
    raise ValueError((corner, middle))


def key_of(values):
    return KEY_VALUES.index(values)


GENERIC = f'''
def StromquistSix.is_eq_self(n: Nat) -> B.Bits.Holds(Nat.is_eq(n, n)):
  match n:
    case 0n:
      Unit{{}}
    case 1n+p:
      StromquistSix.is_eq_self(p)

def StromquistSix.apart_swap(left: Nat, right: Nat, +apart: B.Bits.Holds(Bool.not(Nat.is_eq(left, right)))) ->
  B.Bits.Holds(Bool.not(Nat.is_eq(right, left))):
  match left right:
    case 0n 0n:
      apart
    case 0n 1n+q:
      Unit{{}}
    case 1n+p 0n:
      Unit{{}}
    case 1n+p 1n+q:
      StromquistSix.apart_swap(p, q, apart)

def StromquistSix.different(+left: Nat, +right: Nat, +apart: B.Bits.Holds(Bool.not(Nat.is_eq(left, right))), same: {{left == right : Nat}}) -> Empty:
  B.Bits.never(Nat.is_eq(right, right), StromquistSix.is_eq_self(right),
    B.Bits.transport(Bool.not(Nat.is_eq(left, right)), Bool.not(Nat.is_eq(right, right)),
      Equal.cong(Nat, Bool, x => Bool.not(Nat.is_eq(x, right)), left, right, same), apart))
'''


def generic_square(name):
    return f'StromquistSix.normal({TC6}, six, less, {name})'


def generic_args(name):
    return (f'{generic_square(name)}, StromquistSix.corners({TC6}, six, less, {name}, {name}_bound), StromquistSix.cosine({TC6}, six, less, {name}), '
            f'StromquistSix.sine({TC6}, six, less, {name})')


def meet(corner, middle):
    """Two squares holding only the adjacent keys `corner` and `middle` share a point (StromquistSixSingletons.lean)."""
    ops = symmetry_to_base(corner, middle)
    a, b = (ST.Transport(ops, None, generic_square(name), f'StromquistSix.corners({TC6}, six, less, {name}, {name}_bound)') for name in 'ab')
    a.ctx, b.ctx = (ST.Square(t.normal, t.signs) for t in (a, b))
    pre = lambda t, k: key_of(t.preimage(KEY_VALUES[k]))
    alone = lambda name, k: f'I.Incidence.alone{k}({", ".join(f"M.Membership.inside(TC, {generic_square(name)}, {key(x)})" for x in range(9))}, {name}_single, {name}_key)'
    def alone_part(name, k, x):
        others = [y for y in range(9) if y != k]
        items = [f'Bool.not(M.Membership.inside(TC, {generic_square(name)}, {key(y)}))' for y in others]
        return lefts(items, alone(name, k))[others.index(x)]
    contains = lambda name, k, holds: f'M.Membership.contains(TC, {generic_square(name)}, {key(k)}, {holds})'
    arguments = [a.normal, a.corners, a.signs[0], a.signs[1], b.normal, b.corners, b.signs[0], b.signs[1],
                 a.forward(KEY_VALUES[corner], contains('a', corner, 'a_key')), a.outside(KEY_VALUES[pre(a, 3)], alone_part('a', corner, pre(a, 3))),
                 b.forward(KEY_VALUES[middle], contains('b', middle, 'b_key'))]
    arguments += [b.outside(KEY_VALUES[pre(b, k)], alone_part('b', middle, pre(b, k))) for k in (0, 2, 4)]
    call = f'L.Singletons.meet_base(TC, {", ".join(arguments)})'
    right_point, down_point = SG.meet_points()
    right_point = right_point.replace('SQUARE_B', b.normal)
    down_point = down_point.replace('SQUARE_B', b.normal)
    contained = lambda square, point: f'P.Problem.Containment<F, field, {square}, {point}>'
    both = lambda point: f'C.Certificate.Both<{contained(a.normal, point)}, {contained(b.normal, point)}>'

    def finish(point, name):
        first, moved = a.backward_any(point, f'C.Certificate.first({contained(a.normal, point)}, {contained(b.normal, point)}, {name})')
        second, _ = b.backward_any(point, f'C.Certificate.second({contained(a.normal, point)}, {contained(b.normal, point)}, {name})')
        back = lambda k, c: f'Y.Symmetry.first_quadrant_contains_back(TC, StromquistSix.square({TC6}, six, less, {k}), {moved}, {c})'
        return (f'StromquistSix.disjoint({TC6}, six, less, a, b, a_bound, b_bound, same => StromquistSix.different(a, b, apart, same))'
                f'({moved}, {back("a", first)}, {back("b", second)})')
    single = lambda name: f'I.Incidence.single(Q.Stromquist.row(TC, {generic_square(name)}))'
    return f'''
def StromquistSix.meet{corner}_{middle}({TPL6}, {LESS}, +a: Nat, +b: Nat, +a_bound: N.Natural.Le(1n+a, 6n), +b_bound: N.Natural.Le(1n+b, 6n),
  +apart: B.Bits.Holds(Bool.not(Nat.is_eq(a, b))), +a_single: B.Bits.Holds({single("a")}), +a_key: B.Bits.Holds(M.Membership.inside(TC, {generic_square("a")}, {key(corner)})),
  +b_single: B.Bits.Holds({single("b")}), +b_key: B.Bits.Holds(M.Membership.inside(TC, {generic_square("b")}, {key(middle)}))) -> Empty:
  M.Membership.either({both(right_point)}, {both(down_point)}, Empty, {call}, +right => {finish(right_point, "right")}, +down => {finish(down_point, "down")})
'''


def single(i):
    return f'I.Incidence.single({row(i)})'


def bound(i):
    return 'Unit{}'


def lonely_pair():
    i, j = 'a', 'b'
    """No two squares hold single adjacent key points."""
    s_i, s_j = single(i), single(j)
    touches = lambda pairs: f'B.Bits.touches({pairs}, {row(i)}, {row(j)})'
    def pairs_term(pairs):
        return IN.chain(lambda p, rest: f'B.MorePairs{{{p[0]}n, {p[1]}n, {rest}}}', pairs, 'B.NoPairs{}')

    def case(p, q, holds):
        bp = f'B.Bits.left({bit(i, key(p))}, {bit(j, key(q))}, {holds})'
        bq = f'B.Bits.right({bit(i, key(p))}, {bit(j, key(q))}, {holds})'
        if p == 4:
            return (f'B.Bits.never(Bool.and({s_i}, {bit(i, key(4))}), B.Bits.both({s_i}, {bit(i, key(4))}, single_i, {bp}), '
                    f'I.Incidence.single_not_center({bits_of(i)}, {perimeter(i)}))')
        if q == 4:
            return (f'B.Bits.never(Bool.and({s_j}, {bit(j, key(4))}), B.Bits.both({s_j}, {bit(j, key(4))}, single_j, {bq}), '
                    f'I.Incidence.single_not_center({bits_of(j)}, {perimeter(j)}))')
        if p in CORNER_KEYS:
            return f'StromquistSix.meet{p}_{q}({TC6}, six, less, a, b, a_bound, b_bound, apart, single_i, {bp}, single_j, {bq})'
        return (f'StromquistSix.meet{q}_{p}({TC6}, six, less, b, a, b_bound, a_bound, StromquistSix.apart_swap(a, b, apart), '
                f'single_j, {bq}, single_i, {bp})')

    def eliminate(k, holds):
        if k == len(IN.ORDERED):
            return holds
        p, q = IN.ORDERED[k]
        here = f'Bool.and({bit(i, key(p))}, {bit(j, key(q))})'
        rest = touches(pairs_term(IN.ORDERED[k + 1:]))
        return (f'M.Membership.either(B.Bits.Holds({here}), B.Bits.Holds({rest}), Empty, B.Bits.either({here}, {rest}, {holds}), '
                f'+found{k} => {case(p, q, f"found{k}")}, +later{k} => {eliminate(k + 1, f"later{k}")})')
    t = touches('I.Incidence.adjacent()')
    inner = f'Bool.and({s_j}, {t})'
    body = (f'M.Membership.bind(B.Bits.Holds({s_i}), Empty, B.Bits.left({s_i}, {inner}, holds), +single_i => '
            f'M.Membership.bind(B.Bits.Holds({s_j}), Empty, B.Bits.left({s_j}, {t}, B.Bits.right({s_i}, {inner}, holds)), +single_j => '
            f'{eliminate(0, f"B.Bits.right({s_j}, {t}, B.Bits.right({s_i}, {inner}, holds))")}))')
    return f'''
def StromquistSix.lonely_pair({TPL6}, {LESS}, {NONTRIVIAL}, {PAIR}) -> B.Bits.Holds(Bool.not(I.Incidence.lonely({row(i)}, {row(j)}))):
  B.Bits.not_of(I.Incidence.lonely({row(i)}, {row(j)}), +holds => {body})
'''


CENTER_OF = {7: 'north', 1: 'south', 5: 'east', 3: 'west'}


def center_pattern(n):
    """No square holds exactly the centre and the neighbour n (StromquistSix.lean, no_closed_family_center_pair)."""
    names = NAMES
    literals = [bit('i', key(k)) if k in (4, n) else f'Bool.not({bit("i", key(k))})' for k in range(9)]
    holds = lefts(literals, 'holds')
    orientation = CENTER_OF[n]
    transport = ST.Transport(ST.CENTER_ORIENTATIONS[orientation], None)
    missing = [key_of(transport.preimage(v)) for v in ST.NORTH['missing']]
    points = [ST.point_term(v) for v in ST.extra_points(orientation)]
    lemma = lambda index: (f'Q.Stromquist.center_{orientation}{index}(TC, {args("i")}, nontrivial, '
                           f'M.Membership.contains(TC, {normal("i")}, {key(4)}, {holds[4]}), M.Membership.contains(TC, {normal("i")}, {key(n)}, {holds[n]}), '
                           + ', '.join(holds[m] for m in missing) + ')')
    bits = ', '.join(bit(r, point) for r in names for point in points)
    anys = ', '.join(f'Q.Stromquist.extra_{orientation}(TC, {args(r)}, nontrivial)' for r in names[1:])
    marked = [bit('i', points[k]) for k in (1, 3, 4, 5)]
    crowd = (f'B.Bits.both({marked[0]}, {IN.ands(marked[1:])}, {holds[n]}, B.Bits.both({marked[1]}, {IN.ands(marked[2:])}, '
             f'M.Membership.inside_of(TC, {normal("i")}, {points[3]}, {lemma(0)}), B.Bits.both({marked[2]}, {marked[3]}, '
             f'M.Membership.inside_of(TC, {normal("i")}, {points[4]}, {lemma(1)}), {holds[4]})))')
    aparts = ', '.join(f'StromquistSix.extra_apart_{orientation}({TC6}, six, less, {names[x]}, {names[y]}, {names[x]}_bound, {names[y]}_bound, apart{x}_{y})'
                       for x, y in PAIRS)
    return f'''
def StromquistSix.center_pattern{n}({TPL6}, {LESS}, {NONTRIVIAL}, {ROWS_PARAMS}, +holds: B.Bits.Holds({IN.ands(literals)})) -> Empty:
  I.Incidence.crowded({bits}, {anys}, {crowd}, {aparts})
'''


NAMES = ['i'] + [f'r{k}' for k in range(1, 6)]
PAIRS = [(x, y) for x in range(6) for y in range(x + 1, 6)]
ROWS_PARAMS = ', '.join([f'+{r}: Nat, +{r}_bound: N.Natural.Le(1n+{r}, 6n)' for r in NAMES]
                        + [f'+apart{x}_{y}: B.Bits.Holds(Bool.not(Nat.is_eq({NAMES[x]}, {NAMES[y]})))' for x, y in PAIRS])
ROWS_ARGS = ', '.join([f'{r}, {r}_bound' for r in NAMES] + [f'apart{x}_{y}' for x, y in PAIRS])


def center():
    """No square holds the centre with one neighbour and nothing else."""
    terms = [IN.ands([bit('i', key(k)) if k in (4, n) else f'Bool.not({bit("i", key(k))})' for k in range(9)]) for n in IN.NEIGHBOURS]
    proof = None
    for k in reversed(range(len(terms))):
        n = IN.NEIGHBOURS[k]
        here = f'B.Bits.not_of({terms[k]}, +holds => StromquistSix.center_pattern{n}({TC6}, six, less, nontrivial, {ROWS_ARGS}, holds))'
        proof = here if proof is None else f'B.Bits.neither({terms[k]}, {IN.ors(terms[k + 1:])}, {here}, {proof})'
    return f'''
def StromquistSix.center({TPL6}, {LESS}, {NONTRIVIAL}, {ROWS_PARAMS}) -> B.Bits.Holds(Bool.not(I.Incidence.center_pair({row('i')}))):
  {proof}
'''


def center_of(i):
    order = [i] + [r for r in ROWS if r != i]
    rows = ', '.join(f'{r}n, Unit{{}}' for r in order) + ', ' + ', '.join('Unit{}' for x in range(6) for y in range(x + 1, 6))
    return f'StromquistSix.center({TC6}, six, less, nontrivial, {rows})'


def final():
    bits = ', '.join(bit(i, key(k)) for i in ROWS for k in range(9))
    facts = ([perimeter(i) for i in ROWS] + [f'Q.Stromquist.pair_ok(TC, {args(i)})' for i in ROWS]
             + [center_of(i) for i in ROWS]
             + [f'StromquistSix.key_apart({TC6}, six, less, {i}n, {j}n, Unit{{}}, Unit{{}}, Unit{{}})' for i in ROWS for j in ROWS if i != j]
             + [f'StromquistSix.lonely_pair({TC6}, six, less, nontrivial, {i}n, {j}n, Unit{{}}, Unit{{}}, Unit{{}})' for i in ROWS for j in ROWS if i != j])
    ctx = Context()
    one = ctx.var('one', 'ONE')
    ctx.equal(one, num(1), 'S.Scaling.one_is_number(TC)')
    ctx.below(one, num(0), 'collapsed')
    broken = ctx.le(num(0), -num(1))
    return f'''
def StromquistSix.nontrivial({TPL6}, {LESS}) -> O.FieldOrder.Strict(TC, ZERO, ONE):
  M.Membership.by_cases(TC, ONE, ZERO, O.FieldOrder.Strict(TC, ZERO, ONE),
    +collapsed => Empty.absurd(O.FieldOrder.Strict(TC, ZERO, ONE),
      O.FieldOrder.lt_of(TC, side, {THREE}, less)(S.Scaling.anything(TC, {THREE}, side, {broken}))),
    +positive => positive)

def StromquistSix.lower_bound({TPL6}, +six: N.Natural.Le(6n, count)) -> LE({THREE}, side):
  M.Membership.by_cases(TC, {THREE}, side, LE({THREE}, side), +enough => enough,
    +less => Empty.absurd(LE({THREE}, side), M.Membership.bind(O.FieldOrder.Strict(TC, ZERO, ONE), Empty, StromquistSix.nontrivial({TC6}, six, less),
      +nontrivial => I.Incidence.impossible({bits}, {", ".join(facts)}))))
'''


def main():
    pairs = [(i, j) for i in ROWS for j in ROWS if i != j]
    corner_pairs = [(c, m) for c in CORNER_KEYS for m in range(9) if m != 4 and ((c, m) in IN.ADJACENT or (m, c) in IN.ADJACENT)]
    parts = ([HEADER, ACCESSORS, GENERIC, key_apart()] + [extra_apart(o) for o in ST.CENTER_ORIENTATIONS]
             + [meet(c, m) for c, m in corner_pairs] + [lonely_pair()] + [center_pattern(n) for n in IN.NEIGHBOURS]
             + [center(), final()])
    (ROOT / 'bend' / 'StromquistSix.bend').write_text(expand(''.join(parts)))


if __name__ == '__main__':
    main()
