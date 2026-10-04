#!/usr/bin/env python3
"""Write bend/Incidence.bend: the counting core of Stromquist's s(6) argument.

Six rows of nine bits record which key points of the 3 by 3 grid each square
contains.  From facts about single rows and pairs of rows the core derives a
contradiction, following StromquistSixIncidence.lean: rows that hold a single
point form an independent set of the perimeter, so there are three or four of
them, and either case forces two rows through the centre or a row equal to the
centre and one neighbour.
"""
import itertools
import pathlib

ROWS = 6
POINTS = 9
CENTER = 4
ADJACENT = [(0, 1), (1, 2), (3, 4), (4, 5), (6, 7), (7, 8), (0, 3), (3, 6), (1, 4), (4, 7), (2, 5), (5, 8)]
ORDERED = ADJACENT + [(b, a) for a, b in ADJACENT]
CYCLE = [(a, b) for a, b in ADJACENT if CENTER not in (a, b)]
NEIGHBOURS = [b for a, b in ADJACENT if a == CENTER] + [a for a, b in ADJACENT if b == CENTER]
REFLECTIONS = [lambda k: k, lambda k: 3 * (k // 3) + 2 - k % 3, lambda k: 3 * (2 - k // 3) + k % 3, lambda k: 3 * (k % 3) + k // 3]
BASE_PAIRS = {(0, 2): [1], (0, 4): [1, 3], (0, 5): [1, 4], (0, 7): [3, 4], (0, 8): [1, 7], (1, 5): [2, 4],
              (1, 8): [4, 5], (3, 5): [4], (3, 7): [4, 6], (3, 8): [4, 7], (4, 8): [5, 7], (6, 8): [7]}


def pair_clauses():
    found = {}
    frontier = dict(BASE_PAIRS)
    while frontier:
        found.update(frontier)
        frontier = {}
        for (a, b), xs in found.items():
            for reflect in REFLECTIONS:
                key = tuple(sorted((reflect(a), reflect(b))))
                if key not in found and key not in frontier:
                    frontier[key] = sorted(reflect(x) for x in xs)
    return dict(sorted(found.items()))


PAIRS = pair_clauses()
assert len(PAIRS) == 36 - len(ADJACENT)


def nat(n):
    return f'{n}n'


def ands(items):
    out = items[-1]
    for item in reversed(items[:-1]):
        out = f'Bool.and({item}, {out})'
    return out


def ors(items):
    out = items[-1]
    for item in reversed(items[:-1]):
        out = f'Bool.or({item}, {out})'
    return out


def get(v, k):
    return f'B.Bits.get({v}, {nat(k)})'


def chain(constructor, items, end):
    out = end
    for item in reversed(items):
        out = constructor(item, out)
    return out


ADJACENT_TERM = chain(lambda p, rest: f'B.MorePairs{{{nat(p[0])}, {nat(p[1])}, {rest}}}', ORDERED, 'B.NoPairs{}')

DEFINITIONS = f'''def Incidence.row({', '.join(f'+b{k}: Bool' for k in range(POINTS))}) -> List<&2, Bool>:
  {chain(lambda b, rest: f'Con{{{b}, {rest}}}', [f'b{k}' for k in range(POINTS)], 'Nil{}')}

def Incidence.adjacent() -> B.Bits.Pairs:
  {ADJACENT_TERM}

def Incidence.single(+v: List<&2, Bool>) -> Bool:
  Nat.is_eq(B.Bits.count(v), 1n)

def Incidence.noncenter(+v: List<&2, Bool>) -> Bool:
  {ors([get('v', k) for k in range(POINTS) if k != CENTER])}

def Incidence.pair_ok(+v: List<&2, Bool>) -> Bool:
  {ands([f"Bool.or(Bool.not(Bool.and({get('v', a)}, {get('v', b)})), {ors([get('v', x) for x in xs])})" for (a, b), xs in PAIRS.items()])}

def Incidence.center_pair(+v: List<&2, Bool>) -> Bool:
  {ors([ands([get('v', k) if k in (CENTER, n) else f"Bool.not({get('v', k)})" for k in range(POINTS)]) for n in NEIGHBOURS])}

def Incidence.lonely(+v: List<&2, Bool>, +w: List<&2, Bool>) -> Bool:
  Bool.and(Incidence.single(v), Bool.and(Incidence.single(w), B.Bits.touches(Incidence.adjacent(), v, w)))

def Incidence.independent(+w: List<&2, Bool>) -> Bool:
  Bool.and(Bool.not({get('w', CENTER)}), Bool.not(B.Bits.touches(Incidence.adjacent(), w, w)))

def Incidence.covered(+w: List<&2, Bool>) -> Bool:
  {ands([f"Bool.or({get('w', a)}, {get('w', b)})" for a, b in CYCLE])}

def Incidence.no_cycle_edge(+v: List<&2, Bool>) -> Bool:
  {ands([f"Bool.not(Bool.and({get('v', a)}, {get('v', b)}))" for a, b in CYCLE])}
'''


def single(v):
    return sum(v) == 1


def touches(v, w):
    return any(v[p] and w[q] for p, q in ORDERED)


PREDICATES = {
    'noncenter': lambda v: any(v[k] for k in range(POINTS) if k != CENTER),
    'pair_ok': lambda v: all(not (v[a] and v[b]) or any(v[x] for x in xs) for (a, b), xs in PAIRS.items()),
    'center_pair': lambda v: any(all(v[k] == (k in (CENTER, n)) for k in range(POINTS)) for n in NEIGHBOURS),
    'independent': lambda w: not w[CENTER] and not touches(w, w),
    'covered': lambda w: all(w[a] or w[b] for a, b in CYCLE),
    'no_cycle_edge': lambda v: all(not (v[a] and v[b]) for a, b in CYCLE),
}
R = 'Incidence.row(' + ', '.join(f'v{k}' for k in range(POINTS)) + ')'


def holds(name):
    return (f'B.Bits.Holds(Incidence.{name}({R}))', PREDICATES[name])


def enumeration(name, hypotheses, conclusion):
    claim, check = conclusion
    params = ', '.join([f'+v{k}: Bool' for k in range(POINTS)] + [f'h{i}: {t}' for i, (t, _) in enumerate(hypotheses)])
    lines = [f'def Incidence.{name}({params}) ->', f'  {claim}:']

    lines.append('  match ' + ' '.join(f'v{k}' for k in range(POINTS)) + ':')
    for bits in itertools.product([False, True], repeat=POINTS):
        bits = list(bits)
        lines.append('    case ' + ' '.join('True{}' if b else 'False{}' for b in bits) + ':')
        failed = [i for i, (_, test) in enumerate(hypotheses) if not test(bits)]
        if failed:
            lines.append(f'      match h{failed[0]}:')
        else:
            assert check(bits), (name, bits)
            lines.append('      Unit{}')
    return '\n'.join(lines) + '\n'


def le(a, b, test):
    return (f'N.Natural.Le({a}, {b})', test)


COUNT = f'B.Bits.count({R})'
SINGLE = f'Incidence.single({R})'
ENUMERATIONS = [
    enumeration('single_not_center', [holds('noncenter')],
                (f'B.Bits.Holds(Bool.not(Bool.and({SINGLE}, {get(R, CENTER)})))', lambda v: not (single(v) and v[CENTER]))),
    enumeration('lower_count', [holds('noncenter')],
                le('2n', f'Nat.add({COUNT}, B.Bits.n({SINGLE}))', lambda v: sum(v) + single(v) >= 2)),
    enumeration('single_alone', [],
                (f'B.Bits.Holds(Bool.not(Bool.and({SINGLE}, Bool.and({SINGLE}, B.Bits.touches(Incidence.adjacent(), {R}, {R})))))',
                 lambda v: not (single(v) and touches(v, v)))),
    enumeration('independent_at_most_four', [holds('independent')], le(COUNT, '4n', lambda v: sum(v) <= 4)),
    enumeration('independent_four_covers', [holds('independent'), le('4n', COUNT, lambda v: sum(v) >= 4)], holds('covered')),
    enumeration('center_or_single', [holds('noncenter'), holds('pair_ok'), holds('no_cycle_edge')],
                (f'B.Bits.Holds(Bool.or({SINGLE}, {get(R, CENTER)}))', lambda v: single(v) or v[CENTER])),
    enumeration('full_has_center', [le('9n', COUNT, lambda v: sum(v) >= 9)], (f'B.Bits.Holds({get(R, CENTER)})', lambda v: v[CENTER])),
    enumeration('center_pair_of', [holds('noncenter'), holds('pair_ok'), (f'B.Bits.Holds({get(R, CENTER)})', lambda v: v[CENTER]),
                                   le(f'Nat.add({COUNT}, B.Bits.n({SINGLE}))', '2n', lambda v: sum(v) + single(v) <= 2)],
                holds('center_pair')),
]


def edge_free():
    lines = ['def Incidence.edge_free(wu: Bool, wv: Bool, vu: Bool, vv: Bool, covered: B.Bits.Holds(Bool.or(wu, wv)),',
             '  first: B.Bits.Holds(Bool.not(Bool.and(wu, vu))), second: B.Bits.Holds(Bool.not(Bool.and(wv, vv)))) ->',
             '  B.Bits.Holds(Bool.not(Bool.and(vu, vv))):', '  match wu wv vu vv:']
    for wu, wv, vu, vv in itertools.product([False, True], repeat=4):
        lines.append('    case ' + ' '.join('True{}' if x else 'False{}' for x in (wu, wv, vu, vv)) + ':')
        if not (wu or wv):
            lines.append('      match covered:')
        elif wu and vu:
            lines.append('      match first:')
        elif wv and vv:
            lines.append('      match second:')
        else:
            assert not (vu and vv)
            lines.append('      Unit{}')
    return '\n'.join(lines) + '\n'


def conjuncts(items, proof):
    out = []
    rest = proof
    for i, item in enumerate(items[:-1]):
        tail = ands(items[i + 1:])
        out.append(f'B.Bits.left({item}, {tail}, {rest})')
        rest = f'B.Bits.right({item}, {tail}, {rest})'
    out.append(rest)
    return out


def avoid_cycle():
    w = 'Incidence.row(' + ', '.join(f'w{k}' for k in range(POINTS)) + ')'
    params = ', '.join([f'+w{k}: Bool' for k in range(POINTS)] + [f'+v{k}: Bool' for k in range(POINTS)]
                       + [f'+covered: B.Bits.Holds(Incidence.covered({w}))']
                       + [f'+apart{k}: B.Bits.Holds(Bool.not(Bool.and(w{k}, v{k})))' for k in range(POINTS)])
    edges = [f'Bool.or(w{a}, w{b})' for a, b in CYCLE]
    parts = conjuncts(edges, 'covered')
    proofs = [f'Incidence.edge_free(w{a}, w{b}, v{a}, v{b}, {parts[i]}, apart{a}, apart{b})' for i, (a, b) in enumerate(CYCLE)]
    goals = [f'Bool.not(Bool.and(v{a}, v{b}))' for a, b in CYCLE]
    proof = proofs[-1]
    for i in reversed(range(len(goals) - 1)):
        proof = f'B.Bits.both({goals[i]}, {ands(goals[i + 1:])}, {proofs[i]}, {proof})'
    return f'def Incidence.avoid_cycle({params}) ->\n  B.Bits.Holds(Incidence.no_cycle_edge({R})):\n  {proof}\n'


def three_or_four():
    return '''def Incidence.three_or_four(s: Nat, low: N.Natural.Le(3n, s), high: N.Natural.Le(s, 4n)) -> Or({s == 3n : Nat}, {s == 4n : Nat}):
  match s:
    case 0n:
      match low:
    case 1n+a:
      match a:
        case 0n:
          match low:
        case 1n+b:
          match b:
            case 0n:
              match low:
            case 1n+c:
              match c:
                case 0n:
                  Inl{{==}}
                case 1n+d:
                  match d:
                    case 0n:
                      Inr{{==}}
                    case 1n+e:
                      match high:
'''


def bit(i, k):
    return f'b{i}_{k}'


def row_term(i):
    return 'Incidence.row(' + ', '.join(bit(i, k) for k in range(POINTS)) + ')'


PAIRS_OF_ROWS = [(i, j) for i in range(ROWS) for j in range(ROWS) if i != j]
FACTS = ([(f'noncenter{i}', f'B.Bits.Holds(Incidence.noncenter({row_term(i)}))') for i in range(ROWS)]
         + [(f'pair_ok{i}', f'B.Bits.Holds(Incidence.pair_ok({row_term(i)}))') for i in range(ROWS)]
         + [(f'center{i}', f'B.Bits.Holds(Bool.not(Incidence.center_pair({row_term(i)})))') for i in range(ROWS)]
         + [(f'apart{i}_{j}', f'B.Bits.Holds(Bool.not(B.Bits.meet({row_term(i)}, {row_term(j)})))') for i, j in PAIRS_OF_ROWS]
         + [(f'lonely{i}_{j}', f'B.Bits.Holds(Bool.not(Incidence.lonely({row_term(i)}, {row_term(j)})))') for i, j in PAIRS_OF_ROWS])
BITS = [bit(i, k) for i in range(ROWS) for k in range(POINTS)]
PARAMS = ', '.join([f'+{b}: Bool' for b in BITS] + [f'+{name}: {kind}' for name, kind in FACTS])
ARGS = ', '.join(BITS + [name for name, _ in FACTS])


def bits_of(i):
    return ', '.join(bit(i, k) for k in range(POINTS))


def gets(v):
    return ', '.join(get(v, k) for k in range(POINTS))


def prefix(name, first, i):
    return first if i == 0 else f'{name}{i}'


LETS = ''.join(f'  +r{i}: List<&2, Bool> = {row_term(i)}\n' for i in range(ROWS))
LETS += ''.join(f'  +s{i}: Bool = Incidence.single(r{i})\n' for i in range(ROWS))
LETS += ''.join(f'  +m{i}: List<&2, Bool> = B.Bits.mask(s{i}, r{i})\n' for i in range(ROWS))
LETS += ''.join(f'  +c{i}: List<&2, Bool> = Con{{{bit(i, CENTER)}, Nil{{}}}}\n' for i in range(ROWS))
for name, part in (('U', 'r'), ('S', 'm'), ('C', 'c')):
    for i in range(1, ROWS):
        LETS += f'  +{name}{i}: List<&2, Bool> = B.Bits.union({prefix(name, part + "0", i - 1)}, {part}{i})\n'

ATOMS = ([f'B.Bits.count(r{i})' for i in range(ROWS)] + [f'B.Bits.n(s{i})' for i in range(ROWS)]
         + [f'B.Bits.count(U{i})' for i in range(1, ROWS)] + [f'B.Bits.count(m{i})' for i in range(ROWS)]
         + [f'B.Bits.count(S{i})' for i in range(1, ROWS)] + [f'B.Bits.n(Bool.or(s{i}, {bit(i, CENTER)}))' for i in range(ROWS)]
         + [f'B.Bits.n({bit(i, CENTER)})' for i in range(ROWS)] + [f'B.Bits.count(C{i})' for i in range(1, ROWS)])
INDEX = {atom: i for i, atom in enumerate(ATOMS)}
LETS += '  +values: R.Ring.Values = ' + chain(lambda a, rest: f'R.Value{{{a}, {rest}}}', ATOMS, 'R.NoValues{}') + '\n'


def atom(text):
    return ('atom', INDEX[text])


def const(n):
    return ('const', n)


def plus(*terms):
    out = terms[-1]
    for term in reversed(terms[:-1]):
        out = ('sum', term, out)
    return out


def expr(tree):
    if tree[0] == 'atom':
        return f'R.Atom{{{nat(tree[1])}}}'
    if tree[0] == 'const':
        return f'R.Constant{{{nat(tree[1])}}}'
    return f'R.Sum{{{expr(tree[1])}, {expr(tree[2])}}}'


def linear(tree):
    if tree[0] == 'atom':
        return {tree[1]: 1}
    if tree[0] == 'const':
        return {'one': tree[1]} if tree[1] else {}
    out = dict(linear(tree[1]))
    for key, value in linear(tree[2]).items():
        out[key] = out.get(key, 0) + value
    return out


def combine(forms, sign=1):
    out = {}
    for form in forms:
        for key, value in form.items():
            out[key] = out.get(key, 0) + sign * value
    return {key: value for key, value in out.items() if value}


def tree_of(form):
    terms = []
    for key, value in sorted(form.items(), key=lambda item: str(item[0])):
        assert value > 0, form
        terms.append(const(value) if key == 'one' else (('atom', key) if value == 1 else ('product', value, key)))
    return terms


def form_expr(form):
    terms = tree_of(form)
    if not terms:
        return 'R.Constant{0n}'

    def one(term):
        if term[0] == 'product':
            return f'R.Product{{R.Constant{{{nat(term[1])}}}, R.Atom{{{nat(term[2])}}}}}'
        return expr(term)
    out = one(terms[-1])
    for term in reversed(terms[:-1]):
        out = f'R.Sum{{{one(term)}, {out}}}'
    return out


def summed(facts):
    left = facts[-1][0]
    right = facts[-1][1]
    proof = facts[-1][2]
    for lhs, rhs, fact in reversed(facts[:-1]):
        proof = (f'N.Natural.le_add_inequalities(R.Ring.eval(values, {expr(lhs)}), R.Ring.eval(values, {expr(rhs)}), '
                 f'R.Ring.eval(values, {expr(left)}), R.Ring.eval(values, {expr(right)}), {fact}, {proof})')
        left = ('sum', lhs, left)
        right = ('sum', rhs, right)
    return left, right, proof


def refute(facts):
    left, right, proof = summed(facts)
    slack = combine([linear(left), linear(right)], 1)
    slack = combine([linear(left), {key: -value for key, value in linear(right).items()}, {'one': -1}])
    return f'R.Ring.refute(values, {expr(left)}, {expr(right)}, {form_expr(slack)}, {proof}, {{==}})'


def cancel(facts, smaller, larger):
    left, right, proof = summed(facts)
    common = combine([linear(left), {key: -value for key, value in linear(smaller).items()}])
    other = combine([linear(right), {key: -value for key, value in linear(larger).items()}])
    assert common == other, (common, other)
    return (f'R.Ring.cancel(values, {expr(left)}, {expr(right)}, {form_expr(common)}, {expr(smaller)}, {expr(larger)}, '
            f'{proof}, {{==}}, {{==}})')


def k(i):
    return atom(f'B.Bits.count(r{i})')


def n(i):
    return atom(f'B.Bits.n(s{i})')


def total(name, first, i):
    return first(0) if i == 0 else atom(f'B.Bits.count({name}{i})')


SN = plus(*[n(i) for i in range(ROWS)])
SN_NAT = chain(lambda a, rest: f'Nat.add({a}, {rest})', [f'B.Bits.n(Incidence.single({row_term(i)}))' for i in range(ROWS - 1)],
               f'B.Bits.n(Incidence.single({row_term(ROWS - 1)}))')


def apart_rows(i, j):
    return f'apart{i}_{j}'


def meet_prefix(name, part, i, target, leaf):
    if i == 0:
        return leaf(0, target)
    return (f'B.Bits.apart_union({prefix(name, part + "0", i - 1)}, {part}{i}, {part}{target}, '
            f'{meet_prefix(name, part, i - 1, target, leaf)}, {leaf(i, target)})')


def mask_apart(i, j):
    return f'B.Bits.apart_mask(s{i}, s{j}, r{i}, r{j}, B.Bits.not_both_first(s{i}, s{j}, B.Bits.meet(r{i}, r{j}), apart{i}_{j}))'


def column_apart(i, j):
    return f'B.Bits.apart_single({bit(i, CENTER)}, {bit(j, CENTER)}, B.Bits.apart_at(r{i}, r{j}, {nat(CENTER)}, apart{i}_{j}))'


def chain_facts(name, part, count_of, equation):
    facts = []
    for i in range(1, ROWS):
        previous = total(name, count_of, i - 1)
        lhs = ('sum', previous, count_of(i))
        rhs = atom(f'B.Bits.count({name}{i})')
        pair = f'N.Natural.le_both_from_eq(B.Bits.count({name}{i}), R.Ring.eval(values, {expr(lhs)}), {equation(i)})'
        facts.append((lhs, rhs, f'Pair.snd(N.Natural.Le(B.Bits.count({name}{i}), R.Ring.eval(values, {expr(lhs)})), '
                                f'N.Natural.Le(R.Ring.eval(values, {expr(lhs)}), B.Bits.count({name}{i})), {pair})'))
    return facts


def count_equation(name, part, leaf):
    return lambda i: (f'B.Bits.count_union({prefix(name, part + "0", i - 1)}, {part}{i}, '
                      f'{meet_prefix(name, part, i - 1, i, leaf)})')


U_CHAIN = chain_facts('U', 'r', k, count_equation('U', 'r', lambda i, j: apart_rows(i, j)))
S_CHAIN = chain_facts('S', 'm', lambda i: atom(f'B.Bits.count(m{i})'), count_equation('S', 'm', mask_apart))
C_CHAIN = chain_facts('C', 'c', lambda i: plus(atom(f'B.Bits.n({bit(i, CENTER)})'), const(0)), count_equation('C', 'c', column_apart))
LOWER = [(const(2), plus(k(i), n(i)), f'Incidence.lower_count({bits_of(i)}, noncenter{i})') for i in range(ROWS)]
U_BOUND = (atom('B.Bits.count(U5)'), const(9), 'B.Bits.count_at_most_length(U5)')
MASK_COUNTS = [(n(i), atom(f'B.Bits.count(m{i})'),
                f'Pair.fst(N.Natural.Le(B.Bits.n(s{i}), B.Bits.count(m{i})), N.Natural.Le(B.Bits.count(m{i}), B.Bits.n(s{i})), '
                f'N.Natural.le_both_from_eq(B.Bits.n(s{i}), B.Bits.count(m{i}), Equal.sym(Nat, B.Bits.count(m{i}), B.Bits.n(s{i}), '
                f'Equal.trans(Nat, B.Bits.count(m{i}), B.Bits.select(s{i}, B.Bits.count(r{i})), B.Bits.n(s{i}), '
                f'B.Bits.count_mask(s{i}, r{i}), B.Bits.select_single(B.Bits.count(r{i}))))))') for i in range(ROWS)]


def unset_center(i):
    if i == 0:
        return f'B.Bits.unset_mask(s0, r0, {nat(CENTER)}, Incidence.single_not_center({bits_of(0)}, noncenter0))'
    return (f'B.Bits.unset_union({prefix("S", "m0", i - 1)}, m{i}, {nat(CENTER)}, {unset_center(i - 1)}, '
            f'B.Bits.unset_mask(s{i}, r{i}, {nat(CENTER)}, Incidence.single_not_center({bits_of(i)}, noncenter{i})))')


def lonely_of(i, j):
    return f'lonely{i}_{j}' if i != j else f'Incidence.single_alone({bits_of(i)})'


def untouched_right(i, e):
    leaf = lambda j: f'B.Bits.untouched_mask(Incidence.adjacent(), s{i}, s{j}, r{i}, r{j}, {lonely_of(i, j)})'
    if e == 0:
        return leaf(0)
    return (f'B.Bits.untouched_union_right(Incidence.adjacent(), m{i}, {prefix("S", "m0", e - 1)}, m{e}, '
            f'{untouched_right(i, e - 1)}, {leaf(e)})')


def untouched_left(e):
    if e == 0:
        return untouched_right(0, ROWS - 1)
    return (f'B.Bits.untouched_union_left(Incidence.adjacent(), {prefix("S", "m0", e - 1)}, m{e}, S5, '
            f'{untouched_left(e - 1)}, {untouched_right(e, ROWS - 1)})')


INDEPENDENT = (f'B.Bits.both(Bool.not({get("S5", CENTER)}), Bool.not(B.Bits.touches(Incidence.adjacent(), S5, S5)), '
               f'{unset_center(ROWS - 1)}, {untouched_left(ROWS - 1)})')
S_BOUND = (atom('B.Bits.count(S5)'), const(4), f'Incidence.independent_at_most_four({gets("S5")}, {INDEPENDENT})')

MAIN = f'''def Incidence.by_count({PARAMS}, choice: Or({{{SN_NAT} == 3n : Nat}}, {{{SN_NAT} == 4n : Nat}})) -> Empty:
  match choice:
    case Inl{{three}}:
      Incidence.case_three({ARGS}, three)
    case Inr{{four}}:
      Incidence.case_four({ARGS}, four)

def Incidence.impossible({PARAMS}) -> Empty:
{LETS}  +low: N.Natural.Le(3n, R.Ring.eval(values, {expr(SN)})) = {cancel(LOWER + U_CHAIN + [U_BOUND], const(3), SN)}
  +high: N.Natural.Le(R.Ring.eval(values, {expr(SN)}), 4n) = {cancel(MASK_COUNTS + S_CHAIN + [S_BOUND], SN, const(4))}
  Incidence.by_count({ARGS}, Incidence.three_or_four(R.Ring.eval(values, {expr(SN)}), low, high))
'''


def eq_le(equation, first):
    pair = f'N.Natural.le_both_from_eq(R.Ring.eval(values, {expr(SN)}), {first}n, {equation})'
    kinds = (f'N.Natural.Le(R.Ring.eval(values, {expr(SN)}), {first}n)', f'N.Natural.Le({first}n, R.Ring.eval(values, {expr(SN)}))')
    return pair, kinds


def finish(i):
    others = [LOWER[j] for j in range(ROWS) if j != i]
    reverse = [(rhs, lhs, proof.replace('Pair.snd(', 'Pair.fst(', 1)) for lhs, rhs, proof in U_CHAIN]
    reverse = []
    for lhs, rhs, proof in U_CHAIN:
        reverse.append((lhs, rhs, proof))
    bound = (SN, const(3), 'at_most')
    common_facts = U_CHAIN + [(atom('B.Bits.count(U5)'), const(9), 'B.Bits.count_at_most_length(U5)')] + others + [bound]
    return f'''def Incidence.finish{i}({PARAMS}, +at_most: N.Natural.Le({SN_NAT}, 3n), +center: B.Bits.Holds({bit(i, CENTER)})) -> Empty:
{LETS}  +small: N.Natural.Le(R.Ring.eval(values, {expr(plus(k(i), n(i)))}), 2n) = {cancel(common_facts, plus(k(i), n(i)), const(2))}
  B.Bits.never(Incidence.center_pair(r{i}), Incidence.center_pair_of({bits_of(i)}, noncenter{i}, pair_ok{i}, center, small), center{i})
'''


def find(e):
    lower = f'Incidence.finish{e - 1}({ARGS}, at_most, found)' if e == 1 else \
        f'Incidence.find{e - 1}({ARGS}, at_most, B.Bits.set_union({prefix("U", "r0", e - 2)}, r{e - 1}, {nat(CENTER)}, found))'
    return f'''def Incidence.find{e}({PARAMS}, +at_most: N.Natural.Le({SN_NAT}, 3n),
  choice: Or(B.Bits.Holds(B.Bits.get({'Incidence.row(' + ', '.join(f'b0_{q}' for q in range(POINTS)) + ')' if e == 1 else 'U_PREFIX'}, {nat(CENTER)})), B.Bits.Holds({bit(e, CENTER)}))) -> Empty:
  match choice:
    case Inl{{found}}:
{LETS.replace('  +', '      +')}      {lower}
    case Inr{{found}}:
      Incidence.finish{e}({ARGS}, at_most, found)
'''


def union_term(e):
    term = row_term(0)
    for i in range(1, e + 1):
        term = f'B.Bits.union({term}, {row_term(i)})'
    return term


def case_three():
    at_most_pair, kinds = eq_le('three', 3)
    nine = cancel(LOWER + [(SN, const(3), 'at_most')] + U_CHAIN, const(9), atom('B.Bits.count(U5)'))
    return f'''def Incidence.case_three({PARAMS}, +three: {{{SN_NAT} == 3n : Nat}}) -> Empty:
{LETS}  +at_most: {kinds[0]} = Pair.fst({kinds[0]}, {kinds[1]}, {at_most_pair})
  +nine: N.Natural.Le(9n, B.Bits.count(U5)) = {nine}
  Incidence.find5({ARGS}, at_most, B.Bits.set_union(U4, r5, {nat(CENTER)}, Incidence.full_has_center({gets("U5")}, nine)))
'''


def center_or_single(i):
    def leaf(j, target):
        inner = (f'B.Bits.not_both_first(s{j}, True{{}}, B.Bits.meet(r{j}, r{i}), apart{j}_{i})' if j != i else
                 f'B.Bits.not_and_first(s{i}, Bool.and(True{{}}, B.Bits.meet(r{i}, r{i})), alone)')
        return f'B.Bits.apart_mask(s{j}, True{{}}, r{j}, r{i}, {inner})'

    def meet_s(e):
        if e == 0:
            return leaf(0, i)
        return f'B.Bits.apart_union({prefix("S", "m0", e - 1)}, m{e}, r{i}, {meet_s(e - 1)}, {leaf(e, i)})'
    points = ', '.join(f'B.Bits.apart_at(S5, r{i}, {nat(p)}, apart)' for p in range(POINTS))
    return f'''def Incidence.center_or_single{i}({PARAMS}, +covered: B.Bits.Holds(Incidence.covered(S_TERM)),
  choice: Or(B.Bits.Holds(Incidence.single({row_term(i)})), B.Bits.Holds(Bool.not(Incidence.single({row_term(i)}))))) ->
  B.Bits.Holds(Bool.or(Incidence.single({row_term(i)}), {bit(i, CENTER)})):
  match choice:
    case Inl{{lonely}}:
      B.Bits.first(Incidence.single({row_term(i)}), {bit(i, CENTER)}, lonely)
    case Inr{{alone}}:
{LETS.replace('  +', '      +')}      +apart: B.Bits.Holds(Bool.not(B.Bits.meet(S5, r{i}))) = {meet_s(ROWS - 1)}
      Incidence.center_or_single({bits_of(i)}, noncenter{i}, pair_ok{i},
        Incidence.avoid_cycle({gets("S5")}, {bits_of(i)}, covered, {points}))
'''


def s_term():
    term = f'B.Bits.mask(Incidence.single({row_term(0)}), {row_term(0)})'
    for i in range(1, ROWS):
        term = f'B.Bits.union({term}, B.Bits.mask(Incidence.single({row_term(i)}), {row_term(i)}))'
    return term


def case_four():
    pair, kinds = eq_le('four', 4)
    at_least_s = cancel([(const(4), SN, 'at_least')] + MASK_COUNTS + S_CHAIN, const(4), atom('B.Bits.count(S5)'))
    rows = [f'+either{i}: B.Bits.Holds(Bool.or(s{i}, {bit(i, CENTER)})) = '
            f'Incidence.center_or_single{i}({ARGS}, covered, B.Bits.split(s{i}))' for i in range(ROWS)]
    facts = ([(const(1), atom(f'B.Bits.n(Bool.or(s{i}, {bit(i, CENTER)}))'), f'B.Bits.one_of(Bool.or(s{i}, {bit(i, CENTER)}), either{i})')
              for i in range(ROWS)]
             + [(atom(f'B.Bits.n(Bool.or(s{i}, {bit(i, CENTER)}))'), plus(n(i), atom(f'B.Bits.n({bit(i, CENTER)})')),
                 f'B.Bits.or_at_most(s{i}, {bit(i, CENTER)})') for i in range(ROWS)]
             + [(SN, const(4), 'at_most')] + C_CHAIN + [(atom('B.Bits.count(C5)'), const(1), 'B.Bits.count_at_most_length(C5)')])
    rows_text = ''.join(f'  {row}\n' for row in rows)
    return f'''def Incidence.case_four({PARAMS}, +four: {{{SN_NAT} == 4n : Nat}}) -> Empty:
{LETS}  +at_most: {kinds[0]} = Pair.fst({kinds[0]}, {kinds[1]}, {pair})
  +at_least: {kinds[1]} = Pair.snd({kinds[0]}, {kinds[1]}, {pair})
  +covered: B.Bits.Holds(Incidence.covered(S5)) = Incidence.independent_four_covers({gets("S5")}, {INDEPENDENT},
    {at_least_s})
{rows_text}  {refute(facts)}
'''


HEADER = '''import Base
import ./bend-math/Bits.bend as B
import ./bend-math/Natural.bend as N
import ./bend-math/Ring.bend as R

'''
finds = []
for e in range(1, ROWS):
    finds.append(find(e).replace('U_PREFIX', union_term(e - 1)))
parts = ([HEADER, DEFINITIONS] + ENUMERATIONS + [edge_free(), avoid_cycle(), three_or_four()]
         + [finish(i) for i in range(ROWS)] + finds + [case_three()]
         + [center_or_single(i).replace('S_TERM', s_term()) for i in range(ROWS)] + [case_four(), MAIN])
path = pathlib.Path(__file__).resolve().parent.parent / 'bend' / 'Incidence.bend'
path.write_text('\n'.join(parts))
