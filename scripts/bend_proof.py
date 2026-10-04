"""Shared helpers for the scripts that write proofs in bend/.

Sources use short macros for the ordered-field interface (TPL, TC, ZERO, ONE,
HALF, ADD, NEG, MUL, INV, LE, SAME, AL., AX.) which `expand` turns into Bend.
`le` and `same` search exact certificates with bend-math/tools/certificate.py.
"""
import copy
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'bend' / 'bend-math' / 'tools'))

import atexit
import json
import os

import certificate

PREFIX = 'A.Algebra.'
CACHE_PATH = pathlib.Path(os.environ.get('BEND_PROOF_CACHE', pathlib.Path.home() / '.cache' / 'bend-proof-certificates.json'))
CACHE = json.loads(CACHE_PATH.read_text()) if CACHE_PATH.exists() else {}


@atexit.register
def save_cache():
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(CACHE))


def search(*arguments):
    """certificate.search, remembered across runs because the generators ask the same questions again."""
    key = json.dumps(arguments)
    if key not in CACHE:
        found = certificate.search(*arguments)
        CACHE[key] = None if found is None else certificate.render(*found)
    return CACHE[key]


def expand(src):
    for short, full in [('TPL', '~F: Kind(&2), ~field: K.Field<F>'), ('TC', '~F, ~field'),
                        ('ZERO', PREFIX + 'zero(~F, ~field)'), ('ONE', PREFIX + 'one(~F, ~field)'),
                        ('HALF', PREFIX + 'half(~F, ~field)')]:
        src = re.sub(r'\b%s\b' % short, full, src)
    src = re.sub(r'\bAL\.', PREFIX, src)
    for short, name in [('ADD', 'add'), ('NEG', 'neg'), ('MUL', 'mul'), ('INV', 'inverse'), ('LE', 'le'), ('SAME', 'Same')]:
        src = re.sub(r'\b%s\(' % short, PREFIX + '%s(~F, ~field, ' % name, src)
    return re.sub(r'\bAX\.([a-z_]+)\(', lambda m: 'K.Field.%s(F, field)(' % m.group(1), src)


def values(*terms):
    out = 'R.NoValues{}'
    for term in reversed(terms):
        out = f'R.Value{{{term}, {out}}}'
    return out


def facts(*proofs):
    out = 'Unit{}'
    for proof in reversed(proofs):
        out = f'C.Both{{{proof}, {out}}}'
    return out


def exprs(texts, names):
    out = 'C.NoExprs{}'
    for text in reversed(texts):
        out = f'C.MoreExprs{{{certificate.bend(certificate.parse(text, names))}, {out}}}'
    return out


def term(text, names):
    return certificate.bend(certificate.parse(text, names))


def le(names, value_terms, fact_texts, fact_proofs, equation_texts, equation_proofs, lower, upper, squares=(), products=2,
       required=True, tail=None):
    """Certificate for lower <= upper. With `tail`, the last facts and all values and equations are named lets."""
    frozen = tail['facts'] if tail else []
    found = search(names, list(fact_texts) + frozen, list(equation_texts), f'({upper}) - ({lower})', list(squares), products)
    if found is None:
        if not required:
            return None
        raise SystemExit(f'no certificate for {lower} <= {upper} from {fact_texts} and {equation_texts}')
    denominator, terms = found
    if tail:
        fact_list = chain_with(lambda e, rest: f'C.MoreExprs{{{e}, {rest}}}', [term(t, names) for t in fact_texts], tail['name'])
        proof_list = chain_with(lambda p, rest: f'C.Both{{{p}, {rest}}}', list(fact_proofs), tail['name'] + '_proofs')
        return (f'C.Certificate.le(TC, {tail["values"]}, {fact_list}, {proof_list}, {tail["equations"]}, '
                f'{tail["equations"]}_proofs, {term(lower, names)}, {term(upper, names)}, {denominator}, {terms}, {{==}})')
    return (f'C.Certificate.le(TC, {values(*value_terms)}, {exprs(fact_texts, names)}, {facts(*fact_proofs)}, '
            f'{exprs(equation_texts, names)}, {facts(*equation_proofs)}, {term(lower, names)}, {term(upper, names)}, '
            f'{denominator}, {terms}, {{==}})')


def chain_with(constructor, items, end):
    out = end
    for item in reversed(items):
        out = constructor(item, out)
    return out


def same(names, value_terms, equation_texts, equation_proofs, left, right):
    forward = search(names, [], list(equation_texts), f'({right}) - ({left})', [], 0)
    backward = search(names, [], list(equation_texts), f'({left}) - ({right})', [], 0)
    if forward is None or backward is None or forward[0] != '0n' or backward[0] != '0n':
        raise SystemExit(f'no certificate for {left} = {right}')
    return (f'C.Certificate.same(TC, {values(*value_terms)}, {exprs(equation_texts, names)}, {facts(*equation_proofs)}, '
            f'{term(left, names)}, {term(right, names)}, {forward[1]}, {backward[1]}, {{==}}, {{==}})')


class T:
    """A field term written both as Bend source and as certificate text, with the same tree."""

    def __init__(self, bend, text):
        self.bend = bend
        self.text = text

    def __add__(self, other):
        other = lift(other)
        return T(f'ADD({self.bend}, {other.bend})', f'({self.text} + {other.text})')

    def __radd__(self, other):
        return lift(other) + self

    def __neg__(self):
        return T(f'NEG({self.bend})', f'(-({self.text}))')

    def __sub__(self, other):
        return self + (-lift(other))

    def __rsub__(self, other):
        return lift(other) - self

    def __mul__(self, other):
        other = lift(other)
        return T(f'MUL({self.bend}, {other.bend})', f'({self.text}*{other.text})')

    def __rmul__(self, other):
        return lift(other) * self


def num(n):
    return T(f'R.FieldRing.of_nat(TC, {n}n)', str(n))


def lift(value):
    return value if isinstance(value, T) else num(value)


ZERO_T = T('ZERO', '0')


class Context:
    """Named field values, facts `0 <= term` and equations `term = 0` for certificate searches."""

    def __init__(self):
        self.names = []
        self.terms = []
        self.facts = []
        self.equations = []
        self.lets = []
        self.tail = None
        self.locals_of = {}

    def var(self, name, bend):
        self.names.append(name)
        self.terms.append(bend)
        return T(bend, name)

    def nonnegative(self, value, proof):
        self.facts.append((value.text, proof))

    def below(self, a, b, proof):
        self.facts.append(((b - a).text, f'S.Scaling.fact(TC, {a.bend}, {b.bend}, {proof})'))

    def equal(self, a, b, proof):
        self.equations.append(((a - b).text, f'S.Scaling.equation(TC, {a.bend}, {b.bend}, {proof})'))

    def raw_equation(self, text, proof):
        self.equations.append((text, proof))

    def le(self, a, b, squares=(), products=2, using=None, required=True):
        chosen = self.facts if using is None else [self.facts[i] for i in using]
        return le(self.names, self.terms, [f for f, _ in chosen], [p for _, p in chosen],
                  [e for e, _ in self.equations], [p for _, p in self.equations], lift(a).text, lift(b).text,
                  [s.text if isinstance(s, T) else s for s in squares], products, required, self.tail)

    def freeze(self, name):
        """Bind the current facts (and, the first time, the values and equations) as lets named after `name`."""
        if self.tail is None:
            self.lets.append(f'+{name}_values: R.FieldRing.Values<F> = {values(*self.terms)}')
            self.lets.append(f'+{name}_equations: C.Certificate.Exprs = {exprs([e for e, _ in self.equations], self.names)}')
            self.lets.append(f'+{name}_equations_proofs: C.Certificate.Equations(TC, {name}_values, {name}_equations) = '
                             f'{facts(*[p for _, p in self.equations])}')
            base = {'values': f'{name}_values', 'equations': f'{name}_equations', 'facts': [], 'name': 'C.NoExprs{}'}
            tail_proofs = 'Unit{}'
        else:
            base = dict(self.tail)
            tail_proofs = base['name'] + '_proofs'
        fact_list = chain_with(lambda e, rest: f'C.MoreExprs{{{e}, {rest}}}', [term(f, self.names) for f, _ in self.facts], base['name'])
        proof_list = chain_with(lambda p, rest: f'C.Both{{{p}, {rest}}}', [p for _, p in self.facts], tail_proofs)
        self.lets.append(f'+{name}: C.Certificate.Exprs = {fact_list}')
        self.lets.append(f'+{name}_proofs: C.Certificate.Facts(TC, {base["values"]}, {name}) = {proof_list}')
        self.tail = {'values': base['values'], 'equations': base['equations'],
                     'facts': [f for f, _ in self.facts] + base['facts'], 'name': name}
        self.facts = []

    def copy(self):
        other = copy.copy(self)
        other.names = list(self.names)
        other.terms = list(self.terms)
        other.facts = list(self.facts)
        other.equations = list(self.equations)
        other.lets = list(self.lets)
        return other

    def derive(self, name, a, b, squares=(), products=2):
        """Prove a <= b, bind it as `name` and keep it as a fact."""
        proof = self.le(a, b, squares, products)
        self.lets.append(f'+{name}: LE({lift(a).bend}, {lift(b).bend}) = {proof}')
        self.below(a, b, name)
        return name

    def bindings(self, indent):
        return ''.join(f'{" " * indent}{line}\n' for line in self.lets)

    def var_term(self, name):
        return T(self.terms[self.names.index(name)], name)

    def same(self, a, b):
        return same(self.names, self.terms, [e for e, _ in self.equations], [p for _, p in self.equations],
                    lift(a).text, lift(b).text)


CORNER_NAMES = ('low_low', 'low_high', 'high_low', 'high_high')


class SquareContext(Context):
    """A context for one square matched into center, frame and the corners that fit a container."""

    def __init__(self, prefix=''):
        super().__init__()
        self.prefix = prefix
        p = prefix
        self.cx, self.cy, self.c, self.s = (self.var(p + n, p + n) for n in ('cx', 'cy', 'c', 's'))
        self.raw_equation(((self.c * self.c + self.s * self.s) - 1).text, f'G.Geometry.unit(TC, {p}c, {p}s, {p}ub, {p}ua)')

    def half(self):
        h = self.var('h', 'HALF')
        self.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
        return h

    def square_pattern(self):
        p = self.prefix
        return f'P.Square{{P.Point{{+{p}cx, +{p}cy}}, P.Frame{{+{p}c, +{p}s, +{p}ub, +{p}ua}}}}'

    def square(self):
        p = self.prefix
        return f'P.Square{{P.Point{{{p}cx, {p}cy}}, P.Frame{{{p}c, {p}s, {p}ub, {p}ua}}}}'

    def bind_square(self):
        """Name the matched square `q` (with the prefix) for the rest of the body."""
        name = self.prefix + 'q'
        self.lets.append(f'+{name}: P.Problem.Square<F, field> = {self.square()}')
        return name

    def corners_pattern(self):
        p = self.prefix
        return 'M.Corners{' + ', '.join(f'P.InContainer{{+{p}{n}_left, +{p}{n}_right, +{p}{n}_bottom, +{p}{n}_top}}'
                                      for n in CORNER_NAMES) + '}'

    def corner_facts(self, h, side, which=CORNER_NAMES):
        p = self.prefix
        signs = {'low_low': (-1, -1), 'low_high': (-1, 1), 'high_low': (1, -1), 'high_high': (1, 1)}
        for name in which:
            a, b = signs[name]
            lx = h if a > 0 else -h
            ly = h if b > 0 else -h
            x = self.cx + (lx * self.c - ly * self.s)
            y = self.cy + (lx * self.s + ly * self.c)
            self.nonnegative(x, f'{p}{name}_left')
            self.below(x, side, f'{p}{name}_right')
            self.nonnegative(y, f'{p}{name}_bottom')
            self.below(y, side, f'{p}{name}_top')

    def local(self, point):
        x, y = point
        return ((x - self.cx) * self.c + (y - self.cy) * self.s, (-(x - self.cx)) * self.s + (y - self.cy) * self.c)

    def local_vars(self, point, tag, square):
        """Name a point `p<tag>` and its local coordinates in `square`, as variables defined by equations."""
        x, y = self.local(point)
        self.lets.append(f'+p{tag}: P.Problem.Point<F> = {point_bend(point)}')
        self.lets.append(f'+lx{tag}: F = G.Geometry.local_x(TC, {square}, p{tag})')
        self.lets.append(f'+ly{tag}: F = G.Geometry.local_y(TC, {square}, p{tag})')
        lx = self.var(f'lx{tag}', f'lx{tag}')
        ly = self.var(f'ly{tag}', f'ly{tag}')
        self.equal(lx, x, f'S.Scaling.pair(TC, lx{tag}, {x.bend}, AX.le_reflexive(lx{tag}), AX.le_reflexive(lx{tag}))')
        self.equal(ly, y, f'S.Scaling.pair(TC, ly{tag}, {y.bend}, AX.le_reflexive(ly{tag}), AX.le_reflexive(ly{tag}))')
        self.locals_of[tuple(c.text for c in point)] = (lx, ly, f'p{tag}')
        return lx, ly


def point_bend(point):
    return f'P.Point{{{point[0].bend}, {point[1].bend}}}'


def gap(u, v, name):
    return f'M.Membership.gap(TC, {u.bend}, {v.bend}, {name})'


class Refuter:
    """Refute a case from strict facts `u < v`: prove `v <= u` for one of them, splitting on comparisons if needed."""

    def __init__(self, squares=(), products=2, splits=()):
        self.squares = list(squares)
        self.products = products
        self.splits = list(splits)
        self.fresh = 0

    def name(self, stem):
        self.fresh += 1
        return f'{stem}{self.fresh}'

    def refute(self, ctx, stricts, splits=None):
        splits = self.splits if splits is None else splits
        for u, v, name in stricts:
            cert = ctx.le(v, u, self.squares, self.products, required=False)
            if cert is not None:
                return f'O.FieldOrder.lt_of(TC, {u.bend}, {v.bend}, {name})({cert})'
        for k, (a, b) in enumerate(splits):
            yes, no = self.name('below'), self.name('above')
            low = ctx.copy()
            low.below(a, b, yes)
            first = self.refute(low, stricts, splits[k + 1:])
            if first is None:
                continue
            high = ctx.copy()
            high.nonnegative(a - b, gap(b, a, no))
            second = self.refute(high, stricts + [(b, a, no)], splits[k + 1:])
            if second is None:
                continue
            return f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, Empty, +{yes} => {first}, +{no} => {second})'
        return None


def one_of(ctx, square, points, refuter, stricts=()):
    """A term of type Or(Containment(square, p0), Or(...)); the points must have local variables in ctx."""
    names = [ctx.locals_of[tuple(c.text for c in point)][2] for point in points]
    goal = containments(square, names, named=True)

    def inject(i, proof):
        out = proof if i == len(points) - 1 else f'Inl{{{proof}}}'
        for _ in range(i):
            out = f'Inr{{{out}}}'
        return out

    def decide(i):
        if i == len(points):
            return f'Empty.absurd({goal}, {missing(0, ctx, list(stricts))})'
        p = names[i]
        return (f'M.Membership.when(TC, {square}, {p}, {goal}, +inside{i} => {inject(i, f"inside{i}")}, '
                f'+outside{i} => {decide(i + 1)})')

    def missing(i, current, found):
        if i == len(points):
            proof = refuter.refute(current, found)
            if proof is None:
                raise SystemExit(f'no refutation with {[(u.text, v.text) for u, v, _ in found]}')
            return proof
        if found:
            early = refuter.refute(current, found, splits=[])
            if early is not None:
                return early
        lx, ly, _ = current.locals_of[tuple(c.text for c in points[i])]
        h = current.var_term('h')
        cases = [(h, lx), (lx, -h), (h, ly), (ly, -h)]
        branches = []
        for k, (u, v) in enumerate(cases):
            name = f'miss{i}_{k}'
            branch = current.copy()
            branch.nonnegative(v - u, gap(u, v, name))
            branches.append(f'+{name} => {missing(i + 1, branch, found + [(u, v, name)])}')
        return f'M.Membership.outside(TC, {square}, {names[i]}, Empty, outside{i}, {", ".join(branches)})'

    return decide(0)


def containments(square, points, named=False):
    show = (lambda p: p) if named else point_bend
    out = f'P.Problem.Containment<F, field, {square}, {show(points[-1])}>'
    for point in reversed(points[:-1]):
        out = f'Or(P.Problem.Containment<F, field, {square}, {show(point)}>, {out})'
    return out
