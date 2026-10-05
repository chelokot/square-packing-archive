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
import time

import certificate

PREFIX = 'A.Algebra.'
CACHE_PATH = pathlib.Path(__file__).with_name('bend-certificates.json')
CACHE = json.loads(CACHE_PATH.read_text())


@atexit.register
def save_cache():
    CACHE_PATH.write_text(json.dumps(CACHE, indent=2, sort_keys=True) + '\n')


def search(*arguments):
    """certificate.search, remembered across runs because the generators ask the same questions again."""
    key = json.dumps(arguments)
    if key not in CACHE:
        started = time.time()
        if os.environ.get('BEND_PROOF_LOG'):
            pathlib.Path(os.environ['BEND_PROOF_LOG']).write_text(key)
            print(f'search goal {arguments[3][:150]} facts {len(arguments[1])} squares {len(arguments[4])} products {arguments[5]}', file=sys.stderr, flush=True)
        found = certificate.search(*arguments)
        CACHE[key] = None if found is None else certificate.render(*found)
        if len(CACHE) % 25 == 0:
            save_cache()
        if os.environ.get('BEND_PROOF_LOG') and time.time() - started > 1:
            print(f'{time.time() - started:.1f}s {found is not None} goal {arguments[3][:120]} facts {len(arguments[1])}', file=sys.stderr, flush=True)
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
    """Certificate for lower <= upper. With `tail`, the last facts and all values and equations are named lets,
    and `equation_texts` are the equations added after the freeze."""
    frozen = tail['facts'] if tail else []
    frozen_equations = tail['equation_texts'] if tail else []
    found = search(names, list(fact_texts) + frozen, list(equation_texts) + frozen_equations, f'({upper}) - ({lower})', list(squares), products)
    if found is None:
        if not required:
            return None
        raise SystemExit(f'no certificate for {lower} <= {upper} from {fact_texts} and {equation_texts}')
    denominator, terms = found
    if tail:
        fact_list = chain_with(lambda e, rest: f'C.MoreExprs{{{e}, {rest}}}', [term(t, names) for t in fact_texts], tail['name'])
        proof_list = chain_with(lambda p, rest: f'C.Both{{{p}, {rest}}}', list(fact_proofs), tail.get('proofs', tail['name'] + '_proofs'))
        equation_list = chain_with(lambda e, rest: f'C.MoreExprs{{{e}, {rest}}}', [term(t, names) for t in equation_texts], tail['equations'])
        equation_proof_list = chain_with(lambda p, rest: f'C.Both{{{p}, {rest}}}', list(equation_proofs), tail['equations'] + '_proofs')
        return (f'C.Certificate.le(TC, {tail["values"]}, {fact_list}, {proof_list}, {equation_list}, '
                f'{equation_proof_list}, {term(lower, names)}, {term(upper, names)}, {denominator}, {terms}, {{==}})')
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
        self.history = []

    def var(self, name, bend):
        self.names.append(name)
        self.terms.append(bend)
        return T(bend, name)

    def nonnegative(self, value, proof, name=None):
        self.facts.append((value.text, proof))
        self.history.append((value.text, proof, name or (proof if proof.isidentifier() else None)))

    def below(self, a, b, proof):
        fact = ((b - a).text, f'S.Scaling.fact(TC, {a.bend}, {b.bend}, {proof})')
        self.facts.append(fact)
        self.history.append(fact + (proof,))

    def equal(self, a, b, proof):
        self.equations.append(((a - b).text, f'S.Scaling.equation(TC, {a.bend}, {b.bend}, {proof})'))

    def raw_equation(self, text, proof):
        self.equations.append((text, proof))

    def le(self, a, b, squares=(), products=2, using=None, required=True, only=None):
        tail = self.tail
        if only is not None:
            chosen = [(text, proof) for text, proof, name in self.history if name in only]
            if tail is not None:
                tail = dict(tail, facts=[], name='C.NoExprs{}', proofs='Unit{}')
        else:
            chosen = self.facts if using is None else [self.facts[i] for i in using]
        return le(self.names, self.terms, [f for f, _ in chosen], [p for _, p in chosen],
                  [e for e, _ in self.equations], [p for _, p in self.equations], lift(a).text, lift(b).text,
                  [s.text if isinstance(s, T) else s for s in squares], products, required, tail)

    def freeze(self, name):
        """Bind the current facts (and, the first time, the values and equations) as lets named after `name`."""
        if self.tail is None:
            self.lets.append(f'+{name}_values: R.FieldRing.Values<F> = {values(*self.terms)}')
            self.lets.append(f'+{name}_equations: C.Certificate.Exprs = {exprs([e for e, _ in self.equations], self.names)}')
            self.lets.append(f'+{name}_equations_proofs: C.Certificate.Equations(TC, {name}_values, {name}_equations) = '
                             f'{facts(*[p for _, p in self.equations])}')
            base = {'values': f'{name}_values', 'equations': f'{name}_equations', 'facts': [], 'name': 'C.NoExprs{}',
                    'equation_texts': [e for e, _ in self.equations]}
            self.equations = []
            tail_proofs = 'Unit{}'
        else:
            base = dict(self.tail)
            tail_proofs = base['name'] + '_proofs'
        fact_list = chain_with(lambda e, rest: f'C.MoreExprs{{{e}, {rest}}}', [term(f, self.names) for f, _ in self.facts], base['name'])
        proof_list = chain_with(lambda p, rest: f'C.Both{{{p}, {rest}}}', [p for _, p in self.facts], tail_proofs)
        self.lets.append(f'+{name}: C.Certificate.Exprs = {fact_list}')
        self.lets.append(f'+{name}_proofs: C.Certificate.Facts(TC, {base["values"]}, {name}) = {proof_list}')
        self.tail = {'values': base['values'], 'equations': base['equations'], 'equation_texts': base['equation_texts'],
                     'facts': [f for f, _ in self.facts] + base['facts'], 'name': name}
        self.facts = []

    def copy(self):
        other = copy.copy(self)
        other.names = list(self.names)
        other.terms = list(self.terms)
        other.facts = list(self.facts)
        other.equations = list(self.equations)
        other.lets = list(self.lets)
        other.history = list(self.history)
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

    def __init__(self, squares=(), products=2, splits=(), only=None):
        self.squares = list(squares)
        self.products = products
        self.splits = list(splits)
        self.only = only
        self.fresh = 0

    def name(self, stem):
        self.fresh += 1
        return f'{stem}{self.fresh}'

    def refute(self, ctx, stricts, splits=None):
        splits = self.splits if splits is None else splits
        attempts = self.products if isinstance(self.products, tuple) else (self.products,)
        for products in attempts:
            for u, v, name in stricts:
                only = None if self.only is None else self.only + [n for _, _, n in stricts]
                cert = ctx.le(v, u, self.squares, products, required=False, only=only)
                if cert is not None:
                    return f'O.FieldOrder.lt_of(TC, {u.bend}, {v.bend}, {name})({cert})'
        for k, (a, b) in enumerate(splits):
            yes, no = self.name('below'), self.name('above')
            if self.only is not None:
                self.only = self.only + [yes, no]
            low = ctx.copy()
            low.below(a, b, yes)
            first = self.refute(low, stricts, splits[k + 1:])
            if first is None:
                continue
            high = ctx.copy()
            high.nonnegative(a - b, gap(b, a, no), no)
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
            branch.nonnegative(v - u, gap(u, v, name), name)
            branches.append(f'+{name} => {missing(i + 1, branch, found + [(u, v, name)])}')
        return f'M.Membership.outside(TC, {square}, {names[i]}, Empty, outside{i}, {", ".join(branches)})'

    return decide(0)


def containments(square, points, named=False):
    show = (lambda p: p) if named else point_bend
    out = f'P.Problem.Containment<F, field, {square}, {show(points[-1])}>'
    for point in reversed(points[:-1]):
        out = f'Or(P.Problem.Containment<F, field, {square}, {show(point)}>, {out})'
    return out


def build(ctx, steps, goal, refuter, finish, stricts=()):
    """Run proof steps in order, binding each derived fact, then call finish(ctx, stricts).

    Steps: ('le', name, a, b, squares) proves a <= b by a certificate; ('lt', name, a, b) proves a < b by
    refuting b <= a; ('cases', a, b, yes, no) splits on a <= b and runs the step lists `yes` and `no`.
    """
    stricts = list(stricts)
    if not steps:
        return finish(ctx, stricts)
    step, rest = steps[0], steps[1:]
    if step[0] == 'le':
        _, name, a, b, squares = step[:5]
        options = step[5] if len(step) > 5 else {}
        proof = ctx.le(a, b, squares, options.get('products', refuter.products), only=options.get('only'))
        after = ctx.copy()
        after.below(a, b, name)
        return f'M.Membership.bind(LE({lift(a).bend}, {lift(b).bend}), {goal}, {proof}, +{name} => {build(after, rest, goal, refuter, finish, stricts)})'
    if step[0] == 'lt':
        _, name, a, b = step[:4]
        options = step[4] if len(step) > 4 else {}
        a, b = lift(a), lift(b)
        bad = ctx.copy()
        bad.below(b, a, f'{name}_bad')
        if 'only' in options:
            refutation = None
            for u, v, strict in stricts:
                if strict in options['only'] and refutation is None:
                    cert = bad.le(v, u, options.get('squares', ()), options.get('products', 2),
                                  required=False, only=options['only'] + [f'{name}_bad'])
                    if cert is not None:
                        refutation = f'O.FieldOrder.lt_of(TC, {u.bend}, {v.bend}, {strict})({cert})'
        else:
            saved = refuter.products
            refuter.products = options.get('products', saved)
            refutation = refuter.refute(bad, stricts)
            refuter.products = saved
        if refutation is None:
            raise SystemExit(f'cannot prove {a.text} < {b.text}')
        proof = f'O.FieldOrder.strict_of(TC, {a.bend}, {b.bend}, +{name}_bad => {refutation})'
        after = ctx.copy()
        after.nonnegative(b - a, gap(a, b, name), name)
        return (f'M.Membership.bind(O.FieldOrder.Strict(TC, {a.bend}, {b.bend}), {goal}, {proof}, '
                f'+{name} => {build(after, rest, goal, refuter, finish, stricts + [(a, b, name)])})')
    if step[0] == 'equation':
        _, a, b, proof = step
        after = ctx.copy()
        after.equal(lift(a), lift(b), proof)
        return build(after, rest, goal, refuter, finish, stricts)
    if step[0] == 'given_lt':
        _, name, a, b, proof = step
        a, b = lift(a), lift(b)
        after = ctx.copy()
        after.nonnegative(b - a, gap(a, b, name), name)
        return (f'M.Membership.bind(O.FieldOrder.Strict(TC, {a.bend}, {b.bend}), {goal}, {proof}, '
                f'+{name} => {build(after, rest, goal, refuter, finish, stricts + [(a, b, name)])})')
    if step[0] == 'try':
        for option in step[1]:
            try:
                build(ctx, [option], goal, refuter, lambda current, found: 'probe', stricts)
            except SystemExit as failure:
                if os.environ.get('BEND_PROOF_TRY'):
                    print(f'try {option[1]} with {[n for _, _, n in stricts]}: {str(failure)[:150]}', file=sys.stderr, flush=True)
                continue
            return build(ctx, [option] + rest, goal, refuter, finish, stricts)
        return build(ctx, rest, goal, refuter, finish, stricts)
    if step[0] == 'le_refute':
        _, name, a, b = step[:4]
        a, b = lift(a), lift(b)
        bad = ctx.copy()
        bad.nonnegative(a - b, gap(b, a, f'{name}_bad'), f'{name}_bad')
        options = step[4] if len(step) > 4 else {}
        if 'only' in options:
            proof_le = bad.le(a, b, options.get('squares', ()), options.get('products', 2), only=options['only'] + [f'{name}_bad'])
            refutation = f'O.FieldOrder.lt_of(TC, {b.bend}, {a.bend}, {name}_bad)({proof_le})'
        elif 'splits' in options:
            refutation = Refuter(options.get('squares', ()), options.get('products', 2), options['splits']).refute(
                bad, stricts + [(b, a, f'{name}_bad')])
        else:
            saved = refuter.products
            refuter.products = options.get('products', saved)
            refutation = refuter.refute(bad, stricts + [(b, a, f'{name}_bad')])
            refuter.products = saved
        if refutation is None:
            raise SystemExit(f'cannot prove {a.text} <= {b.text} by contradiction')
        kind = f'LE({a.bend}, {b.bend})'
        proof = (f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {kind}, +{name}_ok => {name}_ok, '
                 f'+{name}_bad => Empty.absurd({kind}, {refutation}))')
        after = ctx.copy()
        after.below(a, b, name)
        return f'M.Membership.bind({kind}, {goal}, {proof}, +{name} => {build(after, rest, goal, refuter, finish, stricts)})'
    if step[0] == 'outside':
        _, square, point, outside = step
        lx, ly, name = ctx.locals_of[tuple(c.text for c in point)]
        h = ctx.var_term('h')
        branches = []
        for k, (u, v) in enumerate([(h, lx), (lx, -h), (h, ly), (ly, -h)]):
            label = f'{outside}_{k}'
            branch = ctx.copy()
            branch.nonnegative(v - u, gap(u, v, label), label)
            found = stricts + [(u, v, label)]
            early = refuter.refute(branch, found, splits=[])
            inner = f'Empty.absurd({goal}, {early})' if early is not None else build(branch, rest, goal, refuter, finish, found)
            branches.append(f'+{label} => {inner}')
        return f'M.Membership.outside(TC, {square}, {name}, {goal}, {outside}, {", ".join(branches)})'
    if step[0] == 'cases':
        _, name, a, b, yes, no = step
        a, b = lift(a), lift(b)
        low = ctx.copy()
        low.below(a, b, name)
        high = ctx.copy()
        high.nonnegative(a - b, gap(b, a, name), name)
        return (f'M.Membership.by_cases(TC, {a.bend}, {b.bend}, {goal}, +{name} => {build(low, yes + rest, goal, refuter, finish, stricts)}, '
                f'+{name} => {build(high, no + rest, goal, refuter, finish, stricts + [(b, a, name)])})')
    raise ValueError(step[0])


def rendered_le(names, values_text, fact_texts, fact_proofs_text, equation_texts, equation_proofs_text, lower, upper,
                squares=(), products=2):
    """Certificate for lower <= upper with the values and proofs already written as Bend."""
    found = search(names, list(fact_texts), list(equation_texts), f'({upper}) - ({lower})', list(squares), products)
    if found is None:
        raise SystemExit(f'no certificate for {lower} <= {upper}')
    denominator, terms = found
    return (f'C.Certificate.le(TC, {values_text}, {exprs(fact_texts, names)}, {fact_proofs_text}, {exprs(equation_texts, names)}, '
            f'{equation_proofs_text}, {term(lower, names)}, {term(upper, names)}, {denominator}, {terms}, {{==}})')


def rendered_same(names, values_text, equation_texts, equation_proofs_text, left, right):
    """Certificate for left = right with the values and proofs already written as Bend."""
    forward = search(names, [], list(equation_texts), f'({right}) - ({left})', [], 0)
    backward = search(names, [], list(equation_texts), f'({left}) - ({right})', [], 0)
    if forward is None or backward is None or forward[0] != '0n' or backward[0] != '0n':
        raise SystemExit(f'no certificate for {left} = {right}')
    return (f'C.Certificate.same(TC, {values_text}, {exprs(equation_texts, names)}, {equation_proofs_text}, '
            f'{term(left, names)}, {term(right, names)}, {forward[1]}, {backward[1]}, {{==}}, {{==}})')
