#!/usr/bin/env python3
"""Write bend/Unavoidable.bend: points that a square fitting the container [0, 3]^2 must contain.

Ports the single-square lemmas of Unavoidable.lean, Friedman.lean and
FriedmanStrip.lean that Stromquist's s(6) argument uses. Every lemma is stated
for a square whose frame has nonnegative cosine and sine, the first-quadrant
normal form; since such a lemma is about the square as a set, each orientation
of the container gets its own statement instead of a reflection.
"""
from types import SimpleNamespace

from bend_proof import ROOT, Refuter, SquareContext, T, containments, expand, num, one_of

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


def normal_lemma(name, params, spec, squares=(), splits=(), derive=True):
    """Emit a lemma for a normal square: hypotheses `a <= b` from spec(square, params) give one of its points."""
    signature_params = {p: T(p, p) for p in params}
    hyps, points = spec(SIGNATURE, signature_params)
    ctx = SquareContext()
    h = ctx.half()
    values = {p: ctx.var(p, p) for p in params}
    ctx.nonnegative(ctx.c, 'cosine_sign')
    ctx.nonnegative(ctx.s, 'sine_sign')
    ctx.corner_facts(h, num(3))
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
def Unavoidable.{name}(TPL, +square: P.Problem.Square<F, field>, +corners: M.Membership.Corners<F, field, square, {THREE}>,
  +cosine_sign: LE(ZERO, P.Problem.cosine(F, field, square)), +sine_sign: LE(ZERO, P.Problem.sine(F, field, square)){param_text}{hyp_text}) ->
  {containments('square', points)}:
  match square corners:
    case {ctx.square_pattern()} {ctx.corners_pattern()}:
{ctx.bindings(6)}      {proof}
'''


def corner(orientation):
    place, back = ORIENTATIONS[orientation]

    def spec(sq, v):
        cx, cy = back(sq.cx, sq.cy)
        tx, ty = back(v['tx'], v['ty'])
        return [(tx, num(1)), (ty, num(1)), (cx, tx), (cy, ty)], [(v['tx'], v['ty'])]
    return normal_lemma(f'{orientation}_corner', ['tx', 'ty'], spec, squares=[lambda q: q.c + q.s - 1])


def pair(orientation):
    place, back = ORIENTATIONS[orientation]

    def spec(sq, v):
        cx, cy = back(sq.cx, sq.cy)
        first = (v['left'], v['height'])
        second = (v['left'] + v['gap'], v['height'])
        image = [place(*first), place(*second)]
        return ([(v['height'], num(1)), (num(0), v['gap']), (v['gap'], num(1)),
                 (v['height'] + v['gap'] * (sq.c * sq.s), sq.c + sq.s),
                 (v['left'], cx), (cx, v['left'] + v['gap']), (cy, v['height'])], image)
    return normal_lemma(f'{orientation}_pair', ['left', 'height', 'gap'], spec,
                        squares=[lambda q: 1 - q.s, lambda q: 1 - q.c], splits=[(lambda q: q.c, lambda q: q.s)])


parts = [HEADER] + [corner(o) for o in ORIENTATIONS] + [pair(o) for o in ORIENTATIONS]
(ROOT / 'bend' / 'Unavoidable.bend').write_text(expand(''.join(parts)))
