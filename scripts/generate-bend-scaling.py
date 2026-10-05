#!/usr/bin/env python3
"""Write bend/Scaling.bend: a packing scaled about the square centres becomes a closed-disjoint family.

Ports Packing.exists_closed_disjoint_family_in_larger_container from
PackingPointCapacity.lean: a packing of side `side` is a family of squares that
fit any container of side `target > side` and do not share even boundary points.
"""
from bend_proof import ROOT, exprs, expand, rendered_le as le, rendered_same as same, term as bend

PARTS = []

def values(*names):
    out = 'R.NoValues{}'
    for n in reversed(names):
        out = f'R.Value{{{n}, {out}}}'
    return out

def facts(*proofs):
    out = 'Unit{}'
    for p in reversed(proofs):
        out = f'C.Both{{{p}, {out}}}'
    return out

src = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Certificate.bend as C
import ./Problem.bend as P
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Packings.bend as S
import ./bend-math/Natural.bend as N

def Scaling.number(TPL, +n: Nat) -> F:
  R.FieldRing.of_nat(TC, n)

def Scaling.one_is_number(TPL) -> SAME(ONE, Scaling.number(TC, 1n)):
  AL.same_symmetric(TC, Scaling.number(TC, 1n), ONE, R.FieldRing.of_nat_one(TC))

def Scaling.fact(TPL, +a: F, +b: F, below: LE(a, b)) -> LE(ZERO, ADD(b, NEG(a))):
  AL.le_respects(TC, ADD(a, NEG(a)), ADD(b, NEG(a)), ZERO, ADD(b, NEG(a)), AX.le_add(a, b, NEG(a), below),
    AL.add_neg(TC, a), AL.same_reflexive(TC, ADD(b, NEG(a))))

def Scaling.equation(TPL, +a: F, +b: F, same: SAME(a, b)) -> C.Certificate.Both<LE(ADD(a, NEG(b)), ZERO), LE(ZERO, ADD(a, NEG(b)))>:
  (below, above) = same
  G.Geometry.zero_difference(TC, a, b, below, above)

def Scaling.number_bound(TPL, +a: F, below: LE(ONE, a)) -> LE(Scaling.number(TC, 1n), a):
  AL.le_respects(TC, ONE, a, Scaling.number(TC, 1n), a, below, Scaling.one_is_number(TC), AL.same_reflexive(TC, a))

def Scaling.number_bound_above(TPL, +a: F, below: LE(a, Scaling.number(TC, 1n))) -> LE(a, ONE):
  AL.le_respects(TC, a, Scaling.number(TC, 1n), a, ONE, below, AL.same_reflexive(TC, a),
    AL.same_symmetric(TC, ONE, Scaling.number(TC, 1n), Scaling.one_is_number(TC)))

def Scaling.half_equation(TPL) -> C.Certificate.Both<LE(ADD(ADD(HALF, HALF), NEG(Scaling.number(TC, 1n))), ZERO),
  LE(ZERO, ADD(ADD(HALF, HALF), NEG(Scaling.number(TC, 1n))))>:
  Scaling.equation(TC, ADD(HALF, HALF), Scaling.number(TC, 1n),
    AL.same_transitive(TC, ADD(HALF, HALF), ONE, Scaling.number(TC, 1n), K.Field.half_double(F, field), Scaling.one_is_number(TC)))

def Scaling.half_nonnegative(TPL) -> LE(ZERO, HALF):
  +h: F = HALF
  ''' + le(['h'], values('h'), [], 'Unit{}', ['h + h - 1'], facts('Scaling.half_equation(TC)'), '0', 'h') + '''

def Scaling.inverse_equation(TPL, +factor: F, +inverse: F, cancel: SAME(MUL(factor, inverse), ONE)) ->
  C.Certificate.Both<LE(ADD(MUL(factor, inverse), NEG(Scaling.number(TC, 1n))), ZERO), LE(ZERO, ADD(MUL(factor, inverse), NEG(Scaling.number(TC, 1n))))>:
  Scaling.equation(TC, MUL(factor, inverse), Scaling.number(TC, 1n),
    AL.same_transitive(TC, MUL(factor, inverse), ONE, Scaling.number(TC, 1n), cancel, Scaling.one_is_number(TC)))

def Scaling.inverse_nonnegative(TPL, +f: F, +i: F, at_least: LE(ONE, f), cancel: SAME(MUL(f, i), ONE)) -> LE(ZERO, i):
  ''' + le(['f', 'i'], values('f', 'i'), ['f - 1'],
          facts('Scaling.fact(TC, Scaling.number(TC, 1n), f, Scaling.number_bound(TC, f, at_least))'),
          ['f*i - 1'], facts('Scaling.inverse_equation(TC, f, i, cancel)'), '0', 'i', squares=['i']) + '''

def Scaling.inverse_at_most_one(TPL, +f: F, +i: F, at_least: LE(ONE, f), +nonnegative: LE(ZERO, i), cancel: SAME(MUL(f, i), ONE)) -> LE(i, ONE):
  Scaling.number_bound_above(TC, i,
    ''' + le(['f', 'i'], values('f', 'i'), ['f - 1', 'i'],
            facts('Scaling.fact(TC, Scaling.number(TC, 1n), f, Scaling.number_bound(TC, f, at_least))', 'nonnegative'),
            ['f*i - 1'], facts('Scaling.inverse_equation(TC, f, i, cancel)'), 'i', '1') + ''')

def Scaling.scaled_at_most(TPL, +h: F, +l: F, +i: F, at_most: LE(l, h), +i_nonnegative: LE(ZERO, i), i_at_most: LE(i, ONE),
  +h_nonnegative: LE(ZERO, h)) -> LE(MUL(l, i), h):
  ''' + le(['h', 'l', 'i'], values('h', 'l', 'i'), ['h - l', 'i', 'h', '1 - i'],
          facts('Scaling.fact(TC, l, h, at_most)', 'i_nonnegative', 'h_nonnegative',
                'Scaling.fact(TC, i, Scaling.number(TC, 1n), AL.le_respects(TC, i, ONE, i, Scaling.number(TC, 1n), i_at_most, AL.same_reflexive(TC, i), Scaling.one_is_number(TC)))'),
          [], 'Unit{}', 'l*i', 'h') + '''

def Scaling.scaled_at_least(TPL, +h: F, +l: F, +i: F, at_least: LE(NEG(h), l), +i_nonnegative: LE(ZERO, i), i_at_most: LE(i, ONE),
  +h_nonnegative: LE(ZERO, h)) -> LE(NEG(h), MUL(l, i)):
  ''' + le(['h', 'l', 'i'], values('h', 'l', 'i'), ['l - (-h)', 'i', 'h', '1 - i'],
          facts('Scaling.fact(TC, NEG(h), l, at_least)', 'i_nonnegative', 'h_nonnegative',
                'Scaling.fact(TC, i, Scaling.number(TC, 1n), AL.le_respects(TC, i, ONE, i, Scaling.number(TC, 1n), i_at_most, AL.same_reflexive(TC, i), Scaling.one_is_number(TC)))'),
          [], 'Unit{}', '-h', 'l*i') + '''
'''
PARTS.append(src)

N = ['cx', 'cy', 'c', 's', 'lx', 'ly', 'x', 'y', 'f', 'i']
V = values(*N)
src2 = '''
def Scaling.pair(TPL, +a: F, +b: F, +below: LE(a, b), +above: LE(b, a)) -> SAME(a, b):
  (below, above)

def Scaling.scale_center(TPL, +factor: F, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, frame}:
      P.Square{P.Point{MUL(factor, center_x), MUL(factor, center_y)}, frame}

def Scaling.scale_point(TPL, +factor: F, point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{MUL(factor, x), MUL(factor, y)}

def Scaling.coordinate(TPL, +value: F, +scaled: F, +bound: F, same: SAME(value, scaled), +low: LE(ZERO, scaled), +high: LE(scaled, bound)) ->
  C.Certificate.Both<LE(ZERO, value), LE(value, bound)>:
  (below, above) = same
  C.Both{AX.le_transitive(ZERO, scaled, value, low, above), AX.le_transitive(value, scaled, bound, below, high)}

def Scaling.in_container(TPL, +side: F, +x: F, +y: F,
  x_bounds: C.Certificate.Both<LE(ZERO, x), LE(x, side)>, y_bounds: C.Certificate.Both<LE(ZERO, y), LE(y, side)>) ->
  P.Problem.InContainer<F, field, side, P.Point{x, y}>:
  match x_bounds y_bounds:
    case C.Both{left, right} C.Both{bottom, top}:
      P.InContainer{left, right, bottom, top}

def Scaling.scale_finish(TPL, +cx: F, +cy: F, +c: F, +s: F, +lx: F, +ly: F, +x: F, +y: F, +f: F, +i: F, +side: F,
  +x_is_below: LE(x, ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s))))),
  +x_is_above: LE(ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s)))), x),
  +y_is_below: LE(y, ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c)))),
  +y_is_above: LE(ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c))), y),
  +cancel_below: LE(MUL(f, i), ONE), +cancel_above: LE(ONE, MUL(f, i)), +f_nonnegative: LE(ZERO, f),
  inner: P.Problem.InContainer<F, field, side, P.Point{
    ADD(cx, ADD(MUL(MUL(lx, i), c), NEG(MUL(MUL(ly, i), s)))), ADD(cy, ADD(MUL(MUL(lx, i), s), MUL(MUL(ly, i), c)))}>) ->
  P.Problem.InContainer<F, field, MUL(f, side), P.Point{x, y}>:
  match inner:
    case P.InContainer{+left, +right, +bottom, +top}:
      +qx: F = ADD(cx, ADD(MUL(MUL(lx, i), c), NEG(MUL(MUL(ly, i), s))))
      +qy: F = ADD(cy, ADD(MUL(MUL(lx, i), s), MUL(MUL(ly, i), c)))
      +equations: C.Certificate.Equations(TC, ''' + V + ''', ''' + exprs(['x - (f*cx + (lx*c - ly*s))', 'f*i - 1'], N) + ''') =
        C.Both{G.Geometry.zero_difference(TC, x, ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s)))), x_is_below, x_is_above),
          C.Both{Scaling.inverse_equation(TC, f, i, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above)), Unit{}}}
      +y_equations: C.Certificate.Equations(TC, ''' + V + ''', ''' + exprs(['y - (f*cy + (lx*s + ly*c))', 'f*i - 1'], N) + ''') =
        C.Both{G.Geometry.zero_difference(TC, y, ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c))), y_is_below, y_is_above),
          C.Both{Scaling.inverse_equation(TC, f, i, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above)), Unit{}}}
      Scaling.in_container(TC, MUL(f, side), x, y,
        Scaling.coordinate(TC, x, MUL(f, qx), MUL(f, side),
          ''' + same(N, V, ['x - (f*cx + (lx*c - ly*s))', 'f*i - 1'], 'equations', 'x', 'f*(cx + ((lx*i)*c - (ly*i)*s))') + ''',
          ''' + le(['f', 'q'], values('f', 'qx'), ['f', 'q'], facts('f_nonnegative', 'left'), [], 'Unit{}', '0', 'f*q') + ''',
          ''' + le(['f', 'q', 'side'], values('f', 'qx', 'side'), ['f', 'side - q'], facts('f_nonnegative', 'Scaling.fact(TC, qx, side, right)'), [], 'Unit{}', 'f*q', 'f*side') + '''),
        Scaling.coordinate(TC, y, MUL(f, qy), MUL(f, side),
          ''' + same(N, V, ['y - (f*cy + (lx*s + ly*c))', 'f*i - 1'], 'y_equations', 'y', 'f*(cy + ((lx*i)*s + (ly*i)*c))') + ''',
          ''' + le(['f', 'q'], values('f', 'qy'), ['f', 'q'], facts('f_nonnegative', 'bottom'), [], 'Unit{}', '0', 'f*q') + ''',
          ''' + le(['f', 'q', 'side'], values('f', 'qy', 'side'), ['f', 'side - q'], facts('f_nonnegative', 'Scaling.fact(TC, qy, side, top)'), [], 'Unit{}', 'f*q', 'f*side') + '''))
'''
PARTS.append(src2)

src3 = '''
def Scaling.scale_fits_at(TPL, +square: P.Problem.Square<F, field>, +side: F, +factor: F, fits: Y.Symmetry.Fits(TC, square, side),
  +at_least: LE(ONE, factor), positive: LE(factor, ZERO) -> Empty, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Scaling.scale_center(TC, factor, square), point>) ->
  P.Problem.InContainer<F, field, MUL(factor, side), point>:
  match square point inside:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}} P.Point{+x, +y}
      P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      Scaling.scale_with_cancel(TC, cx, cy, c, s, unit_below, unit_above, lx, ly, x, y, factor, side, fits, at_least,
        x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above,
        AL.mul_inverse(TC, factor, positive))
'''
helper = '''
def Scaling.scale_with_cancel(TPL, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: LE(ADD(MUL(c, c), MUL(s, s)), ONE), +unit_above: LE(ONE, ADD(MUL(c, c), MUL(s, s))),
  +lx: F, +ly: F, +x: F, +y: F, +f: F, +side: F,
  fits: Y.Symmetry.Fits(TC, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, side),
  +at_least: LE(ONE, f),
  +x_at_most: LE(lx, HALF), +x_at_least: LE(NEG(HALF), lx), +y_at_most: LE(ly, HALF), +y_at_least: LE(NEG(HALF), ly),
  +x_is_below: LE(x, ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s))))),
  +x_is_above: LE(ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s)))), x),
  +y_is_below: LE(y, ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c)))),
  +y_is_above: LE(ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c))), y),
  cancel: SAME(MUL(f, INV(f)), ONE)) ->
  P.Problem.InContainer<F, field, MUL(f, side), P.Point{x, y}>:
  (+cancel_below, +cancel_above) = cancel
  +i: F = INV(f)
  +i_nonnegative: LE(ZERO, i) = Scaling.inverse_nonnegative(TC, f, i, at_least, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above))
  +i_at_most: LE(i, ONE) = Scaling.inverse_at_most_one(TC, f, i, at_least, i_nonnegative, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above))
  +h_nonnegative: LE(ZERO, HALF) = Scaling.half_nonnegative(TC)
  +li: F = MUL(lx, i)
  +mi: F = MUL(ly, i)
  +qx: F = ADD(cx, ADD(MUL(li, c), NEG(MUL(mi, s))))
  +qy: F = ADD(cy, ADD(MUL(li, s), MUL(mi, c)))
  Scaling.scale_finish(TC, cx, cy, c, s, lx, ly, x, y, f, i, side,
    x_is_below, x_is_above, y_is_below, y_is_above, cancel_below, cancel_above,
    AX.le_transitive(ZERO, ONE, f, K.Field.zero_le_one(F, field), at_least),
    fits(P.Point{qx, qy},
      P.Containment{li, mi,
        Scaling.scaled_at_most(TC, HALF, lx, i, x_at_most, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_least(TC, HALF, lx, i, x_at_least, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_most(TC, HALF, ly, i, y_at_most, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_least(TC, HALF, ly, i, y_at_least, i_nonnegative, i_at_most, h_nonnegative),
        AX.le_reflexive(qx), AX.le_reflexive(qx), AX.le_reflexive(qy), AX.le_reflexive(qy)}))

def Scaling.scale_fits(TPL, +square: P.Problem.Square<F, field>, +side: F, +factor: F, fits: Y.Symmetry.Fits(TC, square, side),
  +at_least: LE(ONE, factor), positive: LE(factor, ZERO) -> Empty) ->
  Y.Symmetry.Fits(TC, Scaling.scale_center(TC, factor, square), MUL(factor, side)):
  +point => inside => Scaling.scale_fits_at(TC, square, side, factor, fits, at_least, positive, point, inside)
'''
PARTS.append(helper.split('def Scaling.scale_fits(')[0] + src3 + '\ndef Scaling.scale_fits(' + helper.split('def Scaling.scale_fits(')[1])

M = ['h', 'lx', 'i', 'f']
MV = values('HALF', 'lx', 'i', 'f')
def strict_refute(name, reached_fact_text, reached_fact_proof, bound_text, bound_proof):
    return f'''
def Scaling.{name}(TPL, +lx: F, +i: F, +f: F, +bound: {bound_proof[0]}, +i_nonnegative: LE(ZERO, i), +f_nonnegative: LE(ZERO, f),
  +cancel_below: LE(MUL(f, i), ONE), +cancel_above: LE(ONE, MUL(f, i)), +reached: {reached_fact_proof[0]}) -> LE(f, Scaling.number(TC, 1n)):
  ''' + le(M, MV, [reached_fact_text, bound_text, 'i', 'f'],
          facts(reached_fact_proof[1], bound_proof[1], 'i_nonnegative', 'f_nonnegative'),
          ['f*i - 1', 'h + h - 1'],
          facts('Scaling.inverse_equation(TC, f, i, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above))', 'Scaling.half_equation(TC)'),
          'f', '1', products=3)

src4 = strict_refute('refute_above', 'lx*i - h', ('LE(HALF, MUL(lx, i))', 'Scaling.fact(TC, HALF, MUL(lx, i), reached)'),
                     'h - lx', ('LE(lx, HALF)', 'Scaling.fact(TC, lx, HALF, bound)'))
src4 += strict_refute('refute_below', '-h - lx*i', ('LE(MUL(lx, i), NEG(HALF))', 'Scaling.fact(TC, MUL(lx, i), NEG(HALF), reached)'),
                      'lx - (-h)', ('LE(NEG(HALF), lx)', 'Scaling.fact(TC, NEG(HALF), lx, bound)'))
PARTS.append(src4)

N2 = ['cx', 'cy', 'c', 's', 'lx', 'ly', 'x', 'y', 'f', 'i']
V2 = values(*N2)
src5 = '''
def Scaling.never_reaches(TPL, +lx: F, +i: F, +f: F, +greater: O.FieldOrder.Strict(TC, ONE, f),
  +at_most: LE(lx, HALF), +at_least: LE(NEG(HALF), lx), +i_nonnegative: LE(ZERO, i), +f_nonnegative: LE(ZERO, f),
  +cancel_below: LE(MUL(f, i), ONE), +cancel_above: LE(ONE, MUL(f, i))) ->
  (LE(HALF, MUL(lx, i)) -> Empty) & (LE(MUL(lx, i), NEG(HALF)) -> Empty):
  (
    reached => O.FieldOrder.lt_of(TC, ONE, f, greater)(Scaling.number_bound_above(TC, f,
      Scaling.refute_above(TC, lx, i, f, at_most, i_nonnegative, f_nonnegative, cancel_below, cancel_above, reached))),
    reached => O.FieldOrder.lt_of(TC, ONE, f, greater)(Scaling.number_bound_above(TC, f,
      Scaling.refute_below(TC, lx, i, f, at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above, reached)))
  )

def Scaling.interior_of_sames(TPL, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: LE(ADD(MUL(c, c), MUL(s, s)), ONE), +unit_above: LE(ONE, ADD(MUL(c, c), MUL(s, s))),
  +local_x: F, +local_y: F, +x: F, +y: F,
  x_never: (LE(HALF, local_x) -> Empty) & (LE(local_x, NEG(HALF)) -> Empty),
  y_never: (LE(HALF, local_y) -> Empty) & (LE(local_y, NEG(HALF)) -> Empty),
  x_same: SAME(x, ADD(cx, ADD(MUL(local_x, c), NEG(MUL(local_y, s))))),
  y_same: SAME(y, ADD(cy, ADD(MUL(local_x, s), MUL(local_y, c))))) ->
  P.Problem.InteriorContainment<F, field, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, P.Point{x, y}>:
  (x_below, x_above) = x_never
  (y_below, y_above) = y_never
  (x_is_below, x_is_above) = x_same
  (y_is_below, y_is_above) = y_same
  P.InteriorContainment{local_x, local_y, x_below, x_above, y_below, y_above, x_is_below, x_is_above, y_is_below, y_is_above}

def Scaling.interior_back_with(TPL, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: LE(ADD(MUL(c, c), MUL(s, s)), ONE), +unit_above: LE(ONE, ADD(MUL(c, c), MUL(s, s))),
  +lx: F, +ly: F, +x: F, +y: F, +f: F, +greater: O.FieldOrder.Strict(TC, ONE, f),
  +x_at_most: LE(lx, HALF), +x_at_least: LE(NEG(HALF), lx), +y_at_most: LE(ly, HALF), +y_at_least: LE(NEG(HALF), ly),
  +x_is_below: LE(x, ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s))))),
  +x_is_above: LE(ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s)))), x),
  +y_is_below: LE(y, ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c)))),
  +y_is_above: LE(ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c))), y),
  cancel: SAME(MUL(f, INV(f)), ONE)) ->
  P.Problem.InteriorContainment<F, field, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, P.Point{MUL(INV(f), x), MUL(INV(f), y)}>:
  (+cancel_below, +cancel_above) = cancel
  +i: F = INV(f)
  +at_least: LE(ONE, f) = O.FieldOrder.le_of_lt(TC, ONE, f, O.FieldOrder.lt_of(TC, ONE, f, greater))
  +i_nonnegative: LE(ZERO, i) = Scaling.inverse_nonnegative(TC, f, i, at_least, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above))
  +f_nonnegative: LE(ZERO, f) = AX.le_transitive(ZERO, ONE, f, K.Field.zero_le_one(F, field), at_least)
  +equations: C.Certificate.Equations(TC, ''' + V2 + ''', ''' + exprs(['x - (f*cx + (lx*c - ly*s))', 'f*i - 1'], N2) + ''') =
    C.Both{G.Geometry.zero_difference(TC, x, ADD(MUL(f, cx), ADD(MUL(lx, c), NEG(MUL(ly, s)))), x_is_below, x_is_above),
      C.Both{Scaling.inverse_equation(TC, f, i, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above)), Unit{}}}
  +y_equations: C.Certificate.Equations(TC, ''' + V2 + ''', ''' + exprs(['y - (f*cy + (lx*s + ly*c))', 'f*i - 1'], N2) + ''') =
    C.Both{G.Geometry.zero_difference(TC, y, ADD(MUL(f, cy), ADD(MUL(lx, s), MUL(ly, c))), y_is_below, y_is_above),
      C.Both{Scaling.inverse_equation(TC, f, i, Scaling.pair(TC, MUL(f, i), ONE, cancel_below, cancel_above)), Unit{}}}
  Scaling.interior_of_sames(TC, cx, cy, c, s, unit_below, unit_above, MUL(lx, i), MUL(ly, i), MUL(i, x), MUL(i, y),
    Scaling.never_reaches(TC, lx, i, f, greater, x_at_most, x_at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above),
    Scaling.never_reaches(TC, ly, i, f, greater, y_at_most, y_at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above),
    ''' + same(N2, V2, ['x - (f*cx + (lx*c - ly*s))', 'f*i - 1'], 'equations', 'i*x', 'cx + ((lx*i)*c - (ly*i)*s)') + ''',
    ''' + same(N2, V2, ['y - (f*cy + (lx*s + ly*c))', 'f*i - 1'], 'y_equations', 'i*y', 'cy + ((lx*i)*s + (ly*i)*c)') + ''')

def Scaling.interior_back(TPL, +square: P.Problem.Square<F, field>, +factor: F, +greater: O.FieldOrder.Strict(TC, ONE, factor),
  +point: P.Problem.Point<F>, inside: P.Problem.Containment<F, field, Scaling.scale_center(TC, factor, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Scaling.scale_point(TC, INV(factor), point)>:
  match square point inside:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}} P.Point{+x, +y}
      P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      Scaling.interior_back_with(TC, cx, cy, c, s, unit_below, unit_above, lx, ly, x, y, factor, greater,
        x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above,
        AL.mul_inverse(TC, factor, below => O.FieldOrder.lt_of(TC, ONE, factor, greater)(
          AX.le_transitive(factor, ZERO, ONE, below, K.Field.zero_le_one(F, field)))))
'''
PARTS.append(src5)

PF = ['cx', 'c', 's', 'h', 'side']
PV = values('cx', 'c', 's', 'HALF', 'side')
xs = ['cx + (h*c - 0*s)', 'cx + ((-h)*c - 0*s)', 'cx + (0*c - h*s)', 'cx + (0*c - (-h)*s)']
xb = ['ADD(cx, ADD(MUL(HALF, c), NEG(MUL(ZERO, s))))', 'ADD(cx, ADD(MUL(NEG(HALF), c), NEG(MUL(ZERO, s))))',
      'ADD(cx, ADD(MUL(ZERO, c), NEG(MUL(HALF, s))))', 'ADD(cx, ADD(MUL(ZERO, c), NEG(MUL(NEG(HALF), s))))']
fact_texts = ['0 - side']
fact_proofs = ['Scaling.fact(TC, side, ZERO, nonpositive)']
for k, (t, b) in enumerate(zip(xs, xb)):
    fact_texts += [t, f'side - ({t})']
    fact_proofs += [f'left_{k}', f'Scaling.fact(TC, {b}, side, right_{k})']
locals_ = [('HALF', 'ZERO'), ('NEG(HALF)', 'ZERO'), ('ZERO', 'HALF'), ('ZERO', 'NEG(HALF)')]
def point_at(sq, lx, ly):
    return f'Scaling.point_at(TC, {sq}, {lx}, {ly})'
src6 = '''
def Scaling.anything(TPL, +a: F, +b: F, +broken: LE(ZERO, NEG(Scaling.number(TC, 1n)))) -> LE(a, b):
  ''' + le(['a', 'b'], values('a', 'b'), ['-1'], facts('broken'), [], 'Unit{}', 'a', 'b', squares=['b - a + 1', 'b - a - 1']) + '''

def Scaling.point_at(TPL, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F) -> P.Problem.Point<F>:
  P.Point{
    ADD(P.Problem.center_x(F, field, square), ADD(MUL(local_x, P.Problem.cosine(F, field, square)), NEG(MUL(local_y, P.Problem.sine(F, field, square))))),
    ADD(P.Problem.center_y(F, field, square), ADD(MUL(local_x, P.Problem.sine(F, field, square)), MUL(local_y, P.Problem.cosine(F, field, square))))}

def Scaling.containment_at(TPL, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F,
  +x_at_most: LE(local_x, HALF), +x_at_least: LE(NEG(HALF), local_x), +y_at_most: LE(local_y, HALF), +y_at_least: LE(NEG(HALF), local_y)) ->
  P.Problem.Containment<F, field, square, Scaling.point_at(TC, square, local_x, local_y)>:
  +x: F = P.Problem.x(F, Scaling.point_at(TC, square, local_x, local_y))
  +y: F = P.Problem.y(F, Scaling.point_at(TC, square, local_x, local_y))
  P.Containment{local_x, local_y, x_at_most, x_at_least, y_at_most, y_at_least,
    AX.le_reflexive(x), AX.le_reflexive(x), AX.le_reflexive(y), AX.le_reflexive(y)}

def Scaling.negative_half_at_most(TPL, +h_nonnegative: LE(ZERO, HALF)) -> LE(NEG(HALF), HALF):
  AX.le_transitive(NEG(HALF), ZERO, HALF, Y.Symmetry.negate_bound_left(TC, ZERO, HALF,
    AL.le_respects(TC, ZERO, HALF, NEG(ZERO), HALF, h_nonnegative,
      R.FieldRing.equal(TC, R.NoValues{}, R.Number{0n}, R.Negate{R.Number{0n}}, {==}), AL.same_reflexive(TC, HALF))), h_nonnegative)

def Scaling.negative_half_below_zero(TPL, +h_nonnegative: LE(ZERO, HALF)) -> LE(NEG(HALF), ZERO):
  Y.Symmetry.negate_bound_left(TC, ZERO, HALF,
    AL.le_respects(TC, ZERO, HALF, NEG(ZERO), HALF, h_nonnegative,
      R.FieldRing.equal(TC, R.NoValues{}, R.Number{0n}, R.Negate{R.Number{0n}}, {==}), AL.same_reflexive(TC, HALF)))

def Scaling.side_broken(TPL, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: LE(ADD(MUL(c, c), MUL(s, s)), ONE), +unit_above: LE(ONE, ADD(MUL(c, c), MUL(s, s))), +side: F,
  +nonpositive: LE(side, ZERO),
''' + ''.join(f'''  +left_{k}: LE(ZERO, {b}), +right_{k}: LE({b}, side),
''' for k, b in enumerate(xb)) + '''  +done: Unit) -> LE(ZERO, NEG(Scaling.number(TC, 1n))):
  ''' + le(PF, PV, fact_texts, facts(*fact_proofs), ['c^2 + s^2 - 1', 'h + h - 1'],
          facts('G.Geometry.unit(TC, c, s, unit_below, unit_above)', 'Scaling.half_equation(TC)'), '0', '-1') + '''

def Scaling.side_positive_at(TPL, +square: P.Problem.Square<F, field>, +side: F, +target: F, +less: O.FieldOrder.Strict(TC, side, target),
''' + ''.join(f'''  +inside_{k}: P.Problem.InContainer<F, field, side, {point_at('square', a, b)}>,
''' for k, (a, b) in enumerate(locals_)) + '''  +nonpositive: LE(side, ZERO)) -> Empty:
  match square inside_0 inside_1 inside_2 inside_3:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}}
      P.InContainer{+left_0, +right_0, +b0, +t0} P.InContainer{+left_1, +right_1, +b1, +t1}
      P.InContainer{+left_2, +right_2, +b2, +t2} P.InContainer{+left_3, +right_3, +b3, +t3}:
      O.FieldOrder.lt_of(TC, side, target, less)(Scaling.anything(TC, target, side,
        Scaling.side_broken(TC, cx, cy, c, s, unit_below, unit_above, side, nonpositive,
          left_0, right_0, left_1, right_1, left_2, right_2, left_3, right_3, Unit{})))
'''
PARTS.append(src6)

PT = '~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>'
PC = '~F, ~field, ~count, ~side, ~packing'
SQ = 'S.Packings.squares(F, field, count, side, packing)'
FT = 'S.Packings.fits(F, field, count, side, packing)'
DJ = 'S.Packings.disjoint(F, field, count, side, packing)'
src7 = '''
type Scaling.ClosedFamily<-F: Kind(&2), -field: K.Field<F>, -count: Nat, -target: F> is Type:
  ClosedFamily{
    squares: Nat -> P.Problem.Square<F, field>,
    fits: @index: Nat -> N.Natural.Le(1n+index, count) -> @point: P.Problem.Point<F> ->
      P.Problem.Containment<F, field, squares(index), point> -> P.Problem.InContainer<F, field, target, point>,
    disjoint: @left: Nat -> @right: Nat -> N.Natural.Le(1n+left, count) -> N.Natural.Le(1n+right, count) ->
      ({left == right : Nat} -> Empty) -> @point: P.Problem.Point<F> ->
      P.Problem.Containment<F, field, squares(left), point> -> P.Problem.Containment<F, field, squares(right), point> -> Empty
  }

def Scaling.container_to(TPL, +first: F, +second: F, +point: P.Problem.Point<F>, same: SAME(first, second),
  inside: P.Problem.InContainer<F, field, first, point>) -> P.Problem.InContainer<F, field, second, point>:
  (+forward, +backward) = same
  match inside:
    case P.InContainer{left, right, bottom, top}:
      P.InContainer{left, AX.le_transitive(P.Problem.x(F, point), first, second, right, forward),
        bottom, AX.le_transitive(P.Problem.y(F, point), first, second, top, forward)}

def Scaling.factor_spans(TPL, +target: F, +side: F, cancel: SAME(MUL(side, INV(side)), ONE)) ->
  SAME(MUL(MUL(target, INV(side)), side), target):
  +i: F = INV(side)
  ''' + same(['t', 'i', 'side'], values('target', 'i', 'side'), ['side*i - 1'],
             facts('Scaling.inverse_equation(TC, side, i, cancel)'), '(t*i)*side', 't') + '''

def Scaling.factor_not_above(TPL, +target: F, +side: F, +side_nonnegative: LE(ZERO, side),
  spans: SAME(MUL(MUL(target, INV(side)), side), target), +below: LE(MUL(target, INV(side)), ONE)) -> LE(target, side):
  +i: F = INV(side)
  ''' + le(['t', 'i', 'side'], values('target', 'i', 'side'), ['1 - t*i', 'side'],
          facts('Scaling.fact(TC, MUL(target, i), Scaling.number(TC, 1n), AL.le_respects(TC, MUL(target, i), ONE, MUL(target, i), Scaling.number(TC, 1n), below, AL.same_reflexive(TC, MUL(target, i)), Scaling.one_is_number(TC)))',
                'side_nonnegative'),
          ['(t*i)*side - t'], facts('Scaling.equation(TC, MUL(MUL(target, i), side), target, spans)'), 't', 'side') + '''

def Scaling.family_fits(''' + PT + ''', +target: F, +factor: F, spans: SAME(MUL(factor, side), target),
  +at_least: LE(ONE, factor), positive: LE(factor, ZERO) -> Empty, +index: Nat, bound: N.Natural.Le(1n+index, count),
  +point: P.Problem.Point<F>, inside: P.Problem.Containment<F, field, Scaling.scale_center(TC, factor, ''' + SQ + '''(index)), point>) ->
  P.Problem.InContainer<F, field, target, point>:
  Scaling.container_to(TC, MUL(factor, side), target, point, spans,
    Scaling.scale_fits(TC, ''' + SQ + '''(index), side, factor, ''' + FT + '''(index, bound), at_least, positive)(point, inside))

def Scaling.family_disjoint(''' + PT + ''', +factor: F, +greater: O.FieldOrder.Strict(TC, ONE, factor),
  +left: Nat, +right: Nat, left_bound: N.Natural.Le(1n+left, count), right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.Containment<F, field, Scaling.scale_center(TC, factor, ''' + SQ + '''(left)), point>,
  second: P.Problem.Containment<F, field, Scaling.scale_center(TC, factor, ''' + SQ + '''(right)), point>) -> Empty:
  ''' + DJ + '''(left, right, left_bound, right_bound, different, Scaling.scale_point(TC, INV(factor), point),
    Scaling.interior_back(TC, ''' + SQ + '''(left), factor, greater, point, first),
    Scaling.interior_back(TC, ''' + SQ + '''(right), factor, greater, point, second))

def Scaling.side_positive(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  LE(side, ZERO) -> Empty:
  +h_nonnegative: LE(ZERO, HALF) = Scaling.half_nonnegative(TC)
  +first: P.Problem.Square<F, field> = ''' + SQ + '''(0n)
  +inside_0: P.Problem.InContainer<F, field, side, Scaling.point_at(TC, first, HALF, ZERO)> = ''' + FT + '''(0n, nonempty, Scaling.point_at(TC, first, HALF, ZERO),
    Scaling.containment_at(TC, first, HALF, ZERO, AX.le_reflexive(HALF), Scaling.negative_half_at_most(TC, h_nonnegative), h_nonnegative, Scaling.negative_half_below_zero(TC, h_nonnegative)))
  +inside_1: P.Problem.InContainer<F, field, side, Scaling.point_at(TC, first, NEG(HALF), ZERO)> = ''' + FT + '''(0n, nonempty, Scaling.point_at(TC, first, NEG(HALF), ZERO),
    Scaling.containment_at(TC, first, NEG(HALF), ZERO, Scaling.negative_half_at_most(TC, h_nonnegative), AX.le_reflexive(NEG(HALF)), h_nonnegative, Scaling.negative_half_below_zero(TC, h_nonnegative)))
  +inside_2: P.Problem.InContainer<F, field, side, Scaling.point_at(TC, first, ZERO, HALF)> = ''' + FT + '''(0n, nonempty, Scaling.point_at(TC, first, ZERO, HALF),
    Scaling.containment_at(TC, first, ZERO, HALF, h_nonnegative, Scaling.negative_half_below_zero(TC, h_nonnegative), AX.le_reflexive(HALF), Scaling.negative_half_at_most(TC, h_nonnegative)))
  +inside_3: P.Problem.InContainer<F, field, side, Scaling.point_at(TC, first, ZERO, NEG(HALF))> = ''' + FT + '''(0n, nonempty, Scaling.point_at(TC, first, ZERO, NEG(HALF)),
    Scaling.containment_at(TC, first, ZERO, NEG(HALF), h_nonnegative, Scaling.negative_half_below_zero(TC, h_nonnegative), Scaling.negative_half_at_most(TC, h_nonnegative), AX.le_reflexive(NEG(HALF))))
  nonpositive => Scaling.side_positive_at(TC, first, side, target, less, inside_0, inside_1, inside_2, inside_3, nonpositive)

def Scaling.side_cancel(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  SAME(MUL(side, INV(side)), ONE):
  AL.mul_inverse(TC, side, Scaling.side_positive(''' + PC + ''', target, less, nonempty))

def Scaling.greater(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  O.FieldOrder.Strict(TC, ONE, MUL(target, INV(side))):
  +factor: F = MUL(target, INV(side))
  +side_nonnegative: LE(ZERO, side) = S.Packings.side_nonnegative(F, field, count, side, packing)
  O.FieldOrder.strict_of(TC, ONE, factor,
    below => O.FieldOrder.lt_of(TC, side, target, less)(Scaling.factor_not_above(TC, target, side, side_nonnegative,
      Scaling.factor_spans(TC, target, side, Scaling.side_cancel(''' + PC + ''', target, less, nonempty)), below)))

def Scaling.closed_square(''' + PT + ''', +target: F, +index: Nat) -> P.Problem.Square<F, field>:
  Scaling.scale_center(TC, MUL(target, INV(side)), ''' + SQ + '''(index))

def Scaling.closed_fits(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count),
  +index: Nat, +bound: N.Natural.Le(1n+index, count)) -> Y.Symmetry.Fits(TC, Scaling.closed_square(''' + PC + ''', target, index), target):
  +factor: F = MUL(target, INV(side))
  +greater: O.FieldOrder.Strict(TC, ONE, factor) = Scaling.greater(''' + PC + ''', target, less, nonempty)
  +at_least: LE(ONE, factor) = O.FieldOrder.le_of_lt(TC, ONE, factor, O.FieldOrder.lt_of(TC, ONE, factor, greater))
  +point => inside => Scaling.family_fits(''' + PC + ''', target, factor, Scaling.factor_spans(TC, target, side, Scaling.side_cancel(''' + PC + ''', target, less, nonempty)),
    at_least, below => O.FieldOrder.lt_of(TC, ONE, factor, greater)(AX.le_transitive(factor, ZERO, ONE, below, K.Field.zero_le_one(F, field))),
    index, bound, point, inside)

def Scaling.closed_disjoint(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count),
  +left: Nat, +right: Nat, +left_bound: N.Natural.Le(1n+left, count), +right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty) -> @point: P.Problem.Point<F> ->
  P.Problem.Containment<F, field, Scaling.closed_square(''' + PC + ''', target, left), point> ->
  P.Problem.Containment<F, field, Scaling.closed_square(''' + PC + ''', target, right), point> -> Empty:
  +point => first => second => Scaling.family_disjoint(''' + PC + ''', MUL(target, INV(side)), Scaling.greater(''' + PC + ''', target, less, nonempty),
    left, right, left_bound, right_bound, different, point, first, second)

def Scaling.closed_family(''' + PT + ''', +target: F, +less: O.FieldOrder.Strict(TC, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  Scaling.ClosedFamily<F, field, count, target>:
  ClosedFamily{
    index => Scaling.closed_square(''' + PC + ''', target, index),
    index => bound => Scaling.closed_fits(''' + PC + ''', target, less, nonempty, index, bound),
    left => right => left_bound => right_bound => different =>
      Scaling.closed_disjoint(''' + PC + ''', target, less, nonempty, left, right, left_bound, right_bound, different)
  }
'''
PARTS.append(src7)

(ROOT / 'bend' / 'Scaling.bend').write_text(expand(''.join(PARTS)))
