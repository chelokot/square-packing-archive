#!/usr/bin/env python3
"""Write bend/Membership.bend: deciding whether a square contains a point, and corner data.

`Membership.inside` decides containment through the four bounds on the local
coordinates. `Membership.Corners` records that the four corners of a square
lie in the container; unlike a `Fits` function it is data, so a proof can use
it many times, and `Membership.fits` turns it back into `Fits`.
"""
from bend_proof import ROOT, Context, T, expand, num

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
'''

DECISIONS = '''
def Membership.decision(TPL, +a: F, +b: F, order: Or(LE(a, b), LE(a, b) -> Empty)) -> Bool:
  match order:
    case Inl{below}:
      True{}
    case Inr{above}:
      False{}

def Membership.decide(TPL, +a: F, +b: F) -> Bool:
  Membership.decision(TC, a, b, AX.le_decidable(a, b))

def Membership.below_of(TPL, +a: F, +b: F, order: Or(LE(a, b), LE(a, b) -> Empty),
  holds: B.Bits.Holds(Membership.decision(TC, a, b, order))) -> LE(a, b):
  match order:
    case Inl{below}:
      below
    case Inr{above}:
      match holds:

def Membership.below(TPL, +a: F, +b: F, holds: B.Bits.Holds(Membership.decide(TC, a, b))) -> LE(a, b):
  Membership.below_of(TC, a, b, AX.le_decidable(a, b), holds)

def Membership.decided_of(TPL, +a: F, +b: F, order: Or(LE(a, b), LE(a, b) -> Empty), below: LE(a, b)) ->
  B.Bits.Holds(Membership.decision(TC, a, b, order)):
  match order:
    case Inl{yes}:
      Unit{}
    case Inr{no}:
      no(below)

def Membership.decided(TPL, +a: F, +b: F, below: LE(a, b)) -> B.Bits.Holds(Membership.decide(TC, a, b)):
  Membership.decided_of(TC, a, b, AX.le_decidable(a, b), below)

def Membership.above_of(TPL, +a: F, +b: F, order: Or(LE(a, b), LE(a, b) -> Empty),
  holds: B.Bits.Holds(Bool.not(Membership.decision(TC, a, b, order)))) -> O.FieldOrder.IsRight(TC, a, b, order):
  match order:
    case Inl{below}:
      match holds:
    case Inr{above}:
      Unit{}

def Membership.above(TPL, +a: F, +b: F, holds: B.Bits.Holds(Bool.not(Membership.decide(TC, a, b)))) -> O.FieldOrder.Strict(TC, b, a):
  Membership.above_of(TC, a, b, AX.le_decidable(a, b), holds)

def Membership.within(TPL, +x: F, +y: F) -> Bool:
  Bool.and(Membership.decide(TC, x, HALF), Bool.and(Membership.decide(TC, NEG(HALF), x),
    Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))))

def Membership.inside(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>) -> Bool:
  Membership.within(TC, G.Geometry.local_x(TC, square, point), G.Geometry.local_y(TC, square, point))

def Membership.local_of(TPL, +x: F, +y: F, +holds: B.Bits.Holds(Membership.within(TC, x, y))) -> G.Geometry.Local<F, field, x, y>:
  +first: Bool = Membership.decide(TC, x, HALF)
  +second: Bool = Membership.decide(TC, NEG(HALF), x)
  +third: Bool = Membership.decide(TC, y, HALF)
  +fourth: Bool = Membership.decide(TC, NEG(HALF), y)
  +rest: Bool = Bool.and(second, Bool.and(third, fourth))
  +last: Bool = Bool.and(third, fourth)
  G.Local{
    Membership.below(TC, x, HALF, B.Bits.left(first, rest, holds)),
    Membership.below(TC, NEG(HALF), x, B.Bits.left(second, last, B.Bits.right(first, rest, holds))),
    Membership.below(TC, y, HALF, B.Bits.left(third, fourth, B.Bits.right(second, last, B.Bits.right(first, rest, holds)))),
    Membership.below(TC, NEG(HALF), y, B.Bits.right(third, fourth, B.Bits.right(second, last, B.Bits.right(first, rest, holds))))}

def Membership.contains(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +holds: B.Bits.Holds(Membership.inside(TC, square, point))) -> P.Problem.Containment<F, field, square, point>:
  G.Geometry.local_contains(TC, square, point,
    Membership.local_of(TC, G.Geometry.local_x(TC, square, point), G.Geometry.local_y(TC, square, point), holds))

def Membership.inside_local(TPL, +x: F, +y: F, local: G.Geometry.Local<F, field, x, y>) ->
  B.Bits.Holds(Bool.and(Membership.decide(TC, x, HALF), Bool.and(Membership.decide(TC, NEG(HALF), x),
    Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))))):
  match local:
    case G.Local{+first, +second, +third, +fourth}:
      B.Bits.both(Membership.decide(TC, x, HALF), Bool.and(Membership.decide(TC, NEG(HALF), x),
          Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))),
        Membership.decided(TC, x, HALF, first),
        B.Bits.both(Membership.decide(TC, NEG(HALF), x), Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y)),
          Membership.decided(TC, NEG(HALF), x, second),
          B.Bits.both(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y),
            Membership.decided(TC, y, HALF, third), Membership.decided(TC, NEG(HALF), y, fourth))))

def Membership.inside_of(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +containment: P.Problem.Containment<F, field, square, point>) -> B.Bits.Holds(Membership.inside(TC, square, point)):
  Membership.inside_local(TC, G.Geometry.local_x(TC, square, point), G.Geometry.local_y(TC, square, point),
    G.Geometry.contains_local(TC, square, point, containment))

def Membership.Missing(TPL, +x: F, +y: F) -> Type:
  Or(O.FieldOrder.Strict(TC, HALF, x), Or(O.FieldOrder.Strict(TC, x, NEG(HALF)),
    Or(O.FieldOrder.Strict(TC, HALF, y), O.FieldOrder.Strict(TC, y, NEG(HALF)))))

def Membership.missing_last(TPL, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(TC, y, HALF))), B.Bits.Holds(Bool.not(Membership.decide(TC, NEG(HALF), y))))) ->
  Or(O.FieldOrder.Strict(TC, HALF, y), O.FieldOrder.Strict(TC, y, NEG(HALF))):
  match split:
    case Inl{no}:
      Inl{Membership.above(TC, y, HALF, no)}
    case Inr{no}:
      Inr{Membership.above(TC, NEG(HALF), y, no)}

def Membership.missing_rest(TPL, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(TC, NEG(HALF), x))),
    B.Bits.Holds(Bool.not(Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y)))))) ->
  Or(O.FieldOrder.Strict(TC, x, NEG(HALF)), Or(O.FieldOrder.Strict(TC, HALF, y), O.FieldOrder.Strict(TC, y, NEG(HALF)))):
  match split:
    case Inl{no}:
      Inl{Membership.above(TC, NEG(HALF), x, no)}
    case Inr{no}:
      Inr{Membership.missing_last(TC, x, y, B.Bits.not_both(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y), no))}

def Membership.missing_from(TPL, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(TC, x, HALF))),
    B.Bits.Holds(Bool.not(Bool.and(Membership.decide(TC, NEG(HALF), x), Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))))))) ->
  Membership.Missing(TC, x, y):
  match split:
    case Inl{no}:
      Inl{Membership.above(TC, x, HALF, no)}
    case Inr{no}:
      Inr{Membership.missing_rest(TC, x, y, B.Bits.not_both(Membership.decide(TC, NEG(HALF), x),
        Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y)), no))}

def Membership.missing(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +outside: B.Bits.Holds(Bool.not(Membership.inside(TC, square, point)))) ->
  Membership.Missing(TC, G.Geometry.local_x(TC, square, point), G.Geometry.local_y(TC, square, point)):
  +x: F = G.Geometry.local_x(TC, square, point)
  +y: F = G.Geometry.local_y(TC, square, point)
  Membership.missing_from(TC, x, y, B.Bits.not_both(Membership.decide(TC, x, HALF),
    Bool.and(Membership.decide(TC, NEG(HALF), x), Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))), outside))
'''

ELIMINATORS = '''
def Membership.when_split(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  yes: P.Problem.Containment<F, field, square, point> -> Goal, no: B.Bits.Holds(Bool.not(Membership.inside(TC, square, point))) -> Goal,
  split: Or(B.Bits.Holds(Membership.inside(TC, square, point)), B.Bits.Holds(Bool.not(Membership.inside(TC, square, point))))) -> Goal:
  match split:
    case Inl{inside}:
      yes(Membership.contains(TC, square, point, inside))
    case Inr{outside}:
      no(outside)

def Membership.when(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  yes: P.Problem.Containment<F, field, square, point> -> Goal, no: B.Bits.Holds(Bool.not(Membership.inside(TC, square, point))) -> Goal) -> Goal:
  Membership.when_split(TC, square, point, Goal, yes, no, B.Bits.split(Membership.inside(TC, square, point)))

def Membership.local_split(TPL, +x: F, +y: F, -Goal: Type,
  yes: G.Geometry.Local<F, field, x, y> -> Goal, no: Membership.Missing(TC, x, y) -> Goal,
  split: Or(B.Bits.Holds(Membership.within(TC, x, y)), B.Bits.Holds(Bool.not(Membership.within(TC, x, y))))) -> Goal:
  match split:
    case Inl{inside}:
      yes(Membership.local_of(TC, x, y, inside))
    case Inr{outside}:
      no(Membership.missing_from(TC, x, y, B.Bits.not_both(Membership.decide(TC, x, HALF),
        Bool.and(Membership.decide(TC, NEG(HALF), x), Bool.and(Membership.decide(TC, y, HALF), Membership.decide(TC, NEG(HALF), y))), outside)))

def Membership.when_local(TPL, +x: F, +y: F, -Goal: Type,
  yes: G.Geometry.Local<F, field, x, y> -> Goal, no: Membership.Missing(TC, x, y) -> Goal) -> Goal:
  Membership.local_split(TC, x, y, Goal, yes, no, B.Bits.split(Membership.within(TC, x, y)))

def Membership.cases_missing(TPL, +x: F, +y: F, -Goal: Type, missing: Membership.Missing(TC, x, y),
  x_high: O.FieldOrder.Strict(TC, HALF, x) -> Goal, x_low: O.FieldOrder.Strict(TC, x, NEG(HALF)) -> Goal,
  y_high: O.FieldOrder.Strict(TC, HALF, y) -> Goal, y_low: O.FieldOrder.Strict(TC, y, NEG(HALF)) -> Goal) -> Goal:
  match missing:
    case Inl{first}:
      x_high(first)
    case Inr{rest}:
      match rest:
        case Inl{second}:
          x_low(second)
        case Inr{last}:
          match last:
            case Inl{third}:
              y_high(third)
            case Inr{fourth}:
              y_low(fourth)

def Membership.outside(TPL, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  +outside: B.Bits.Holds(Bool.not(Membership.inside(TC, square, point))),
  x_high: O.FieldOrder.Strict(TC, HALF, G.Geometry.local_x(TC, square, point)) -> Goal,
  x_low: O.FieldOrder.Strict(TC, G.Geometry.local_x(TC, square, point), NEG(HALF)) -> Goal,
  y_high: O.FieldOrder.Strict(TC, HALF, G.Geometry.local_y(TC, square, point)) -> Goal,
  y_low: O.FieldOrder.Strict(TC, G.Geometry.local_y(TC, square, point), NEG(HALF)) -> Goal) -> Goal:
  Membership.cases_missing(TC, G.Geometry.local_x(TC, square, point), G.Geometry.local_y(TC, square, point), Goal,
    Membership.missing(TC, square, point, outside), x_high, x_low, y_high, y_low)

def Membership.cases_of(TPL, +a: F, +b: F, -Goal: Type, order: Or(LE(a, b), LE(a, b) -> Empty),
  yes: LE(a, b) -> Goal, no: O.FieldOrder.IsRight(TC, a, b, order) -> Goal) -> Goal:
  match order:
    case Inl{below}:
      yes(below)
    case Inr{above}:
      no(Unit{})

def Membership.bind(-A: Type, -Goal: Type, value: A, body: A -> Goal) -> Goal:
  body(value)

def Membership.either(-A: Type, -B: Type, -Goal: Type, choice: Or(A, B), left: A -> Goal, right: B -> Goal) -> Goal:
  match choice:
    case Inl{a}:
      left(a)
    case Inr{b}:
      right(b)

def Membership.gap(TPL, +u: F, +v: F, +strict: O.FieldOrder.Strict(TC, u, v)) -> LE(ZERO, ADD(v, NEG(u))):
  S.Scaling.fact(TC, u, v, O.FieldOrder.le_of_lt(TC, u, v, O.FieldOrder.lt_of(TC, u, v, strict)))

def Membership.by_cases(TPL, +a: F, +b: F, -Goal: Type, yes: LE(a, b) -> Goal, no: O.FieldOrder.Strict(TC, b, a) -> Goal) -> Goal:
  Membership.cases_of(TC, a, b, Goal, AX.le_decidable(a, b), yes, no)
'''

CORNERS = '''
def Membership.corner(TPL, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F) -> P.Problem.Point<F>:
  +cx: F = P.Problem.center_x(F, field, square)
  +cy: F = P.Problem.center_y(F, field, square)
  +c: F = P.Problem.cosine(F, field, square)
  +s: F = P.Problem.sine(F, field, square)
  P.Point{ADD(cx, ADD(MUL(local_x, c), NEG(MUL(local_y, s)))), ADD(cy, ADD(MUL(local_x, s), MUL(local_y, c)))}

type Membership.Corners<-F: Kind(&2), -field: K.Field<F>, -square: P.Problem.Square<F, field>, -side: F> is Data:
  Corners{
    low_low: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square))))}>,
    low_high: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square))))}>,
    high_low: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square))))}>,
    high_high: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square))))}>
  }

def Membership.corner_inside(TPL, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F,
  +x_at_most: LE(local_x, HALF), +x_at_least: LE(NEG(HALF), local_x), +y_at_most: LE(local_y, HALF), +y_at_least: LE(NEG(HALF), local_y)) ->
  P.Problem.Containment<F, field, square, Membership.corner(TC, square, local_x, local_y)>:
  match square:
    case P.Square{+center, +frame}:
      match center frame:
        case P.Point{+cx, +cy} P.Frame{+c, +s, +unit_below, +unit_above}:
          +x: F = ADD(cx, ADD(MUL(local_x, c), NEG(MUL(local_y, s))))
          +y: F = ADD(cy, ADD(MUL(local_x, s), MUL(local_y, c)))
          P.Containment{local_x, local_y, x_at_most, x_at_least, y_at_most, y_at_least,
            AX.le_reflexive(x), AX.le_reflexive(x), AX.le_reflexive(y), AX.le_reflexive(y)}

def Membership.half_at_least(TPL) -> LE(NEG(HALF), HALF):
  S.Scaling.negative_half_at_most(TC, S.Scaling.half_nonnegative(TC))
'''


def fits_certificates():
    ctx = Context()
    cx, cy, c, s = (ctx.var(n, n) for n in ('cx', 'cy', 'c', 's'))
    lx, ly, x, y, side = (ctx.var(n, n) for n in ('lx', 'ly', 'x', 'y', 'side'))
    h = ctx.var('h', 'HALF')
    ctx.raw_equation('h + h - 1', 'S.Scaling.half_equation(TC)')
    ctx.equal(x, cx + (lx * c - ly * s), 'S.Scaling.pair(TC, x, ADD(cx, ADD(MUL(lx, c), NEG(MUL(ly, s)))), xb, xa)')
    ctx.equal(y, cy + (lx * s + ly * c), 'S.Scaling.pair(TC, y, ADD(cy, ADD(MUL(lx, s), MUL(ly, c))), yb, ya)')
    ctx.below(lx, h, 'x_at_most')
    ctx.below(-h, lx, 'x_at_least')
    ctx.below(ly, h, 'y_at_most')
    ctx.below(-h, ly, 'y_at_least')
    corners = [('low_low', -h, -h), ('low_high', -h, h), ('high_low', h, -h), ('high_high', h, h)]
    for name, a, b in corners:
        cxk = cx + (a * c - b * s)
        cyk = cy + (a * s + b * c)
        ctx.nonnegative(cxk, f'{name}_left')
        ctx.below(cxk, side, f'{name}_right')
        ctx.nonnegative(cyk, f'{name}_bottom')
        ctx.below(cyk, side, f'{name}_top')
    groups = {'left': [4 * k + 4 for k in range(4)], 'right': [4 * k + 5 for k in range(4)],
              'bottom': [4 * k + 6 for k in range(4)], 'top': [4 * k + 7 for k in range(4)]}
    local = [0, 1, 2, 3]
    return (ctx.le(0, x, products=3, using=local + groups['left']), ctx.le(x, side, products=3, using=local + groups['right']),
            ctx.le(0, y, products=3, using=local + groups['bottom']), ctx.le(y, side, products=3, using=local + groups['top']))


def fits_part():
    left, right, bottom, top = fits_certificates()
    patterns = ' '.join(f'Corners{{P.InContainer{{+{n}_left, +{n}_right, +{n}_bottom, +{n}_top}}' if False else ''
                        for n in [])
    corner_patterns = ', '.join(f'P.InContainer{{+{n}_left, +{n}_right, +{n}_bottom, +{n}_top}}'
                                for n in ('low_low', 'low_high', 'high_low', 'high_high'))
    return f'''
def Membership.fits_at(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>,
  +point: P.Problem.Point<F>, +inside: P.Problem.Containment<F, field, square, point>) -> P.Problem.InContainer<F, field, side, point>:
  match square corners point inside:
    case P.Square{{P.Point{{+cx, +cy}}, P.Frame{{+c, +s, +unit_below, +unit_above}}}} Corners{{{corner_patterns}}}
      P.Point{{+x, +y}} P.Containment{{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +xb, +xa, +yb, +ya}}:
      +x_low: LE(ZERO, x) = {left}
      +x_high: LE(x, side) = {right}
      +y_low: LE(ZERO, y) = {bottom}
      +y_high: LE(y, side) = {top}
      P.InContainer{{x_low, x_high, y_low, y_high}}

def Membership.fits(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Y.Symmetry.Fits(TC, square, side):
  +point => inside => Membership.fits_at(TC, square, side, corners, point, inside)

def Membership.corners_of(TPL, +square: P.Problem.Square<F, field>, +side: F, first: Y.Symmetry.Fits(TC, square, side),
  second: Y.Symmetry.Fits(TC, square, side), third: Y.Symmetry.Fits(TC, square, side), fourth: Y.Symmetry.Fits(TC, square, side)) ->
  Membership.Corners<F, field, square, side>:
  Corners{{
    first(Membership.corner(TC, square, NEG(HALF), NEG(HALF)), Membership.corner_inside(TC, square, NEG(HALF), NEG(HALF),
      Membership.half_at_least(TC), AX.le_reflexive(NEG(HALF)), Membership.half_at_least(TC), AX.le_reflexive(NEG(HALF)))),
    second(Membership.corner(TC, square, NEG(HALF), HALF), Membership.corner_inside(TC, square, NEG(HALF), HALF,
      Membership.half_at_least(TC), AX.le_reflexive(NEG(HALF)), AX.le_reflexive(HALF), Membership.half_at_least(TC))),
    third(Membership.corner(TC, square, HALF, NEG(HALF)), Membership.corner_inside(TC, square, HALF, NEG(HALF),
      AX.le_reflexive(HALF), Membership.half_at_least(TC), Membership.half_at_least(TC), AX.le_reflexive(NEG(HALF)))),
    fourth(Membership.corner(TC, square, HALF, HALF), Membership.corner_inside(TC, square, HALF, HALF,
      AX.le_reflexive(HALF), Membership.half_at_least(TC), AX.le_reflexive(HALF), Membership.half_at_least(TC)))}}
'''


def strict_product():
    """The product of two positive elements is positive."""
    ctx = Context()
    a, b, i = ctx.var('a', 'a'), ctx.var('b', 'b'), ctx.var('i', 'INV(a)')
    ctx.equal(a * i, num(1), 'AL.same_transitive(TC, MUL(a, INV(a)), ONE, R.FieldRing.of_nat(TC, 1n), '
              'AL.mul_inverse(TC, a, O.FieldOrder.lt_of(TC, ZERO, a, first)), S.Scaling.one_is_number(TC))')
    ctx.nonnegative(a, 'O.FieldOrder.le_of_lt(TC, ZERO, a, O.FieldOrder.lt_of(TC, ZERO, a, first))')
    inverse = ctx.le(num(0), i, squares=[i])
    ctx.nonnegative(i, 'inverse_nonnegative')
    ctx.below(a * b, num(0), 'not_positive')
    proof = ctx.le(b, num(0))
    return f'''
def Membership.strict_product(TPL, +a: F, +b: F, +first: O.FieldOrder.Strict(TC, ZERO, a), +second: O.FieldOrder.Strict(TC, ZERO, b)) ->
  O.FieldOrder.Strict(TC, ZERO, MUL(a, b)):
  +inverse_nonnegative: LE(ZERO, INV(a)) = {inverse}
  O.FieldOrder.strict_of(TC, ZERO, MUL(a, b), +not_positive => O.FieldOrder.lt_of(TC, ZERO, b, second)({proof}))
'''


MOVES = '''
def Membership.moved(TPL, +square: P.Problem.Square<F, field>, +first: P.Problem.Point<F>, +second: P.Problem.Point<F>,
  +x_below: LE(P.Problem.x(F, first), P.Problem.x(F, second)), +x_above: LE(P.Problem.x(F, second), P.Problem.x(F, first)),
  +y_below: LE(P.Problem.y(F, first), P.Problem.y(F, second)), +y_above: LE(P.Problem.y(F, second), P.Problem.y(F, first)),
  +inside: P.Problem.Containment<F, field, square, first>) -> P.Problem.Containment<F, field, square, second>:
  match inside:
    case P.Containment{+lx, +ly, +a, +b, +c, +d, +xb, +xa, +yb, +ya}:
      +x: F = ADD(P.Problem.center_x(F, field, square), ADD(MUL(lx, P.Problem.cosine(F, field, square)), NEG(MUL(ly, P.Problem.sine(F, field, square)))))
      +y: F = ADD(P.Problem.center_y(F, field, square), ADD(MUL(lx, P.Problem.sine(F, field, square)), MUL(ly, P.Problem.cosine(F, field, square))))
      P.Containment{lx, ly, a, b, c, d,
        AX.le_transitive(P.Problem.x(F, second), P.Problem.x(F, first), x, x_above, xb),
        AX.le_transitive(x, P.Problem.x(F, first), P.Problem.x(F, second), xa, x_below),
        AX.le_transitive(P.Problem.y(F, second), P.Problem.y(F, first), y, y_above, yb),
        AX.le_transitive(y, P.Problem.y(F, first), P.Problem.y(F, second), ya, y_below)}

def Membership.outside_split(TPL, +first: P.Problem.Square<F, field>, +p: P.Problem.Point<F>, +second: P.Problem.Square<F, field>, +q: P.Problem.Point<F>,
  back: P.Problem.Containment<F, field, second, q> -> P.Problem.Containment<F, field, first, p>,
  +out: B.Bits.Holds(Bool.not(Membership.inside(TC, first, p))),
  split: Or(B.Bits.Holds(Membership.inside(TC, second, q)), B.Bits.Holds(Bool.not(Membership.inside(TC, second, q))))) ->
  B.Bits.Holds(Bool.not(Membership.inside(TC, second, q))):
  match split:
    case Inl{inside}:
      Empty.absurd(B.Bits.Holds(Bool.not(Membership.inside(TC, second, q))), B.Bits.never(Membership.inside(TC, first, p),
        Membership.inside_of(TC, first, p, back(Membership.contains(TC, second, q, inside))), out))
    case Inr{outside}:
      outside

def Membership.outside_of(TPL, +first: P.Problem.Square<F, field>, +p: P.Problem.Point<F>, +second: P.Problem.Square<F, field>, +q: P.Problem.Point<F>,
  back: P.Problem.Containment<F, field, second, q> -> P.Problem.Containment<F, field, first, p>,
  +out: B.Bits.Holds(Bool.not(Membership.inside(TC, first, p)))) -> B.Bits.Holds(Bool.not(Membership.inside(TC, second, q))):
  Membership.outside_split(TC, first, p, second, q, back, out, B.Bits.split(Membership.inside(TC, second, q)))
'''

TRANSPORTS = '''
def Membership.swap_corners(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.swap(TC, square), side>:
  Membership.corners_of(TC, Y.Symmetry.swap(TC, square), side, Y.Symmetry.swap_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.swap_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.swap_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.swap_fits(TC, square, side, Membership.fits(TC, square, side, corners)))

def Membership.reflect_x_corners(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.reflect_x(TC, side, square), side>:
  Membership.corners_of(TC, Y.Symmetry.reflect_x(TC, side, square), side,
    Y.Symmetry.reflect_x_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_x_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_x_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_x_fits(TC, square, side, Membership.fits(TC, square, side, corners)))

def Membership.reflect_y_corners(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.reflect_y(TC, side, square), side>:
  Membership.corners_of(TC, Y.Symmetry.reflect_y(TC, side, square), side,
    Y.Symmetry.reflect_y_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_y_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_y_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.reflect_y_fits(TC, square, side, Membership.fits(TC, square, side, corners)))

def Membership.first_quadrant_corners(TPL, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.first_quadrant(TC, square), side>:
  Membership.corners_of(TC, Y.Symmetry.first_quadrant(TC, square), side,
    Y.Symmetry.first_quadrant_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.first_quadrant_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.first_quadrant_fits(TC, square, side, Membership.fits(TC, square, side, corners)), Y.Symmetry.first_quadrant_fits(TC, square, side, Membership.fits(TC, square, side, corners)))
'''

(ROOT / 'bend' / 'Membership.bend').write_text(expand(HEADER + DECISIONS + ELIMINATORS + CORNERS + fits_part() + MOVES + TRANSPORTS + strict_product()))
