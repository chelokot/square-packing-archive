import Base
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

def Membership.decision(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, a, b) -> Empty)) -> Bool:
  match order:
    case Inl{below}:
      True{}
    case Inr{above}:
      False{}

def Membership.decide(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Bool:
  Membership.decision(~F, ~field, a, b, K.Field.le_decidable(F, field)(a, b))

def Membership.below_of(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, a, b) -> Empty),
  holds: B.Bits.Holds(Membership.decision(~F, ~field, a, b, order))) -> A.Algebra.le(~F, ~field, a, b):
  match order:
    case Inl{below}:
      below
    case Inr{above}:
      match holds:

def Membership.below(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, holds: B.Bits.Holds(Membership.decide(~F, ~field, a, b))) -> A.Algebra.le(~F, ~field, a, b):
  Membership.below_of(~F, ~field, a, b, K.Field.le_decidable(F, field)(a, b), holds)

def Membership.decided_of(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, a, b) -> Empty), below: A.Algebra.le(~F, ~field, a, b)) ->
  B.Bits.Holds(Membership.decision(~F, ~field, a, b, order)):
  match order:
    case Inl{yes}:
      Unit{}
    case Inr{no}:
      no(below)

def Membership.decided(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, a, b)) -> B.Bits.Holds(Membership.decide(~F, ~field, a, b)):
  Membership.decided_of(~F, ~field, a, b, K.Field.le_decidable(F, field)(a, b), below)

def Membership.above_of(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, a, b) -> Empty),
  holds: B.Bits.Holds(Bool.not(Membership.decision(~F, ~field, a, b, order)))) -> O.FieldOrder.IsRight(~F, ~field, a, b, order):
  match order:
    case Inl{below}:
      match holds:
    case Inr{above}:
      Unit{}

def Membership.above(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, holds: B.Bits.Holds(Bool.not(Membership.decide(~F, ~field, a, b)))) -> O.FieldOrder.Strict(~F, ~field, b, a):
  Membership.above_of(~F, ~field, a, b, K.Field.le_decidable(F, field)(a, b), holds)

def Membership.within(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F) -> Bool:
  Bool.and(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)), Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x),
    Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))))

def Membership.inside(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>) -> Bool:
  Membership.within(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point))

def Membership.local_of(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, +holds: B.Bits.Holds(Membership.within(~F, ~field, x, y))) -> G.Geometry.Local<F, field, x, y>:
  +first: Bool = Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field))
  +second: Bool = Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x)
  +third: Bool = Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field))
  +fourth: Bool = Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y)
  +rest: Bool = Bool.and(second, Bool.and(third, fourth))
  +last: Bool = Bool.and(third, fourth)
  G.Local{
    Membership.below(~F, ~field, x, A.Algebra.half(~F, ~field), B.Bits.left(first, rest, holds)),
    Membership.below(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x, B.Bits.left(second, last, B.Bits.right(first, rest, holds))),
    Membership.below(~F, ~field, y, A.Algebra.half(~F, ~field), B.Bits.left(third, fourth, B.Bits.right(second, last, B.Bits.right(first, rest, holds)))),
    Membership.below(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y, B.Bits.right(third, fourth, B.Bits.right(second, last, B.Bits.right(first, rest, holds))))}

def Membership.contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +holds: B.Bits.Holds(Membership.inside(~F, ~field, square, point))) -> P.Problem.Containment<F, field, square, point>:
  G.Geometry.local_contains(~F, ~field, square, point,
    Membership.local_of(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point), holds))

def Membership.inside_local(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, local: G.Geometry.Local<F, field, x, y>) ->
  B.Bits.Holds(Bool.and(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)), Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x),
    Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))))):
  match local:
    case G.Local{+first, +second, +third, +fourth}:
      B.Bits.both(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)), Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x),
          Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))),
        Membership.decided(~F, ~field, x, A.Algebra.half(~F, ~field), first),
        B.Bits.both(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x), Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y)),
          Membership.decided(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x, second),
          B.Bits.both(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y),
            Membership.decided(~F, ~field, y, A.Algebra.half(~F, ~field), third), Membership.decided(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y, fourth))))

def Membership.inside_of(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +containment: P.Problem.Containment<F, field, square, point>) -> B.Bits.Holds(Membership.inside(~F, ~field, square, point)):
  Membership.inside_local(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point),
    G.Geometry.contains_local(~F, ~field, square, point, containment))

def Membership.Missing(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F) -> Type:
  Or(O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), x), Or(O.FieldOrder.Strict(~F, ~field, x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))),
    Or(O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), y), O.FieldOrder.Strict(~F, ~field, y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))))))

def Membership.missing_last(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)))), B.Bits.Holds(Bool.not(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))))) ->
  Or(O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), y), O.FieldOrder.Strict(~F, ~field, y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)))):
  match split:
    case Inl{no}:
      Inl{Membership.above(~F, ~field, y, A.Algebra.half(~F, ~field), no)}
    case Inr{no}:
      Inr{Membership.above(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y, no)}

def Membership.missing_rest(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x))),
    B.Bits.Holds(Bool.not(Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y)))))) ->
  Or(O.FieldOrder.Strict(~F, ~field, x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), Or(O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), y), O.FieldOrder.Strict(~F, ~field, y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))))):
  match split:
    case Inl{no}:
      Inl{Membership.above(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x, no)}
    case Inr{no}:
      Inr{Membership.missing_last(~F, ~field, x, y, B.Bits.not_both(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y), no))}

def Membership.missing_from(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F,
  split: Or(B.Bits.Holds(Bool.not(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)))),
    B.Bits.Holds(Bool.not(Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x), Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))))))) ->
  Membership.Missing(~F, ~field, x, y):
  match split:
    case Inl{no}:
      Inl{Membership.above(~F, ~field, x, A.Algebra.half(~F, ~field), no)}
    case Inr{no}:
      Inr{Membership.missing_rest(~F, ~field, x, y, B.Bits.not_both(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x),
        Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y)), no))}

def Membership.missing(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  +outside: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, square, point)))) ->
  Membership.Missing(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point)):
  +x: F = G.Geometry.local_x(~F, ~field, square, point)
  +y: F = G.Geometry.local_y(~F, ~field, square, point)
  Membership.missing_from(~F, ~field, x, y, B.Bits.not_both(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)),
    Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x), Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))), outside))

def Membership.when_split(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  yes: P.Problem.Containment<F, field, square, point> -> Goal, no: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, square, point))) -> Goal,
  split: Or(B.Bits.Holds(Membership.inside(~F, ~field, square, point)), B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, square, point))))) -> Goal:
  match split:
    case Inl{inside}:
      yes(Membership.contains(~F, ~field, square, point, inside))
    case Inr{outside}:
      no(outside)

def Membership.when(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  yes: P.Problem.Containment<F, field, square, point> -> Goal, no: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, square, point))) -> Goal) -> Goal:
  Membership.when_split(~F, ~field, square, point, Goal, yes, no, B.Bits.split(Membership.inside(~F, ~field, square, point)))

def Membership.local_split(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, -Goal: Type,
  yes: G.Geometry.Local<F, field, x, y> -> Goal, no: Membership.Missing(~F, ~field, x, y) -> Goal,
  split: Or(B.Bits.Holds(Membership.within(~F, ~field, x, y)), B.Bits.Holds(Bool.not(Membership.within(~F, ~field, x, y))))) -> Goal:
  match split:
    case Inl{inside}:
      yes(Membership.local_of(~F, ~field, x, y, inside))
    case Inr{outside}:
      no(Membership.missing_from(~F, ~field, x, y, B.Bits.not_both(Membership.decide(~F, ~field, x, A.Algebra.half(~F, ~field)),
        Bool.and(Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x), Bool.and(Membership.decide(~F, ~field, y, A.Algebra.half(~F, ~field)), Membership.decide(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y))), outside)))

def Membership.when_local(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, -Goal: Type,
  yes: G.Geometry.Local<F, field, x, y> -> Goal, no: Membership.Missing(~F, ~field, x, y) -> Goal) -> Goal:
  Membership.local_split(~F, ~field, x, y, Goal, yes, no, B.Bits.split(Membership.within(~F, ~field, x, y)))

def Membership.cases_missing(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, -Goal: Type, missing: Membership.Missing(~F, ~field, x, y),
  x_high: O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), x) -> Goal, x_low: O.FieldOrder.Strict(~F, ~field, x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Goal,
  y_high: O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), y) -> Goal, y_low: O.FieldOrder.Strict(~F, ~field, y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Goal) -> Goal:
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

def Membership.outside(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, -Goal: Type,
  +outside: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, square, point))),
  x_high: O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), G.Geometry.local_x(~F, ~field, square, point)) -> Goal,
  x_low: O.FieldOrder.Strict(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Goal,
  y_high: O.FieldOrder.Strict(~F, ~field, A.Algebra.half(~F, ~field), G.Geometry.local_y(~F, ~field, square, point)) -> Goal,
  y_low: O.FieldOrder.Strict(~F, ~field, G.Geometry.local_y(~F, ~field, square, point), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Goal) -> Goal:
  Membership.cases_missing(~F, ~field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point), Goal,
    Membership.missing(~F, ~field, square, point, outside), x_high, x_low, y_high, y_low)

def Membership.cases_of(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, -Goal: Type, order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, a, b) -> Empty),
  yes: A.Algebra.le(~F, ~field, a, b) -> Goal, no: O.FieldOrder.IsRight(~F, ~field, a, b, order) -> Goal) -> Goal:
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

def Membership.gap(~F: Kind(&2), ~field: K.Field<F>, +u: F, +v: F, +strict: O.FieldOrder.Strict(~F, ~field, u, v)) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, v, A.Algebra.neg(~F, ~field, u))):
  S.Scaling.fact(~F, ~field, u, v, O.FieldOrder.le_of_lt(~F, ~field, u, v, O.FieldOrder.lt_of(~F, ~field, u, v, strict)))

def Membership.by_cases(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, -Goal: Type, yes: A.Algebra.le(~F, ~field, a, b) -> Goal, no: O.FieldOrder.Strict(~F, ~field, b, a) -> Goal) -> Goal:
  Membership.cases_of(~F, ~field, a, b, Goal, K.Field.le_decidable(F, field)(a, b), yes, no)

def Membership.corner(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F) -> P.Problem.Point<F>:
  +cx: F = P.Problem.center_x(F, field, square)
  +cy: F = P.Problem.center_y(F, field, square)
  +c: F = P.Problem.cosine(F, field, square)
  +s: F = P.Problem.sine(F, field, square)
  P.Point{A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, s)))), A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, s), A.Algebra.mul(~F, ~field, local_y, c)))}

type Membership.Corners<-F: Kind(&2), -field: K.Field<F>, -square: P.Problem.Square<F, field>, -side: F> is Data:
  Corners{
    low_low: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square))))}>,
    low_high: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square))))}>,
    high_low: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), P.Problem.cosine(F, field, square))))}>,
    high_high: P.Problem.InContainer<F, field, side, P.Point{K.Field.add(F, field)(P.Problem.center_x(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square))))), K.Field.add(F, field)(P.Problem.center_y(F, field, square), K.Field.add(F, field)(K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.sine(F, field, square)), K.Field.mul(F, field)(K.Field.half(F, field), P.Problem.cosine(F, field, square))))}>
  }

def Membership.corner_inside(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F,
  +x_at_most: A.Algebra.le(~F, ~field, local_x, A.Algebra.half(~F, ~field)), +x_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x), +y_at_most: A.Algebra.le(~F, ~field, local_y, A.Algebra.half(~F, ~field)), +y_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y)) ->
  P.Problem.Containment<F, field, square, Membership.corner(~F, ~field, square, local_x, local_y)>:
  match square:
    case P.Square{+center, +frame}:
      match center frame:
        case P.Point{+cx, +cy} P.Frame{+c, +s, +unit_below, +unit_above}:
          +x: F = A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, s))))
          +y: F = A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, s), A.Algebra.mul(~F, ~field, local_y, c)))
          P.Containment{local_x, local_y, x_at_most, x_at_least, y_at_most, y_at_least,
            K.Field.le_reflexive(F, field)(x), K.Field.le_reflexive(F, field)(x), K.Field.le_reflexive(F, field)(y), K.Field.le_reflexive(F, field)(y)}

def Membership.half_at_least(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.half(~F, ~field)):
  S.Scaling.negative_half_at_most(~F, ~field, S.Scaling.half_nonnegative(~F, ~field))

def Membership.fits_at(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>,
  +point: P.Problem.Point<F>, +inside: P.Problem.Containment<F, field, square, point>) -> P.Problem.InContainer<F, field, side, point>:
  match square corners point inside:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}} Corners{P.InContainer{+low_low_left, +low_low_right, +low_low_bottom, +low_low_top}, P.InContainer{+low_high_left, +low_high_right, +low_high_bottom, +low_high_top}, P.InContainer{+high_low_left, +high_low_right, +high_low_bottom, +high_low_top}, P.InContainer{+high_high_left, +high_high_right, +high_high_bottom, +high_high_top}}
      P.Point{+x, +y} P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +xb, +xa, +yb, +ya}:
      +x_low: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), x) = C.Certificate.le(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{side, R.Value{A.Algebra.half(~F, ~field), R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{4n}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{5n}}}, C.MoreExprs{R.Plus{R.Variable{5n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{9n}, R.Variable{3n}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{9n}, R.Variable{3n}}}}}, C.NoExprs{}}}}}}}}}, C.Both{S.Scaling.fact(~F, ~field, lx, A.Algebra.half(~F, ~field), x_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx, x_at_least), C.Both{S.Scaling.fact(~F, ~field, ly, A.Algebra.half(~F, ~field), y_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly, y_at_least), C.Both{low_low_left, C.Both{low_high_left, C.Both{high_low_left, C.Both{high_high_left, Unit{}}}}}}}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{9n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.NoExprs{}}}}, C.Both{S.Scaling.half_equation(~F, ~field), C.Both{S.Scaling.equation(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), S.Scaling.pair(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), xb, xa)), C.Both{S.Scaling.equation(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), S.Scaling.pair(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), yb, ya)), Unit{}}}}, R.Number{0n}, R.Variable{6n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{2n, C.MoreIndices{4n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{3n, C.MoreIndices{5n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{2n, C.MoreIndices{6n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{3n, C.MoreIndices{7n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{5n}}, R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{3n}}, R.Variable{5n}}, R.Variable{9n}}}, R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{4n}}}}, R.Negate{R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{2n}}, R.Variable{4n}}, R.Variable{9n}}}}, R.Negate{R.Multiply{R.Number{1n}, R.Variable{0n}}}}, R.Negate{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{0n}}, R.Variable{9n}}}}}, C.MoreTerms{C.Multiple{1n, R.Number{1n}}, C.NoTerms{}}}}}}}, {==})
      +x_high: A.Algebra.le(~F, ~field, x, side) = C.Certificate.le(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{side, R.Value{A.Algebra.half(~F, ~field), R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{4n}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{5n}}}, C.MoreExprs{R.Plus{R.Variable{5n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{9n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{9n}, R.Variable{3n}}}}}}}, C.NoExprs{}}}}}}}}}, C.Both{S.Scaling.fact(~F, ~field, lx, A.Algebra.half(~F, ~field), x_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx, x_at_least), C.Both{S.Scaling.fact(~F, ~field, ly, A.Algebra.half(~F, ~field), y_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly, y_at_least), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s)))), side, low_low_right), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s)))), side, low_high_right), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s)))), side, high_low_right), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s)))), side, high_high_right), Unit{}}}}}}}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{9n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.NoExprs{}}}}, C.Both{S.Scaling.half_equation(~F, ~field), C.Both{S.Scaling.equation(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), S.Scaling.pair(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), xb, xa)), C.Both{S.Scaling.equation(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), S.Scaling.pair(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), yb, ya)), Unit{}}}}, R.Variable{6n}, R.Variable{8n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{2n, C.MoreIndices{4n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{3n, C.MoreIndices{5n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{2n, C.MoreIndices{6n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{3n, C.MoreIndices{7n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Negate{R.Multiply{R.Number{1n}, R.Variable{8n}}}, R.Negate{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{8n}}, R.Variable{9n}}}}, R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{5n}}}}, R.Negate{R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{3n}}, R.Variable{5n}}, R.Variable{9n}}}}, R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{4n}}}, R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{2n}}, R.Variable{4n}}, R.Variable{9n}}}, R.Multiply{R.Number{1n}, R.Variable{0n}}}, R.Multiply{R.Multiply{R.Number{2n}, R.Variable{0n}}, R.Variable{9n}}}}, C.MoreTerms{C.Multiple{1n, R.Negate{R.Number{1n}}}, C.NoTerms{}}}}}}}, {==})
      +y_low: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), y) = C.Certificate.le(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{side, R.Value{A.Algebra.half(~F, ~field), R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{4n}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{5n}}}, C.MoreExprs{R.Plus{R.Variable{5n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Variable{9n}, R.Variable{2n}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{3n}}, R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{3n}}, R.Multiply{R.Variable{9n}, R.Variable{2n}}}}, C.NoExprs{}}}}}}}}}, C.Both{S.Scaling.fact(~F, ~field, lx, A.Algebra.half(~F, ~field), x_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx, x_at_least), C.Both{S.Scaling.fact(~F, ~field, ly, A.Algebra.half(~F, ~field), y_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly, y_at_least), C.Both{low_low_bottom, C.Both{low_high_bottom, C.Both{high_low_bottom, C.Both{high_high_bottom, Unit{}}}}}}}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{9n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.NoExprs{}}}}, C.Both{S.Scaling.half_equation(~F, ~field), C.Both{S.Scaling.equation(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), S.Scaling.pair(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), xb, xa)), C.Both{S.Scaling.equation(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), S.Scaling.pair(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), yb, ya)), Unit{}}}}, R.Number{0n}, R.Variable{7n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{2n, C.MoreIndices{4n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{3n, C.MoreIndices{5n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{2n, C.MoreIndices{6n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{3n, C.MoreIndices{7n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{4n}}}, R.Negate{R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{3n}}, R.Variable{4n}}, R.Variable{9n}}}}, R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{5n}}}}, R.Negate{R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{2n}}, R.Variable{5n}}, R.Variable{9n}}}}, R.Negate{R.Multiply{R.Number{1n}, R.Variable{1n}}}}, R.Negate{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{1n}}, R.Variable{9n}}}}}, C.MoreTerms{C.Multiple{2n, R.Number{1n}}, C.NoTerms{}}}}}}}, {==})
      +y_high: A.Algebra.le(~F, ~field, y, side) = C.Certificate.le(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{side, R.Value{A.Algebra.half(~F, ~field), R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{4n}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{9n}, R.Negate{R.Variable{5n}}}, C.MoreExprs{R.Plus{R.Variable{5n}, R.Negate{R.Negate{R.Variable{9n}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Variable{9n}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{3n}}, R.Multiply{R.Negate{R.Variable{9n}}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Variable{8n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{9n}, R.Variable{3n}}, R.Multiply{R.Variable{9n}, R.Variable{2n}}}}}}, C.NoExprs{}}}}}}}}}, C.Both{S.Scaling.fact(~F, ~field, lx, A.Algebra.half(~F, ~field), x_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx, x_at_least), C.Both{S.Scaling.fact(~F, ~field, ly, A.Algebra.half(~F, ~field), y_at_most), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly, y_at_least), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s), A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c))), side, low_low_top), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s), A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c))), side, low_high_top), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s), A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c))), side, high_low_top), C.Both{S.Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s), A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c))), side, high_high_top), Unit{}}}}}}}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{9n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.NoExprs{}}}}, C.Both{S.Scaling.half_equation(~F, ~field), C.Both{S.Scaling.equation(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), S.Scaling.pair(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), xb, xa)), C.Both{S.Scaling.equation(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), S.Scaling.pair(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), yb, ya)), Unit{}}}}, R.Variable{7n}, R.Variable{8n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{2n, C.MoreIndices{4n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{3n, C.MoreIndices{5n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{2n, C.MoreIndices{6n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{1n, C.MoreIndices{3n, C.MoreIndices{7n, C.NoIndices{}}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Plus{R.Negate{R.Multiply{R.Number{1n}, R.Variable{8n}}}, R.Negate{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{8n}}, R.Variable{9n}}}}, R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{4n}}}, R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{3n}}, R.Variable{4n}}, R.Variable{9n}}}, R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{5n}}}, R.Multiply{R.Multiply{R.Multiply{R.Number{2n}, R.Variable{2n}}, R.Variable{5n}}, R.Variable{9n}}}, R.Multiply{R.Number{1n}, R.Variable{1n}}}, R.Multiply{R.Multiply{R.Number{2n}, R.Variable{1n}}, R.Variable{9n}}}}, C.MoreTerms{C.Multiple{2n, R.Negate{R.Number{1n}}}, C.NoTerms{}}}}}}}, {==})
      P.InContainer{x_low, x_high, y_low, y_high}

def Membership.fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Y.Symmetry.Fits(~F, ~field, square, side):
  +point => inside => Membership.fits_at(~F, ~field, square, side, corners, point, inside)

def Membership.corners_of(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, first: Y.Symmetry.Fits(~F, ~field, square, side),
  second: Y.Symmetry.Fits(~F, ~field, square, side), third: Y.Symmetry.Fits(~F, ~field, square, side), fourth: Y.Symmetry.Fits(~F, ~field, square, side)) ->
  Membership.Corners<F, field, square, side>:
  Corners{
    first(Membership.corner(~F, ~field, square, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), Membership.corner_inside(~F, ~field, square, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)),
      Membership.half_at_least(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), Membership.half_at_least(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))))),
    second(Membership.corner(~F, ~field, square, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.half(~F, ~field)), Membership.corner_inside(~F, ~field, square, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.half(~F, ~field),
      Membership.half_at_least(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Membership.half_at_least(~F, ~field))),
    third(Membership.corner(~F, ~field, square, A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), Membership.corner_inside(~F, ~field, square, A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)),
      K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Membership.half_at_least(~F, ~field), Membership.half_at_least(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))))),
    fourth(Membership.corner(~F, ~field, square, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field)), Membership.corner_inside(~F, ~field, square, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field),
      K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Membership.half_at_least(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Membership.half_at_least(~F, ~field)))}

def Membership.moved(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +first: P.Problem.Point<F>, +second: P.Problem.Point<F>,
  +x_below: A.Algebra.le(~F, ~field, P.Problem.x(F, first), P.Problem.x(F, second)), +x_above: A.Algebra.le(~F, ~field, P.Problem.x(F, second), P.Problem.x(F, first)),
  +y_below: A.Algebra.le(~F, ~field, P.Problem.y(F, first), P.Problem.y(F, second)), +y_above: A.Algebra.le(~F, ~field, P.Problem.y(F, second), P.Problem.y(F, first)),
  +inside: P.Problem.Containment<F, field, square, first>) -> P.Problem.Containment<F, field, square, second>:
  match inside:
    case P.Containment{+lx, +ly, +a, +b, +c, +d, +xb, +xa, +yb, +ya}:
      +x: F = A.Algebra.add(~F, ~field, P.Problem.center_x(F, field, square), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, P.Problem.cosine(F, field, square)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, P.Problem.sine(F, field, square)))))
      +y: F = A.Algebra.add(~F, ~field, P.Problem.center_y(F, field, square), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, P.Problem.sine(F, field, square)), A.Algebra.mul(~F, ~field, ly, P.Problem.cosine(F, field, square))))
      P.Containment{lx, ly, a, b, c, d,
        K.Field.le_transitive(F, field)(P.Problem.x(F, second), P.Problem.x(F, first), x, x_above, xb),
        K.Field.le_transitive(F, field)(x, P.Problem.x(F, first), P.Problem.x(F, second), xa, x_below),
        K.Field.le_transitive(F, field)(P.Problem.y(F, second), P.Problem.y(F, first), y, y_above, yb),
        K.Field.le_transitive(F, field)(y, P.Problem.y(F, first), P.Problem.y(F, second), ya, y_below)}

def Membership.outside_split(~F: Kind(&2), ~field: K.Field<F>, +first: P.Problem.Square<F, field>, +p: P.Problem.Point<F>, +second: P.Problem.Square<F, field>, +q: P.Problem.Point<F>,
  back: P.Problem.Containment<F, field, second, q> -> P.Problem.Containment<F, field, first, p>,
  +out: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, first, p))),
  split: Or(B.Bits.Holds(Membership.inside(~F, ~field, second, q)), B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, second, q))))) ->
  B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, second, q))):
  match split:
    case Inl{inside}:
      Empty.absurd(B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, second, q))), B.Bits.never(Membership.inside(~F, ~field, first, p),
        Membership.inside_of(~F, ~field, first, p, back(Membership.contains(~F, ~field, second, q, inside))), out))
    case Inr{outside}:
      outside

def Membership.outside_of(~F: Kind(&2), ~field: K.Field<F>, +first: P.Problem.Square<F, field>, +p: P.Problem.Point<F>, +second: P.Problem.Square<F, field>, +q: P.Problem.Point<F>,
  back: P.Problem.Containment<F, field, second, q> -> P.Problem.Containment<F, field, first, p>,
  +out: B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, first, p)))) -> B.Bits.Holds(Bool.not(Membership.inside(~F, ~field, second, q))):
  Membership.outside_split(~F, ~field, first, p, second, q, back, out, B.Bits.split(Membership.inside(~F, ~field, second, q)))

def Membership.swap_corners(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.swap(~F, ~field, square), side>:
  Membership.corners_of(~F, ~field, Y.Symmetry.swap(~F, ~field, square), side, Y.Symmetry.swap_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.swap_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.swap_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.swap_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)))

def Membership.reflect_x_corners(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.reflect_x(~F, ~field, side, square), side>:
  Membership.corners_of(~F, ~field, Y.Symmetry.reflect_x(~F, ~field, side, square), side,
    Y.Symmetry.reflect_x_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_x_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_x_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_x_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)))

def Membership.reflect_y_corners(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.reflect_y(~F, ~field, side, square), side>:
  Membership.corners_of(~F, ~field, Y.Symmetry.reflect_y(~F, ~field, side, square), side,
    Y.Symmetry.reflect_y_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_y_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_y_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.reflect_y_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)))

def Membership.first_quadrant_corners(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +corners: Membership.Corners<F, field, square, side>) ->
  Membership.Corners<F, field, Y.Symmetry.first_quadrant(~F, ~field, square), side>:
  Membership.corners_of(~F, ~field, Y.Symmetry.first_quadrant(~F, ~field, square), side,
    Y.Symmetry.first_quadrant_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.first_quadrant_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.first_quadrant_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)), Y.Symmetry.first_quadrant_fits(~F, ~field, square, side, Membership.fits(~F, ~field, square, side, corners)))
