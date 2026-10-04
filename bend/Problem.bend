import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/Natural.bend as N

type Problem.Point<-F: Kind(&2)> is Data:
  Point{x: F, y: F}

type Problem.Frame<-F: Kind(&2), -field: K.Field<F>> is Data:
  Frame{
    cosine: F,
    sine: F,
    unit_below: K.Field.le(F, field)(K.Field.add(F, field)(K.Field.mul(F, field)(cosine, cosine), K.Field.mul(F, field)(sine, sine)), K.Field.one(F, field)),
    unit_above: K.Field.le(F, field)(K.Field.one(F, field), K.Field.add(F, field)(K.Field.mul(F, field)(cosine, cosine), K.Field.mul(F, field)(sine, sine)))
  }

type Problem.Square<-F: Kind(&2), -field: K.Field<F>> is Data:
  Square{center: Problem.Point<F>, frame: Problem.Frame<F, field>}

def Problem.x(-F: Kind(&2), point: Problem.Point<F>) -> F:
  match point:
    case Point{x, y}:
      x

def Problem.y(-F: Kind(&2), point: Problem.Point<F>) -> F:
  match point:
    case Point{x, y}:
      y

def Problem.cosine(-F: Kind(&2), -field: K.Field<F>, square: Problem.Square<F, field>) -> F:
  match square:
    case Square{center, frame}:
      match frame:
        case Frame{cosine, sine, unit_below, unit_above}:
          cosine

def Problem.sine(-F: Kind(&2), -field: K.Field<F>, square: Problem.Square<F, field>) -> F:
  match square:
    case Square{center, frame}:
      match frame:
        case Frame{cosine, sine, unit_below, unit_above}:
          sine

def Problem.center_x(-F: Kind(&2), -field: K.Field<F>, square: Problem.Square<F, field>) -> F:
  match square:
    case Square{center, frame}:
      Problem.x(F, center)

def Problem.center_y(-F: Kind(&2), -field: K.Field<F>, square: Problem.Square<F, field>) -> F:
  match square:
    case Square{center, frame}:
      Problem.y(F, center)

type Problem.Containment<-F: Kind(&2), -field: K.Field<F>, -square: Problem.Square<F, field>, -point: Problem.Point<F>> is Data:
  Containment{
    local_x: F,
    local_y: F,
    x_at_most: K.Field.le(F, field)(local_x, K.Field.half(F, field)),
    x_at_least: K.Field.le(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), local_x),
    y_at_most: K.Field.le(F, field)(local_y, K.Field.half(F, field)),
    y_at_least: K.Field.le(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), local_y),
    x_is_below: K.Field.le(F, field)(Problem.x(F, point), K.Field.add(F, field)(Problem.center_x(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(local_y, Problem.sine(F, field, square)))))),
    x_is_above: K.Field.le(F, field)(K.Field.add(F, field)(Problem.center_x(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(local_y, Problem.sine(F, field, square))))), Problem.x(F, point)),
    y_is_below: K.Field.le(F, field)(Problem.y(F, point), K.Field.add(F, field)(Problem.center_y(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.sine(F, field, square)), K.Field.mul(F, field)(local_y, Problem.cosine(F, field, square))))),
    y_is_above: K.Field.le(F, field)(K.Field.add(F, field)(Problem.center_y(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.sine(F, field, square)), K.Field.mul(F, field)(local_y, Problem.cosine(F, field, square)))), Problem.y(F, point))
  }

type Problem.InteriorContainment<-F: Kind(&2), -field: K.Field<F>, -square: Problem.Square<F, field>, -point: Problem.Point<F>> is Type:
  InteriorContainment{
    local_x: F,
    local_y: F,
    x_below: K.Field.le(F, field)(K.Field.half(F, field), local_x) -> Empty,
    x_above: K.Field.le(F, field)(local_x, K.Field.neg(F, field)(K.Field.half(F, field))) -> Empty,
    y_below: K.Field.le(F, field)(K.Field.half(F, field), local_y) -> Empty,
    y_above: K.Field.le(F, field)(local_y, K.Field.neg(F, field)(K.Field.half(F, field))) -> Empty,
    x_is_below: K.Field.le(F, field)(Problem.x(F, point), K.Field.add(F, field)(Problem.center_x(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(local_y, Problem.sine(F, field, square)))))),
    x_is_above: K.Field.le(F, field)(K.Field.add(F, field)(Problem.center_x(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.cosine(F, field, square)), K.Field.neg(F, field)(K.Field.mul(F, field)(local_y, Problem.sine(F, field, square))))), Problem.x(F, point)),
    y_is_below: K.Field.le(F, field)(Problem.y(F, point), K.Field.add(F, field)(Problem.center_y(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.sine(F, field, square)), K.Field.mul(F, field)(local_y, Problem.cosine(F, field, square))))),
    y_is_above: K.Field.le(F, field)(K.Field.add(F, field)(Problem.center_y(F, field, square),
      K.Field.add(F, field)(K.Field.mul(F, field)(local_x, Problem.sine(F, field, square)), K.Field.mul(F, field)(local_y, Problem.cosine(F, field, square)))), Problem.y(F, point))
  }

type Problem.InContainer<-F: Kind(&2), -field: K.Field<F>, -side: F, -point: Problem.Point<F>> is Data:
  InContainer{
    left: K.Field.le(F, field)(K.Field.zero(F, field), Problem.x(F, point)),
    right: K.Field.le(F, field)(Problem.x(F, point), side),
    bottom: K.Field.le(F, field)(K.Field.zero(F, field), Problem.y(F, point)),
    top: K.Field.le(F, field)(Problem.y(F, point), side)
  }

type Problem.Packing<-F: Kind(&2), -field: K.Field<F>, -count: Nat, -side: F> is Type:
  Packing{
    squares: Nat -> Problem.Square<F, field>,
    side_nonnegative: K.Field.le(F, field)(K.Field.zero(F, field), side),
    fits: @index: Nat -> N.Natural.Le(1n+index, count) -> @point: Problem.Point<F> ->
      Problem.Containment<F, field, squares(index), point> -> Problem.InContainer<F, field, side, point>,
    disjoint: @left: Nat -> @right: Nat -> N.Natural.Le(1n+left, count) -> N.Natural.Le(1n+right, count) ->
      ({left == right : Nat} -> Empty) -> @point: Problem.Point<F> ->
      Problem.InteriorContainment<F, field, squares(left), point> -> Problem.InteriorContainment<F, field, squares(right), point> -> Empty
  }
