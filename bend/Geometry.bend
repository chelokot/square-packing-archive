import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/Certificate.bend as C
import ./Problem.bend as P

type Geometry.Local<-F: Kind(&2), -field: K.Field<F>, -local_x: F, -local_y: F> is Data:
  Local{
    x_at_most: K.Field.le(F, field)(local_x, K.Field.half(F, field)),
    x_at_least: K.Field.le(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), local_x),
    y_at_most: K.Field.le(F, field)(local_y, K.Field.half(F, field)),
    y_at_least: K.Field.le(F, field)(K.Field.neg(F, field)(K.Field.half(F, field)), local_y)
  }

type Geometry.StrictLocal<-F: Kind(&2), -field: K.Field<F>, -local_x: F, -local_y: F> is Type:
  StrictLocal{
    x_below: K.Field.le(F, field)(K.Field.half(F, field), local_x) -> Empty,
    x_above: K.Field.le(F, field)(local_x, K.Field.neg(F, field)(K.Field.half(F, field))) -> Empty,
    y_below: K.Field.le(F, field)(K.Field.half(F, field), local_y) -> Empty,
    y_above: K.Field.le(F, field)(local_y, K.Field.neg(F, field)(K.Field.half(F, field))) -> Empty
  }

def Geometry.local_x(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>) -> F:
  A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, P.Problem.x(F, point), A.Algebra.neg(~F, ~field, P.Problem.center_x(F, field, square))), P.Problem.cosine(F, field, square)),
    A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, P.Problem.y(F, point), A.Algebra.neg(~F, ~field, P.Problem.center_y(F, field, square))), P.Problem.sine(F, field, square)))

def Geometry.local_y(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>) -> F:
  A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.add(~F, ~field, P.Problem.x(F, point), A.Algebra.neg(~F, ~field, P.Problem.center_x(F, field, square)))), P.Problem.sine(F, field, square)),
    A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, P.Problem.y(F, point), A.Algebra.neg(~F, ~field, P.Problem.center_y(F, field, square))), P.Problem.cosine(F, field, square)))

def Geometry.zero_difference(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, a, b), above: A.Algebra.le(~F, ~field, b, a)) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.zero(~F, ~field)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)))>:
  C.Both{
    A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, b)), A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.zero(~F, ~field), K.Field.le_add(F, field)(a, b, A.Algebra.neg(~F, ~field, b), below),
      A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b))), A.Algebra.add_neg(~F, ~field, b)),
    A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, b)), A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), K.Field.le_add(F, field)(b, a, A.Algebra.neg(~F, ~field, b), above),
      A.Algebra.add_neg(~F, ~field, b), A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b))))
  }

def Geometry.unit(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F,
  unit_below: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine)), A.Algebra.one(~F, ~field)),
  unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine)))) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine)), A.Algebra.neg(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n))), A.Algebra.zero(~F, ~field)),
    A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine)), A.Algebra.neg(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n))))>:
  +norm: F = A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine))
  Geometry.zero_difference(~F, ~field, norm, R.FieldRing.of_nat(~F, ~field, 1n),
    A.Algebra.le_respects(~F, ~field, norm, A.Algebra.one(~F, ~field), norm, R.FieldRing.of_nat(~F, ~field, 1n), unit_below, A.Algebra.same_reflexive(~F, ~field, norm), A.Algebra.same_symmetric(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field), R.FieldRing.of_nat_one(~F, ~field))),
    A.Algebra.le_respects(~F, ~field, A.Algebra.one(~F, ~field), norm, R.FieldRing.of_nat(~F, ~field, 1n), norm, unit_above, A.Algebra.same_symmetric(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field), R.FieldRing.of_nat_one(~F, ~field)), A.Algebra.same_reflexive(~F, ~field, norm)))

def Geometry.unit_expr() -> R.FieldRing.Expr:
  R.Plus{R.Plus{R.Multiply{R.Variable{2n}, R.Variable{2n}}, R.Multiply{R.Variable{3n}, R.Variable{3n}}}, R.Negate{R.Number{1n}}}

def Geometry.offset_x_expr(local_x: R.FieldRing.Expr, local_y: R.FieldRing.Expr) -> R.FieldRing.Expr:
  R.Plus{R.Variable{0n}, R.Plus{R.Multiply{local_x, R.Variable{2n}}, R.Negate{R.Multiply{local_y, R.Variable{3n}}}}}

def Geometry.offset_y_expr(local_x: R.FieldRing.Expr, local_y: R.FieldRing.Expr) -> R.FieldRing.Expr:
  R.Plus{R.Variable{1n}, R.Plus{R.Multiply{local_x, R.Variable{3n}}, R.Multiply{local_y, R.Variable{2n}}}}

def Geometry.local_x_expr() -> R.FieldRing.Expr:
  R.Plus{R.Multiply{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{7n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}

def Geometry.local_y_expr() -> R.FieldRing.Expr:
  R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{7n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}

def Geometry.term(equation: Nat, multiplier: R.FieldRing.Expr, rest: C.Certificate.Terms) -> C.Certificate.Terms:
  C.MoreTerms{C.Multiple{equation, multiplier}, rest}

def Geometry.one_times(index: Nat) -> R.FieldRing.Expr:
  R.Multiply{R.Number{1n}, R.Variable{index}}

def Geometry.values(~F: Kind(&2), ~field: K.Field<F>, +center_x: F, +center_y: F, +cosine: F, +sine: F, +local_x: F, +local_y: F, +x: F, +y: F) -> R.FieldRing.Values<F>:
  R.Value{center_x, R.Value{center_y, R.Value{cosine, R.Value{sine, R.Value{local_x, R.Value{local_y, R.Value{x, R.Value{y, R.NoValues{}}}}}}}}}

def Geometry.containment_equations() -> C.Certificate.Exprs:
  C.MoreExprs{Geometry.unit_expr(), C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{Geometry.offset_x_expr(R.Variable{4n}, R.Variable{5n})}},
    C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{Geometry.offset_y_expr(R.Variable{4n}, R.Variable{5n})}}, C.NoExprs{}}}}

def Geometry.local_from(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +computed_x: F, +computed_y: F,
  same_x: A.Algebra.Same(~F, ~field, computed_x, local_x), same_y: A.Algebra.Same(~F, ~field, computed_y, local_y),
  +x_at_most: A.Algebra.le(~F, ~field, local_x, A.Algebra.half(~F, ~field)), +x_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x),
  +y_at_most: A.Algebra.le(~F, ~field, local_y, A.Algebra.half(~F, ~field)), +y_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y)) ->
  Geometry.Local<F, field, computed_x, computed_y>:
  (x_below, x_above) = same_x
  (y_below, y_above) = same_y
  Local{
    K.Field.le_transitive(F, field)(computed_x, local_x, A.Algebra.half(~F, ~field), x_below, x_at_most),
    K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x, computed_x, x_at_least, x_above),
    K.Field.le_transitive(F, field)(computed_y, local_y, A.Algebra.half(~F, ~field), y_below, y_at_most),
    K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y, computed_y, y_at_least, y_above)
  }

def Geometry.contains_local(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  containment: P.Problem.Containment<F, field, square, point>) ->
  Geometry.Local<F, field, Geometry.local_x(~F, ~field, square, point), Geometry.local_y(~F, ~field, square, point)>:
  match square point containment:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}
      P.Containment{+local_x, +local_y, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      +values: R.FieldRing.Values<F> = Geometry.values(~F, ~field, center_x, center_y, cosine, sine, local_x, local_y, x, y)
      +offset_x: F = A.Algebra.add(~F, ~field, center_x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, cosine), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, sine))))
      +offset_y: F = A.Algebra.add(~F, ~field, center_y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, sine), A.Algebra.mul(~F, ~field, local_y, cosine)))
      +equations: C.Certificate.Equations(~F, ~field, values, Geometry.containment_equations()) =
        C.Both{Geometry.unit(~F, ~field, cosine, sine, unit_below, unit_above),
          C.Both{Geometry.zero_difference(~F, ~field, x, offset_x, x_is_below, x_is_above),
            C.Both{Geometry.zero_difference(~F, ~field, y, offset_y, y_is_below, y_is_above), Unit{}}}}
      Geometry.local_from(~F, ~field, local_x, local_y,
        C.Certificate.value(~F, ~field, values, Geometry.local_x_expr()), C.Certificate.value(~F, ~field, values, Geometry.local_y_expr()),
        C.Certificate.same(~F, ~field, values, Geometry.containment_equations(), equations, Geometry.local_x_expr(), R.Variable{4n},
          Geometry.term(0n, R.Negate{Geometry.one_times(4n)}, Geometry.term(1n, R.Negate{Geometry.one_times(2n)}, Geometry.term(2n, R.Negate{Geometry.one_times(3n)}, C.NoTerms{}))), Geometry.term(0n, Geometry.one_times(4n), Geometry.term(1n, Geometry.one_times(2n), Geometry.term(2n, Geometry.one_times(3n), C.NoTerms{}))), {==}, {==}),
        C.Certificate.same(~F, ~field, values, Geometry.containment_equations(), equations, Geometry.local_y_expr(), R.Variable{5n},
          Geometry.term(0n, R.Negate{Geometry.one_times(5n)}, Geometry.term(1n, Geometry.one_times(3n), Geometry.term(2n, R.Negate{Geometry.one_times(2n)}, C.NoTerms{}))), Geometry.term(0n, Geometry.one_times(5n), Geometry.term(1n, R.Negate{Geometry.one_times(3n)}, Geometry.term(2n, Geometry.one_times(2n), C.NoTerms{}))), {==}, {==}),
        x_at_most, x_at_least, y_at_most, y_at_least)

def Geometry.unit_equations() -> C.Certificate.Exprs:
  C.MoreExprs{Geometry.unit_expr(), C.NoExprs{}}

def Geometry.containment_of(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, +local_x: F, +local_y: F,
  local: Geometry.Local<F, field, local_x, local_y>,
  same_x: A.Algebra.Same(~F, ~field, P.Problem.x(F, point), A.Algebra.add(~F, ~field, P.Problem.center_x(F, field, square),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.cosine(F, field, square)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, P.Problem.sine(F, field, square)))))),
  same_y: A.Algebra.Same(~F, ~field, P.Problem.y(F, point), A.Algebra.add(~F, ~field, P.Problem.center_y(F, field, square),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.sine(F, field, square)), A.Algebra.mul(~F, ~field, local_y, P.Problem.cosine(F, field, square)))))) ->
  P.Problem.Containment<F, field, square, point>:
  match local:
    case Local{x_at_most, x_at_least, y_at_most, y_at_least}:
      (x_is_below, x_is_above) = same_x
      (y_is_below, y_is_above) = same_y
      P.Containment{local_x, local_y, x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above}

def Geometry.local_contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  local: Geometry.Local<F, field, Geometry.local_x(~F, ~field, square, point), Geometry.local_y(~F, ~field, square, point)>) ->
  P.Problem.Containment<F, field, square, point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +values: R.FieldRing.Values<F> = Geometry.values(~F, ~field, center_x, center_y, cosine, sine, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field), x, y)
      +equations: C.Certificate.Equations(~F, ~field, values, Geometry.unit_equations()) =
        C.Both{Geometry.unit(~F, ~field, cosine, sine, unit_below, unit_above), Unit{}}
      Geometry.containment_of(~F, ~field,
        P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}, P.Point{x, y},
        C.Certificate.value(~F, ~field, values, Geometry.local_x_expr()), C.Certificate.value(~F, ~field, values, Geometry.local_y_expr()),
        local,
        C.Certificate.same(~F, ~field, values, Geometry.unit_equations(), equations,
          R.Variable{6n}, Geometry.offset_x_expr(Geometry.local_x_expr(), Geometry.local_y_expr()),
          Geometry.term(0n, R.Plus{Geometry.one_times(6n), R.Negate{Geometry.one_times(0n)}}, C.NoTerms{}), Geometry.term(0n, R.Plus{R.Negate{Geometry.one_times(6n)}, Geometry.one_times(0n)}, C.NoTerms{}), {==}, {==}),
        C.Certificate.same(~F, ~field, values, Geometry.unit_equations(), equations,
          R.Variable{7n}, Geometry.offset_y_expr(Geometry.local_x_expr(), Geometry.local_y_expr()),
          Geometry.term(0n, R.Plus{Geometry.one_times(7n), R.Negate{Geometry.one_times(1n)}}, C.NoTerms{}), Geometry.term(0n, R.Plus{R.Negate{Geometry.one_times(7n)}, Geometry.one_times(1n)}, C.NoTerms{}), {==}, {==}))

def Geometry.strict_local_from(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +computed_x: F, +computed_y: F,
  same_x: A.Algebra.Same(~F, ~field, computed_x, local_x), same_y: A.Algebra.Same(~F, ~field, computed_y, local_y),
  x_below: A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), local_x) -> Empty, x_above: A.Algebra.le(~F, ~field, local_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty,
  y_below: A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), local_y) -> Empty, y_above: A.Algebra.le(~F, ~field, local_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty) ->
  Geometry.StrictLocal<F, field, computed_x, computed_y>:
  (x_is_below, x_is_above) = same_x
  (y_is_below, y_is_above) = same_y
  StrictLocal{
    reached => x_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), computed_x, local_x, reached, x_is_below)),
    reached => x_above(K.Field.le_transitive(F, field)(local_x, computed_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x_is_above, reached)),
    reached => y_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), computed_y, local_y, reached, y_is_below)),
    reached => y_above(K.Field.le_transitive(F, field)(local_y, computed_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y_is_above, reached))
  }

def Geometry.interior_local(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  interior: P.Problem.InteriorContainment<F, field, square, point>) ->
  Geometry.StrictLocal<F, field, Geometry.local_x(~F, ~field, square, point), Geometry.local_y(~F, ~field, square, point)>:
  match square point interior:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}
      P.InteriorContainment{+local_x, +local_y, x_below, x_above, y_below, y_above, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      +values: R.FieldRing.Values<F> = Geometry.values(~F, ~field, center_x, center_y, cosine, sine, local_x, local_y, x, y)
      +offset_x: F = A.Algebra.add(~F, ~field, center_x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, cosine), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, sine))))
      +offset_y: F = A.Algebra.add(~F, ~field, center_y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, sine), A.Algebra.mul(~F, ~field, local_y, cosine)))
      +equations: C.Certificate.Equations(~F, ~field, values, Geometry.containment_equations()) =
        C.Both{Geometry.unit(~F, ~field, cosine, sine, unit_below, unit_above),
          C.Both{Geometry.zero_difference(~F, ~field, x, offset_x, x_is_below, x_is_above),
            C.Both{Geometry.zero_difference(~F, ~field, y, offset_y, y_is_below, y_is_above), Unit{}}}}
      Geometry.strict_local_from(~F, ~field, local_x, local_y,
        C.Certificate.value(~F, ~field, values, Geometry.local_x_expr()), C.Certificate.value(~F, ~field, values, Geometry.local_y_expr()),
        C.Certificate.same(~F, ~field, values, Geometry.containment_equations(), equations, Geometry.local_x_expr(), R.Variable{4n},
          Geometry.term(0n, R.Negate{Geometry.one_times(4n)}, Geometry.term(1n, R.Negate{Geometry.one_times(2n)}, Geometry.term(2n, R.Negate{Geometry.one_times(3n)}, C.NoTerms{}))), Geometry.term(0n, Geometry.one_times(4n), Geometry.term(1n, Geometry.one_times(2n), Geometry.term(2n, Geometry.one_times(3n), C.NoTerms{}))), {==}, {==}),
        C.Certificate.same(~F, ~field, values, Geometry.containment_equations(), equations, Geometry.local_y_expr(), R.Variable{5n},
          Geometry.term(0n, R.Negate{Geometry.one_times(5n)}, Geometry.term(1n, Geometry.one_times(3n), Geometry.term(2n, R.Negate{Geometry.one_times(2n)}, C.NoTerms{}))), Geometry.term(0n, Geometry.one_times(5n), Geometry.term(1n, R.Negate{Geometry.one_times(3n)}, Geometry.term(2n, Geometry.one_times(2n), C.NoTerms{}))), {==}, {==}),
        x_below, x_above, y_below, y_above)

def Geometry.interior_of(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>, +local_x: F, +local_y: F,
  local: Geometry.StrictLocal<F, field, local_x, local_y>,
  same_x: A.Algebra.Same(~F, ~field, P.Problem.x(F, point), A.Algebra.add(~F, ~field, P.Problem.center_x(F, field, square),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.cosine(F, field, square)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, P.Problem.sine(F, field, square)))))),
  same_y: A.Algebra.Same(~F, ~field, P.Problem.y(F, point), A.Algebra.add(~F, ~field, P.Problem.center_y(F, field, square),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.sine(F, field, square)), A.Algebra.mul(~F, ~field, local_y, P.Problem.cosine(F, field, square)))))) ->
  P.Problem.InteriorContainment<F, field, square, point>:
  match local:
    case StrictLocal{x_below, x_above, y_below, y_above}:
      (x_is_below, x_is_above) = same_x
      (y_is_below, y_is_above) = same_y
      P.InteriorContainment{local_x, local_y, x_below, x_above, y_below, y_above, x_is_below, x_is_above, y_is_below, y_is_above}

def Geometry.local_interior(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  local: Geometry.StrictLocal<F, field, Geometry.local_x(~F, ~field, square, point), Geometry.local_y(~F, ~field, square, point)>) ->
  P.Problem.InteriorContainment<F, field, square, point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +values: R.FieldRing.Values<F> = Geometry.values(~F, ~field, center_x, center_y, cosine, sine, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field), x, y)
      +equations: C.Certificate.Equations(~F, ~field, values, Geometry.unit_equations()) =
        C.Both{Geometry.unit(~F, ~field, cosine, sine, unit_below, unit_above), Unit{}}
      Geometry.interior_of(~F, ~field,
        P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}, P.Point{x, y},
        C.Certificate.value(~F, ~field, values, Geometry.local_x_expr()), C.Certificate.value(~F, ~field, values, Geometry.local_y_expr()),
        local,
        C.Certificate.same(~F, ~field, values, Geometry.unit_equations(), equations,
          R.Variable{6n}, Geometry.offset_x_expr(Geometry.local_x_expr(), Geometry.local_y_expr()),
          Geometry.term(0n, R.Plus{Geometry.one_times(6n), R.Negate{Geometry.one_times(0n)}}, C.NoTerms{}), Geometry.term(0n, R.Plus{R.Negate{Geometry.one_times(6n)}, Geometry.one_times(0n)}, C.NoTerms{}), {==}, {==}),
        C.Certificate.same(~F, ~field, values, Geometry.unit_equations(), equations,
          R.Variable{7n}, Geometry.offset_y_expr(Geometry.local_x_expr(), Geometry.local_y_expr()),
          Geometry.term(0n, R.Plus{Geometry.one_times(7n), R.Negate{Geometry.one_times(1n)}}, C.NoTerms{}), Geometry.term(0n, R.Plus{R.Negate{Geometry.one_times(7n)}, Geometry.one_times(1n)}, C.NoTerms{}), {==}, {==}))

def Geometry.square_unit(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, P.Problem.cosine(F, field, square), P.Problem.cosine(F, field, square)),
    A.Algebra.mul(~F, ~field, P.Problem.sine(F, field, square), P.Problem.sine(F, field, square))), A.Algebra.neg(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n))), A.Algebra.zero(~F, ~field)),
    A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, P.Problem.cosine(F, field, square), P.Problem.cosine(F, field, square)),
    A.Algebra.mul(~F, ~field, P.Problem.sine(F, field, square), P.Problem.sine(F, field, square))), A.Algebra.neg(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n))))>:
  match square:
    case P.Square{+center, P.Frame{+c, +s, +ub, +ua}}:
      Geometry.unit(~F, ~field, c, s, ub, ua)
