import Base
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

def Scaling.number(~F: Kind(&2), ~field: K.Field<F>, +n: Nat) -> F:
  R.FieldRing.of_nat(~F, ~field, n)

def Scaling.one_is_number(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.Same(~F, ~field, A.Algebra.one(~F, ~field), Scaling.number(~F, ~field, 1n)):
  A.Algebra.same_symmetric(~F, ~field, Scaling.number(~F, ~field, 1n), A.Algebra.one(~F, ~field), R.FieldRing.of_nat_one(~F, ~field))

def Scaling.fact(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, a))):
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, a)), A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, a)), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, a)), K.Field.le_add(F, field)(a, b, A.Algebra.neg(~F, ~field, a), below),
    A.Algebra.add_neg(~F, ~field, a), A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, b, A.Algebra.neg(~F, ~field, a))))

def Scaling.equation(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, same: A.Algebra.Same(~F, ~field, a, b)) -> C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.zero(~F, ~field)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)))>:
  (below, above) = same
  G.Geometry.zero_difference(~F, ~field, a, b, below, above)

def Scaling.number_bound(~F: Kind(&2), ~field: K.Field<F>, +a: F, below: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), a)) -> A.Algebra.le(~F, ~field, Scaling.number(~F, ~field, 1n), a):
  A.Algebra.le_respects(~F, ~field, A.Algebra.one(~F, ~field), a, Scaling.number(~F, ~field, 1n), a, below, Scaling.one_is_number(~F, ~field), A.Algebra.same_reflexive(~F, ~field, a))

def Scaling.number_bound_above(~F: Kind(&2), ~field: K.Field<F>, +a: F, below: A.Algebra.le(~F, ~field, a, Scaling.number(~F, ~field, 1n))) -> A.Algebra.le(~F, ~field, a, A.Algebra.one(~F, ~field)):
  A.Algebra.le_respects(~F, ~field, a, Scaling.number(~F, ~field, 1n), a, A.Algebra.one(~F, ~field), below, A.Algebra.same_reflexive(~F, ~field, a),
    A.Algebra.same_symmetric(~F, ~field, A.Algebra.one(~F, ~field), Scaling.number(~F, ~field, 1n), Scaling.one_is_number(~F, ~field)))

def Scaling.half_equation(~F: Kind(&2), ~field: K.Field<F>) -> C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n))), A.Algebra.zero(~F, ~field)),
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n))))>:
  Scaling.equation(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field)), Scaling.number(~F, ~field, 1n),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.half(~F, ~field)), A.Algebra.one(~F, ~field), Scaling.number(~F, ~field, 1n), K.Field.half_double(F, field), Scaling.one_is_number(~F, ~field)))

def Scaling.half_nonnegative(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field)):
  +h: F = A.Algebra.half(~F, ~field)
  C.Certificate.le(~F, ~field, R.Value{h, R.NoValues{}}, C.NoExprs{}, Unit{}, C.MoreExprs{R.Plus{R.Plus{R.Variable{0n}, R.Variable{0n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}, C.Both{Scaling.half_equation(~F, ~field), Unit{}}, R.Number{0n}, R.Variable{0n}, 1n, C.MoreTerms{C.Product{1n, C.NoIndices{}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Number{1n}}, C.NoTerms{}}}, {==})

def Scaling.inverse_equation(~F: Kind(&2), ~field: K.Field<F>, +factor: F, +inverse: F, cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, factor, inverse), A.Algebra.one(~F, ~field))) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, inverse), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n))), A.Algebra.zero(~F, ~field)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, inverse), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n))))>:
  Scaling.equation(~F, ~field, A.Algebra.mul(~F, ~field, factor, inverse), Scaling.number(~F, ~field, 1n),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, factor, inverse), A.Algebra.one(~F, ~field), Scaling.number(~F, ~field, 1n), cancel, Scaling.one_is_number(~F, ~field)))

def Scaling.inverse_nonnegative(~F: Kind(&2), ~field: K.Field<F>, +f: F, +i: F, at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), f), cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i):
  C.Certificate.le(~F, ~field, R.Value{f, R.Value{i, R.NoValues{}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Negate{R.Number{1n}}}, C.NoExprs{}}, C.Both{Scaling.fact(~F, ~field, Scaling.number(~F, ~field, 1n), f, Scaling.number_bound(~F, ~field, f, at_least)), Unit{}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}, C.Both{Scaling.inverse_equation(~F, ~field, f, i, cancel), Unit{}}, R.Number{0n}, R.Variable{1n}, 0n, C.MoreTerms{C.Product{1n, C.NoIndices{}, R.Variable{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.NoIndices{}}, R.Variable{1n}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{1n}}}}, C.NoTerms{}}}}, {==})

def Scaling.inverse_at_most_one(~F: Kind(&2), ~field: K.Field<F>, +f: F, +i: F, at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), f), +nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, i, A.Algebra.one(~F, ~field)):
  Scaling.number_bound_above(~F, ~field, i,
    C.Certificate.le(~F, ~field, R.Value{f, R.Value{i, R.NoValues{}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Variable{1n}, C.NoExprs{}}}, C.Both{Scaling.fact(~F, ~field, Scaling.number(~F, ~field, 1n), f, Scaling.number_bound(~F, ~field, f, at_least)), C.Both{nonnegative, Unit{}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}, C.Both{Scaling.inverse_equation(~F, ~field, f, i, cancel), Unit{}}, R.Variable{1n}, R.Number{1n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Number{1n}}}, C.NoTerms{}}}, {==}))

def Scaling.scaled_at_most(~F: Kind(&2), ~field: K.Field<F>, +h: F, +l: F, +i: F, at_most: A.Algebra.le(~F, ~field, l, h), +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), i_at_most: A.Algebra.le(~F, ~field, i, A.Algebra.one(~F, ~field)),
  +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), h)) -> A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, l, i), h):
  C.Certificate.le(~F, ~field, R.Value{h, R.Value{l, R.Value{i, R.NoValues{}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, C.MoreExprs{R.Variable{2n}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Plus{R.Number{1n}, R.Negate{R.Variable{2n}}}, C.NoExprs{}}}}}, C.Both{Scaling.fact(~F, ~field, l, h, at_most), C.Both{i_nonnegative, C.Both{h_nonnegative, C.Both{Scaling.fact(~F, ~field, i, Scaling.number(~F, ~field, 1n), A.Algebra.le_respects(~F, ~field, i, A.Algebra.one(~F, ~field), i, Scaling.number(~F, ~field, 1n), i_at_most, A.Algebra.same_reflexive(~F, ~field, i), Scaling.one_is_number(~F, ~field))), Unit{}}}}}, C.NoExprs{}, Unit{}, R.Multiply{R.Variable{1n}, R.Variable{2n}}, R.Variable{0n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{2n, C.MoreIndices{3n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}}, {==})

def Scaling.scaled_at_least(~F: Kind(&2), ~field: K.Field<F>, +h: F, +l: F, +i: F, at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, h), l), +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), i_at_most: A.Algebra.le(~F, ~field, i, A.Algebra.one(~F, ~field)),
  +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), h)) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, h), A.Algebra.mul(~F, ~field, l, i)):
  C.Certificate.le(~F, ~field, R.Value{h, R.Value{l, R.Value{i, R.NoValues{}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Negate{R.Negate{R.Variable{0n}}}}, C.MoreExprs{R.Variable{2n}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Plus{R.Number{1n}, R.Negate{R.Variable{2n}}}, C.NoExprs{}}}}}, C.Both{Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, h), l, at_least), C.Both{i_nonnegative, C.Both{h_nonnegative, C.Both{Scaling.fact(~F, ~field, i, Scaling.number(~F, ~field, 1n), A.Algebra.le_respects(~F, ~field, i, A.Algebra.one(~F, ~field), i, Scaling.number(~F, ~field, 1n), i_at_most, A.Algebra.same_reflexive(~F, ~field, i), Scaling.one_is_number(~F, ~field))), Unit{}}}}}, C.NoExprs{}, Unit{}, R.Negate{R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{2n}}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{1n, C.MoreIndices{2n, C.MoreIndices{3n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}}, {==})

def Scaling.pair(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +below: A.Algebra.le(~F, ~field, a, b), +above: A.Algebra.le(~F, ~field, b, a)) -> A.Algebra.Same(~F, ~field, a, b):
  (below, above)

def Scaling.scale_center(~F: Kind(&2), ~field: K.Field<F>, +factor: F, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, frame}:
      P.Square{P.Point{A.Algebra.mul(~F, ~field, factor, center_x), A.Algebra.mul(~F, ~field, factor, center_y)}, frame}

def Scaling.scale_point(~F: Kind(&2), ~field: K.Field<F>, +factor: F, point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{A.Algebra.mul(~F, ~field, factor, x), A.Algebra.mul(~F, ~field, factor, y)}

def Scaling.coordinate(~F: Kind(&2), ~field: K.Field<F>, +value: F, +scaled: F, +bound: F, same: A.Algebra.Same(~F, ~field, value, scaled), +low: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), scaled), +high: A.Algebra.le(~F, ~field, scaled, bound)) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), value), A.Algebra.le(~F, ~field, value, bound)>:
  (below, above) = same
  C.Both{K.Field.le_transitive(F, field)(A.Algebra.zero(~F, ~field), scaled, value, low, above), K.Field.le_transitive(F, field)(value, scaled, bound, below, high)}

def Scaling.in_container(~F: Kind(&2), ~field: K.Field<F>, +side: F, +x: F, +y: F,
  x_bounds: C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), x), A.Algebra.le(~F, ~field, x, side)>, y_bounds: C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), y), A.Algebra.le(~F, ~field, y, side)>) ->
  P.Problem.InContainer<F, field, side, P.Point{x, y}>:
  match x_bounds y_bounds:
    case C.Both{left, right} C.Both{bottom, top}:
      P.InContainer{left, right, bottom, top}

def Scaling.scale_finish(~F: Kind(&2), ~field: K.Field<F>, +cx: F, +cy: F, +c: F, +s: F, +lx: F, +ly: F, +x: F, +y: F, +f: F, +i: F, +side: F,
  +x_is_below: A.Algebra.le(~F, ~field, x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s))))),
  +x_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), x),
  +y_is_below: A.Algebra.le(~F, ~field, y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c)))),
  +y_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), y),
  +cancel_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field)), +cancel_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, f, i)), +f_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), f),
  inner: P.Problem.InContainer<F, field, side, P.Point{
    A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, ly, i), s)))), A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), s), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, ly, i), c)))}>) ->
  P.Problem.InContainer<F, field, A.Algebra.mul(~F, ~field, f, side), P.Point{x, y}>:
  match inner:
    case P.InContainer{+left, +right, +bottom, +top}:
      +qx: F = A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, ly, i), s))))
      +qy: F = A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), s), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, ly, i), c)))
      +equations: C.Certificate.Equations(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{0n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}) =
        C.Both{G.Geometry.zero_difference(~F, ~field, x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), x_is_below, x_is_above),
          C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), Unit{}}}
      +y_equations: C.Certificate.Equations(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{1n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}) =
        C.Both{G.Geometry.zero_difference(~F, ~field, y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), y_is_below, y_is_above),
          C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), Unit{}}}
      Scaling.in_container(~F, ~field, A.Algebra.mul(~F, ~field, f, side), x, y,
        Scaling.coordinate(~F, ~field, x, A.Algebra.mul(~F, ~field, f, qx), A.Algebra.mul(~F, ~field, f, side),
          C.Certificate.same(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{0n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, equations, R.Variable{6n}, R.Multiply{R.Variable{8n}, R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Multiply{R.Variable{4n}, R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Multiply{R.Variable{5n}, R.Variable{9n}}, R.Variable{3n}}}}}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Number{1n}}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{5n}}}, R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{4n}}}}, C.NoTerms{}}}, C.MoreTerms{C.Multiple{0n, R.Number{1n}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{5n}}, R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{4n}}}}}, C.NoTerms{}}}, {==}, {==}),
          C.Certificate.le(~F, ~field, R.Value{f, R.Value{qx, R.NoValues{}}}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Variable{1n}, C.NoExprs{}}}, C.Both{f_nonnegative, C.Both{left, Unit{}}}, C.NoExprs{}, Unit{}, R.Number{0n}, R.Multiply{R.Variable{0n}, R.Variable{1n}}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}, {==}),
          C.Certificate.le(~F, ~field, R.Value{f, R.Value{qx, R.Value{side, R.NoValues{}}}}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Plus{R.Variable{2n}, R.Negate{R.Variable{1n}}}, C.NoExprs{}}}, C.Both{f_nonnegative, C.Both{Scaling.fact(~F, ~field, qx, side, right), Unit{}}}, C.NoExprs{}, Unit{}, R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Multiply{R.Variable{0n}, R.Variable{2n}}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}, {==})),
        Scaling.coordinate(~F, ~field, y, A.Algebra.mul(~F, ~field, f, qy), A.Algebra.mul(~F, ~field, f, side),
          C.Certificate.same(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{1n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, y_equations, R.Variable{7n}, R.Multiply{R.Variable{8n}, R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Multiply{R.Variable{4n}, R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Multiply{R.Variable{5n}, R.Variable{9n}}, R.Variable{2n}}}}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Number{1n}}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{4n}}, R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{5n}}}}, C.NoTerms{}}}, C.MoreTerms{C.Multiple{0n, R.Number{1n}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{3n}}, R.Variable{4n}}}, R.Negate{R.Multiply{R.Multiply{R.Number{1n}, R.Variable{2n}}, R.Variable{5n}}}}}, C.NoTerms{}}}, {==}, {==}),
          C.Certificate.le(~F, ~field, R.Value{f, R.Value{qy, R.NoValues{}}}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Variable{1n}, C.NoExprs{}}}, C.Both{f_nonnegative, C.Both{bottom, Unit{}}}, C.NoExprs{}, Unit{}, R.Number{0n}, R.Multiply{R.Variable{0n}, R.Variable{1n}}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}, {==}),
          C.Certificate.le(~F, ~field, R.Value{f, R.Value{qy, R.Value{side, R.NoValues{}}}}, C.MoreExprs{R.Variable{0n}, C.MoreExprs{R.Plus{R.Variable{2n}, R.Negate{R.Variable{1n}}}, C.NoExprs{}}}, C.Both{f_nonnegative, C.Both{Scaling.fact(~F, ~field, qy, side, top), Unit{}}}, C.NoExprs{}, Unit{}, R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Multiply{R.Variable{0n}, R.Variable{2n}}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.NoTerms{}}, {==})))

def Scaling.scale_with_cancel(~F: Kind(&2), ~field: K.Field<F>, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s)), A.Algebra.one(~F, ~field)), +unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s))),
  +lx: F, +ly: F, +x: F, +y: F, +f: F, +side: F,
  fits: Y.Symmetry.Fits(~F, ~field, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, side),
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), f),
  +x_at_most: A.Algebra.le(~F, ~field, lx, A.Algebra.half(~F, ~field)), +x_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx), +y_at_most: A.Algebra.le(~F, ~field, ly, A.Algebra.half(~F, ~field)), +y_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly),
  +x_is_below: A.Algebra.le(~F, ~field, x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s))))),
  +x_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), x),
  +y_is_below: A.Algebra.le(~F, ~field, y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c)))),
  +y_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), y),
  cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, f, A.Algebra.inverse(~F, ~field, f)), A.Algebra.one(~F, ~field))) ->
  P.Problem.InContainer<F, field, A.Algebra.mul(~F, ~field, f, side), P.Point{x, y}>:
  (+cancel_below, +cancel_above) = cancel
  +i: F = A.Algebra.inverse(~F, ~field, f)
  +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i) = Scaling.inverse_nonnegative(~F, ~field, f, i, at_least, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above))
  +i_at_most: A.Algebra.le(~F, ~field, i, A.Algebra.one(~F, ~field)) = Scaling.inverse_at_most_one(~F, ~field, f, i, at_least, i_nonnegative, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above))
  +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field)) = Scaling.half_nonnegative(~F, ~field)
  +li: F = A.Algebra.mul(~F, ~field, lx, i)
  +mi: F = A.Algebra.mul(~F, ~field, ly, i)
  +qx: F = A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, li, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, mi, s))))
  +qy: F = A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, li, s), A.Algebra.mul(~F, ~field, mi, c)))
  Scaling.scale_finish(~F, ~field, cx, cy, c, s, lx, ly, x, y, f, i, side,
    x_is_below, x_is_above, y_is_below, y_is_above, cancel_below, cancel_above,
    K.Field.le_transitive(F, field)(A.Algebra.zero(~F, ~field), A.Algebra.one(~F, ~field), f, K.Field.zero_le_one(F, field), at_least),
    fits(P.Point{qx, qy},
      P.Containment{li, mi,
        Scaling.scaled_at_most(~F, ~field, A.Algebra.half(~F, ~field), lx, i, x_at_most, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_least(~F, ~field, A.Algebra.half(~F, ~field), lx, i, x_at_least, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_most(~F, ~field, A.Algebra.half(~F, ~field), ly, i, y_at_most, i_nonnegative, i_at_most, h_nonnegative),
        Scaling.scaled_at_least(~F, ~field, A.Algebra.half(~F, ~field), ly, i, y_at_least, i_nonnegative, i_at_most, h_nonnegative),
        K.Field.le_reflexive(F, field)(qx), K.Field.le_reflexive(F, field)(qx), K.Field.le_reflexive(F, field)(qy), K.Field.le_reflexive(F, field)(qy)}))


def Scaling.scale_fits_at(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +factor: F, fits: Y.Symmetry.Fits(~F, ~field, square, side),
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), factor), positive: A.Algebra.le(~F, ~field, factor, A.Algebra.zero(~F, ~field)) -> Empty, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Scaling.scale_center(~F, ~field, factor, square), point>) ->
  P.Problem.InContainer<F, field, A.Algebra.mul(~F, ~field, factor, side), point>:
  match square point inside:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}} P.Point{+x, +y}
      P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      Scaling.scale_with_cancel(~F, ~field, cx, cy, c, s, unit_below, unit_above, lx, ly, x, y, factor, side, fits, at_least,
        x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above,
        A.Algebra.mul_inverse(~F, ~field, factor, positive))

def Scaling.scale_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +factor: F, fits: Y.Symmetry.Fits(~F, ~field, square, side),
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), factor), positive: A.Algebra.le(~F, ~field, factor, A.Algebra.zero(~F, ~field)) -> Empty) ->
  Y.Symmetry.Fits(~F, ~field, Scaling.scale_center(~F, ~field, factor, square), A.Algebra.mul(~F, ~field, factor, side)):
  +point => inside => Scaling.scale_fits_at(~F, ~field, square, side, factor, fits, at_least, positive, point, inside)

def Scaling.refute_above(~F: Kind(&2), ~field: K.Field<F>, +lx: F, +i: F, +f: F, +bound: A.Algebra.le(~F, ~field, lx, A.Algebra.half(~F, ~field)), +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), +f_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), f),
  +cancel_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field)), +cancel_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, f, i)), +reached: A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.mul(~F, ~field, lx, i))) -> A.Algebra.le(~F, ~field, f, Scaling.number(~F, ~field, 1n)):
  C.Certificate.le(~F, ~field, R.Value{A.Algebra.half(~F, ~field), R.Value{lx, R.Value{i, R.Value{f, R.NoValues{}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{1n}, R.Variable{2n}}, R.Negate{R.Variable{0n}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, C.MoreExprs{R.Variable{2n}, C.MoreExprs{R.Variable{3n}, C.NoExprs{}}}}}, C.Both{Scaling.fact(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.mul(~F, ~field, lx, i), reached), C.Both{Scaling.fact(~F, ~field, lx, A.Algebra.half(~F, ~field), bound), C.Both{i_nonnegative, C.Both{f_nonnegative, Unit{}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{3n}, R.Variable{2n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{0n}, R.Variable{0n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), C.Both{Scaling.half_equation(~F, ~field), Unit{}}}, R.Variable{3n}, R.Number{1n}, 0n, C.MoreTerms{C.Product{2n, C.MoreIndices{1n, C.NoIndices{}}, R.Number{1n}}, C.MoreTerms{C.Product{2n, C.MoreIndices{0n, C.MoreIndices{3n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Multiply{R.Number{2n}, R.Variable{1n}}}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Negate{R.Number{1n}}, R.Multiply{R.Number{1n}, R.Variable{3n}}}}, C.NoTerms{}}}}}, {==})
def Scaling.refute_below(~F: Kind(&2), ~field: K.Field<F>, +lx: F, +i: F, +f: F, +bound: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx), +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), +f_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), f),
  +cancel_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field)), +cancel_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, f, i)), +reached: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)))) -> A.Algebra.le(~F, ~field, f, Scaling.number(~F, ~field, 1n)):
  C.Certificate.le(~F, ~field, R.Value{A.Algebra.half(~F, ~field), R.Value{lx, R.Value{i, R.Value{f, R.NoValues{}}}}}, C.MoreExprs{R.Plus{R.Negate{R.Variable{0n}}, R.Negate{R.Multiply{R.Variable{1n}, R.Variable{2n}}}}, C.MoreExprs{R.Plus{R.Variable{1n}, R.Negate{R.Negate{R.Variable{0n}}}}, C.MoreExprs{R.Variable{2n}, C.MoreExprs{R.Variable{3n}, C.NoExprs{}}}}}, C.Both{Scaling.fact(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), reached), C.Both{Scaling.fact(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx, bound), C.Both{i_nonnegative, C.Both{f_nonnegative, Unit{}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{3n}, R.Variable{2n}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{0n}, R.Variable{0n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), C.Both{Scaling.half_equation(~F, ~field), Unit{}}}, R.Variable{3n}, R.Number{1n}, 0n, C.MoreTerms{C.Product{2n, C.MoreIndices{1n, C.NoIndices{}}, R.Number{1n}}, C.MoreTerms{C.Product{2n, C.MoreIndices{0n, C.MoreIndices{3n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Multiply{R.Number{2n}, R.Variable{1n}}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Negate{R.Number{1n}}, R.Multiply{R.Number{1n}, R.Variable{3n}}}}, C.NoTerms{}}}}}, {==})
def Scaling.never_reaches(~F: Kind(&2), ~field: K.Field<F>, +lx: F, +i: F, +f: F, +greater: O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), f),
  +at_most: A.Algebra.le(~F, ~field, lx, A.Algebra.half(~F, ~field)), +at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx), +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i), +f_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), f),
  +cancel_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field)), +cancel_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, f, i))) ->
  (A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.mul(~F, ~field, lx, i)) -> Empty) & (A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, lx, i), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty):
  (
    reached => O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), f, greater)(Scaling.number_bound_above(~F, ~field, f,
      Scaling.refute_above(~F, ~field, lx, i, f, at_most, i_nonnegative, f_nonnegative, cancel_below, cancel_above, reached))),
    reached => O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), f, greater)(Scaling.number_bound_above(~F, ~field, f,
      Scaling.refute_below(~F, ~field, lx, i, f, at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above, reached)))
  )

def Scaling.interior_of_sames(~F: Kind(&2), ~field: K.Field<F>, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s)), A.Algebra.one(~F, ~field)), +unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s))),
  +local_x: F, +local_y: F, +x: F, +y: F,
  x_never: (A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), local_x) -> Empty) & (A.Algebra.le(~F, ~field, local_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty),
  y_never: (A.Algebra.le(~F, ~field, A.Algebra.half(~F, ~field), local_y) -> Empty) & (A.Algebra.le(~F, ~field, local_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty),
  x_same: A.Algebra.Same(~F, ~field, x, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, s))))),
  y_same: A.Algebra.Same(~F, ~field, y, A.Algebra.add(~F, ~field, cy, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, s), A.Algebra.mul(~F, ~field, local_y, c))))) ->
  P.Problem.InteriorContainment<F, field, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, P.Point{x, y}>:
  (x_below, x_above) = x_never
  (y_below, y_above) = y_never
  (x_is_below, x_is_above) = x_same
  (y_is_below, y_is_above) = y_same
  P.InteriorContainment{local_x, local_y, x_below, x_above, y_below, y_above, x_is_below, x_is_above, y_is_below, y_is_above}

def Scaling.interior_back_with(~F: Kind(&2), ~field: K.Field<F>, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s)), A.Algebra.one(~F, ~field)), +unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s))),
  +lx: F, +ly: F, +x: F, +y: F, +f: F, +greater: O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), f),
  +x_at_most: A.Algebra.le(~F, ~field, lx, A.Algebra.half(~F, ~field)), +x_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), lx), +y_at_most: A.Algebra.le(~F, ~field, ly, A.Algebra.half(~F, ~field)), +y_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), ly),
  +x_is_below: A.Algebra.le(~F, ~field, x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s))))),
  +x_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), x),
  +y_is_below: A.Algebra.le(~F, ~field, y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c)))),
  +y_is_above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), y),
  cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, f, A.Algebra.inverse(~F, ~field, f)), A.Algebra.one(~F, ~field))) ->
  P.Problem.InteriorContainment<F, field, P.Square{P.Point{cx, cy}, P.Frame{c, s, unit_below, unit_above}}, P.Point{A.Algebra.mul(~F, ~field, A.Algebra.inverse(~F, ~field, f), x), A.Algebra.mul(~F, ~field, A.Algebra.inverse(~F, ~field, f), y)}>:
  (+cancel_below, +cancel_above) = cancel
  +i: F = A.Algebra.inverse(~F, ~field, f)
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), f) = O.FieldOrder.le_of_lt(~F, ~field, A.Algebra.one(~F, ~field), f, O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), f, greater))
  +i_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), i) = Scaling.inverse_nonnegative(~F, ~field, f, i, at_least, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above))
  +f_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), f) = K.Field.le_transitive(F, field)(A.Algebra.zero(~F, ~field), A.Algebra.one(~F, ~field), f, K.Field.zero_le_one(F, field), at_least)
  +equations: C.Certificate.Equations(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{0n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}) =
    C.Both{G.Geometry.zero_difference(~F, ~field, x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cx), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, ly, s)))), x_is_below, x_is_above),
      C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), Unit{}}}
  +y_equations: C.Certificate.Equations(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{1n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}) =
    C.Both{G.Geometry.zero_difference(~F, ~field, y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, f, cy), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, lx, s), A.Algebra.mul(~F, ~field, ly, c))), y_is_below, y_is_above),
      C.Both{Scaling.inverse_equation(~F, ~field, f, i, Scaling.pair(~F, ~field, A.Algebra.mul(~F, ~field, f, i), A.Algebra.one(~F, ~field), cancel_below, cancel_above)), Unit{}}}
  Scaling.interior_of_sames(~F, ~field, cx, cy, c, s, unit_below, unit_above, A.Algebra.mul(~F, ~field, lx, i), A.Algebra.mul(~F, ~field, ly, i), A.Algebra.mul(~F, ~field, i, x), A.Algebra.mul(~F, ~field, i, y),
    Scaling.never_reaches(~F, ~field, lx, i, f, greater, x_at_most, x_at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above),
    Scaling.never_reaches(~F, ~field, ly, i, f, greater, y_at_most, y_at_least, i_nonnegative, f_nonnegative, cancel_below, cancel_above),
    C.Certificate.same(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{6n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{0n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{2n}}, R.Negate{R.Multiply{R.Variable{5n}, R.Variable{3n}}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, equations, R.Multiply{R.Variable{9n}, R.Variable{6n}}, R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Multiply{R.Variable{4n}, R.Variable{9n}}, R.Variable{2n}}, R.Negate{R.Multiply{R.Multiply{R.Variable{5n}, R.Variable{9n}}, R.Variable{3n}}}}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{9n}}}}, C.MoreTerms{C.Multiple{1n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{0n}}}}, C.NoTerms{}}}, C.MoreTerms{C.Multiple{0n, R.Multiply{R.Number{1n}, R.Variable{9n}}}, C.MoreTerms{C.Multiple{1n, R.Multiply{R.Number{1n}, R.Variable{0n}}}, C.NoTerms{}}}, {==}, {==}),
    C.Certificate.same(~F, ~field, R.Value{cx, R.Value{cy, R.Value{c, R.Value{s, R.Value{lx, R.Value{ly, R.Value{x, R.Value{y, R.Value{f, R.Value{i, R.NoValues{}}}}}}}}}}}, C.MoreExprs{R.Plus{R.Variable{7n}, R.Negate{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{1n}}, R.Plus{R.Multiply{R.Variable{4n}, R.Variable{3n}}, R.Multiply{R.Variable{5n}, R.Variable{2n}}}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{8n}, R.Variable{9n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, y_equations, R.Multiply{R.Variable{9n}, R.Variable{7n}}, R.Plus{R.Variable{1n}, R.Plus{R.Multiply{R.Multiply{R.Variable{4n}, R.Variable{9n}}, R.Variable{3n}}, R.Multiply{R.Multiply{R.Variable{5n}, R.Variable{9n}}, R.Variable{2n}}}}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{9n}}}}, C.MoreTerms{C.Multiple{1n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{1n}}}}, C.NoTerms{}}}, C.MoreTerms{C.Multiple{0n, R.Multiply{R.Number{1n}, R.Variable{9n}}}, C.MoreTerms{C.Multiple{1n, R.Multiply{R.Number{1n}, R.Variable{1n}}}, C.NoTerms{}}}, {==}, {==}))

def Scaling.interior_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +factor: F, +greater: O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), factor),
  +point: P.Problem.Point<F>, inside: P.Problem.Containment<F, field, Scaling.scale_center(~F, ~field, factor, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Scaling.scale_point(~F, ~field, A.Algebra.inverse(~F, ~field, factor), point)>:
  match square point inside:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}} P.Point{+x, +y}
      P.Containment{+lx, +ly, +x_at_most, +x_at_least, +y_at_most, +y_at_least, +x_is_below, +x_is_above, +y_is_below, +y_is_above}:
      Scaling.interior_back_with(~F, ~field, cx, cy, c, s, unit_below, unit_above, lx, ly, x, y, factor, greater,
        x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above,
        A.Algebra.mul_inverse(~F, ~field, factor, below => O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), factor, greater)(
          K.Field.le_transitive(F, field)(factor, A.Algebra.zero(~F, ~field), A.Algebra.one(~F, ~field), below, K.Field.zero_le_one(F, field)))))

def Scaling.anything(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +broken: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n)))) -> A.Algebra.le(~F, ~field, a, b):
  C.Certificate.le(~F, ~field, R.Value{a, R.Value{b, R.NoValues{}}}, C.MoreExprs{R.Negate{R.Number{1n}}, C.NoExprs{}}, C.Both{broken, Unit{}}, C.NoExprs{}, Unit{}, R.Variable{0n}, R.Variable{1n}, 3n, C.MoreTerms{C.Product{1n, C.NoIndices{}, R.Plus{R.Plus{R.Variable{1n}, R.Negate{R.Variable{0n}}}, R.Number{1n}}}, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.NoIndices{}}, R.Plus{R.Plus{R.Variable{1n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Number{1n}}}}, C.NoTerms{}}}, {==})

def Scaling.point_at(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F) -> P.Problem.Point<F>:
  P.Point{
    A.Algebra.add(~F, ~field, P.Problem.center_x(F, field, square), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.cosine(F, field, square)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, P.Problem.sine(F, field, square))))),
    A.Algebra.add(~F, ~field, P.Problem.center_y(F, field, square), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, P.Problem.sine(F, field, square)), A.Algebra.mul(~F, ~field, local_y, P.Problem.cosine(F, field, square))))}

def Scaling.containment_at(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +local_x: F, +local_y: F,
  +x_at_most: A.Algebra.le(~F, ~field, local_x, A.Algebra.half(~F, ~field)), +x_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x), +y_at_most: A.Algebra.le(~F, ~field, local_y, A.Algebra.half(~F, ~field)), +y_at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y)) ->
  P.Problem.Containment<F, field, square, Scaling.point_at(~F, ~field, square, local_x, local_y)>:
  +x: F = P.Problem.x(F, Scaling.point_at(~F, ~field, square, local_x, local_y))
  +y: F = P.Problem.y(F, Scaling.point_at(~F, ~field, square, local_x, local_y))
  P.Containment{local_x, local_y, x_at_most, x_at_least, y_at_most, y_at_least,
    K.Field.le_reflexive(F, field)(x), K.Field.le_reflexive(F, field)(x), K.Field.le_reflexive(F, field)(y), K.Field.le_reflexive(F, field)(y)}

def Scaling.negative_half_at_most(~F: Kind(&2), ~field: K.Field<F>, +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.half(~F, ~field)):
  K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field), Y.Symmetry.negate_bound_left(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field),
    A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.half(~F, ~field), h_nonnegative,
      R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Number{0n}, R.Negate{R.Number{0n}}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.half(~F, ~field)))), h_nonnegative)

def Scaling.negative_half_below_zero(~F: Kind(&2), ~field: K.Field<F>, +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field)):
  Y.Symmetry.negate_bound_left(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field),
    A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.half(~F, ~field), h_nonnegative,
      R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Number{0n}, R.Negate{R.Number{0n}}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.half(~F, ~field))))

def Scaling.side_broken(~F: Kind(&2), ~field: K.Field<F>, +cx: F, +cy: F, +c: F, +s: F,
  +unit_below: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s)), A.Algebra.one(~F, ~field)), +unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, c), A.Algebra.mul(~F, ~field, s, s))), +side: F,
  +nonpositive: A.Algebra.le(~F, ~field, side, A.Algebra.zero(~F, ~field)),
  +left_0: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s))))), +right_0: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s)))), side),
  +left_1: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s))))), +right_1: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s)))), side),
  +left_2: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s))))), +right_2: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s)))), side),
  +left_3: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s))))), +right_3: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s)))), side),
  +done: Unit) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, Scaling.number(~F, ~field, 1n))):
  C.Certificate.le(~F, ~field, R.Value{cx, R.Value{c, R.Value{s, R.Value{A.Algebra.half(~F, ~field), R.Value{side, R.NoValues{}}}}}}, C.MoreExprs{R.Plus{R.Number{0n}, R.Negate{R.Variable{4n}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{3n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Number{0n}, R.Variable{2n}}}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{3n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Number{0n}, R.Variable{2n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{3n}}, R.Variable{1n}}, R.Negate{R.Multiply{R.Number{0n}, R.Variable{2n}}}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Negate{R.Variable{3n}}, R.Variable{1n}}, R.Negate{R.Multiply{R.Number{0n}, R.Variable{2n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Number{0n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Variable{3n}, R.Variable{2n}}}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Number{0n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Variable{3n}, R.Variable{2n}}}}}}}, C.MoreExprs{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Number{0n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Negate{R.Variable{3n}}, R.Variable{2n}}}}}, C.MoreExprs{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Number{0n}, R.Variable{1n}}, R.Negate{R.Multiply{R.Negate{R.Variable{3n}}, R.Variable{2n}}}}}}}, C.NoExprs{}}}}}}}}}}, C.Both{Scaling.fact(~F, ~field, side, A.Algebra.zero(~F, ~field), nonpositive), C.Both{left_0, C.Both{Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s)))), side, right_0), C.Both{left_1, C.Both{Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), s)))), side, right_1), C.Both{left_2, C.Both{Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.half(~F, ~field), s)))), side, right_2), C.Both{left_3, C.Both{Scaling.fact(~F, ~field, A.Algebra.add(~F, ~field, cx, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), c), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), s)))), side, right_3), Unit{}}}}}}}}}}, C.MoreExprs{R.Plus{R.Plus{R.Multiply{R.Variable{1n}, R.Variable{1n}}, R.Multiply{R.Variable{2n}, R.Variable{2n}}}, R.Negate{R.Number{1n}}}, C.MoreExprs{R.Plus{R.Plus{R.Variable{3n}, R.Variable{3n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}}, C.Both{G.Geometry.unit(~F, ~field, c, s, unit_below, unit_above), C.Both{Scaling.half_equation(~F, ~field), Unit{}}}, R.Number{0n}, R.Negate{R.Number{1n}}, 0n, C.MoreTerms{C.Product{2n, C.MoreIndices{0n, C.MoreIndices{5n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{2n, C.MoreIndices{0n, C.MoreIndices{7n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{4n, C.MoreIndices{1n, C.MoreIndices{3n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{2n, C.MoreIndices{5n, C.MoreIndices{6n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Product{2n, C.MoreIndices{7n, C.MoreIndices{8n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Multiply{R.Multiply{R.Number{4n}, R.Variable{3n}}, R.Variable{3n}}}, C.MoreTerms{C.Multiple{1n, R.Plus{R.Number{1n}, R.Multiply{R.Number{2n}, R.Variable{3n}}}}, C.NoTerms{}}}}}}}}, {==})

def Scaling.side_positive_at(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target),
  +inside_0: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, square, A.Algebra.half(~F, ~field), A.Algebra.zero(~F, ~field))>,
  +inside_1: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, square, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field))>,
  +inside_2: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, square, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field))>,
  +inside_3: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, square, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)))>,
  +nonpositive: A.Algebra.le(~F, ~field, side, A.Algebra.zero(~F, ~field))) -> Empty:
  match square inside_0 inside_1 inside_2 inside_3:
    case P.Square{P.Point{+cx, +cy}, P.Frame{+c, +s, +unit_below, +unit_above}}
      P.InContainer{+left_0, +right_0, +b0, +t0} P.InContainer{+left_1, +right_1, +b1, +t1}
      P.InContainer{+left_2, +right_2, +b2, +t2} P.InContainer{+left_3, +right_3, +b3, +t3}:
      O.FieldOrder.lt_of(~F, ~field, side, target, less)(Scaling.anything(~F, ~field, target, side,
        Scaling.side_broken(~F, ~field, cx, cy, c, s, unit_below, unit_above, side, nonpositive,
          left_0, right_0, left_1, right_1, left_2, right_2, left_3, right_3, Unit{})))

type Scaling.ClosedFamily<-F: Kind(&2), -field: K.Field<F>, -count: Nat, -target: F> is Type:
  ClosedFamily{
    squares: Nat -> P.Problem.Square<F, field>,
    fits: @index: Nat -> N.Natural.Le(1n+index, count) -> @point: P.Problem.Point<F> ->
      P.Problem.Containment<F, field, squares(index), point> -> P.Problem.InContainer<F, field, target, point>,
    disjoint: @left: Nat -> @right: Nat -> N.Natural.Le(1n+left, count) -> N.Natural.Le(1n+right, count) ->
      ({left == right : Nat} -> Empty) -> @point: P.Problem.Point<F> ->
      P.Problem.Containment<F, field, squares(left), point> -> P.Problem.Containment<F, field, squares(right), point> -> Empty
  }

def Scaling.container_to(~F: Kind(&2), ~field: K.Field<F>, +first: F, +second: F, +point: P.Problem.Point<F>, same: A.Algebra.Same(~F, ~field, first, second),
  inside: P.Problem.InContainer<F, field, first, point>) -> P.Problem.InContainer<F, field, second, point>:
  (+forward, +backward) = same
  match inside:
    case P.InContainer{left, right, bottom, top}:
      P.InContainer{left, K.Field.le_transitive(F, field)(P.Problem.x(F, point), first, second, right, forward),
        bottom, K.Field.le_transitive(F, field)(P.Problem.y(F, point), first, second, top, forward)}

def Scaling.factor_spans(~F: Kind(&2), ~field: K.Field<F>, +target: F, +side: F, cancel: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, side, A.Algebra.inverse(~F, ~field, side)), A.Algebra.one(~F, ~field))) ->
  A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side)), side), target):
  +i: F = A.Algebra.inverse(~F, ~field, side)
  C.Certificate.same(~F, ~field, R.Value{target, R.Value{i, R.Value{side, R.NoValues{}}}}, C.MoreExprs{R.Plus{R.Multiply{R.Variable{2n}, R.Variable{1n}}, R.Negate{R.Number{1n}}}, C.NoExprs{}}, C.Both{Scaling.inverse_equation(~F, ~field, side, i, cancel), Unit{}}, R.Multiply{R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Variable{2n}}, R.Variable{0n}, C.MoreTerms{C.Multiple{0n, R.Negate{R.Multiply{R.Number{1n}, R.Variable{0n}}}}, C.NoTerms{}}, C.MoreTerms{C.Multiple{0n, R.Multiply{R.Number{1n}, R.Variable{0n}}}, C.NoTerms{}}, {==}, {==})

def Scaling.factor_not_above(~F: Kind(&2), ~field: K.Field<F>, +target: F, +side: F, +side_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), side),
  spans: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side)), side), target), +below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side)), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, target, side):
  +i: F = A.Algebra.inverse(~F, ~field, side)
  C.Certificate.le(~F, ~field, R.Value{target, R.Value{i, R.Value{side, R.NoValues{}}}}, C.MoreExprs{R.Plus{R.Number{1n}, R.Negate{R.Multiply{R.Variable{0n}, R.Variable{1n}}}}, C.MoreExprs{R.Variable{2n}, C.NoExprs{}}}, C.Both{Scaling.fact(~F, ~field, A.Algebra.mul(~F, ~field, target, i), Scaling.number(~F, ~field, 1n), A.Algebra.le_respects(~F, ~field, A.Algebra.mul(~F, ~field, target, i), A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, target, i), Scaling.number(~F, ~field, 1n), below, A.Algebra.same_reflexive(~F, ~field, A.Algebra.mul(~F, ~field, target, i)), Scaling.one_is_number(~F, ~field))), C.Both{side_nonnegative, Unit{}}}, C.MoreExprs{R.Plus{R.Multiply{R.Multiply{R.Variable{0n}, R.Variable{1n}}, R.Variable{2n}}, R.Negate{R.Variable{0n}}}, C.NoExprs{}}, C.Both{Scaling.equation(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, target, i), side), target, spans), Unit{}}, R.Variable{0n}, R.Variable{2n}, 0n, C.MoreTerms{C.Product{1n, C.MoreIndices{0n, C.MoreIndices{1n, C.NoIndices{}}}, R.Number{1n}}, C.MoreTerms{C.Multiple{0n, R.Number{1n}}, C.NoTerms{}}}, {==})

def Scaling.family_fits(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +factor: F, spans: A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, factor, side), target),
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), factor), positive: A.Algebra.le(~F, ~field, factor, A.Algebra.zero(~F, ~field)) -> Empty, +index: Nat, bound: N.Natural.Le(1n+index, count),
  +point: P.Problem.Point<F>, inside: P.Problem.Containment<F, field, Scaling.scale_center(~F, ~field, factor, S.Packings.squares(F, field, count, side, packing)(index)), point>) ->
  P.Problem.InContainer<F, field, target, point>:
  Scaling.container_to(~F, ~field, A.Algebra.mul(~F, ~field, factor, side), target, point, spans,
    Scaling.scale_fits(~F, ~field, S.Packings.squares(F, field, count, side, packing)(index), side, factor, S.Packings.fits(F, field, count, side, packing)(index, bound), at_least, positive)(point, inside))

def Scaling.family_disjoint(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +factor: F, +greater: O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), factor),
  +left: Nat, +right: Nat, left_bound: N.Natural.Le(1n+left, count), right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.Containment<F, field, Scaling.scale_center(~F, ~field, factor, S.Packings.squares(F, field, count, side, packing)(left)), point>,
  second: P.Problem.Containment<F, field, Scaling.scale_center(~F, ~field, factor, S.Packings.squares(F, field, count, side, packing)(right)), point>) -> Empty:
  S.Packings.disjoint(F, field, count, side, packing)(left, right, left_bound, right_bound, different, Scaling.scale_point(~F, ~field, A.Algebra.inverse(~F, ~field, factor), point),
    Scaling.interior_back(~F, ~field, S.Packings.squares(F, field, count, side, packing)(left), factor, greater, point, first),
    Scaling.interior_back(~F, ~field, S.Packings.squares(F, field, count, side, packing)(right), factor, greater, point, second))

def Scaling.side_positive(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  A.Algebra.le(~F, ~field, side, A.Algebra.zero(~F, ~field)) -> Empty:
  +h_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field)) = Scaling.half_nonnegative(~F, ~field)
  +first: P.Problem.Square<F, field> = S.Packings.squares(F, field, count, side, packing)(0n)
  +inside_0: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, first, A.Algebra.half(~F, ~field), A.Algebra.zero(~F, ~field))> = S.Packings.fits(F, field, count, side, packing)(0n, nonempty, Scaling.point_at(~F, ~field, first, A.Algebra.half(~F, ~field), A.Algebra.zero(~F, ~field)),
    Scaling.containment_at(~F, ~field, first, A.Algebra.half(~F, ~field), A.Algebra.zero(~F, ~field), K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Scaling.negative_half_at_most(~F, ~field, h_nonnegative), h_nonnegative, Scaling.negative_half_below_zero(~F, ~field, h_nonnegative)))
  +inside_1: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, first, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field))> = S.Packings.fits(F, field, count, side, packing)(0n, nonempty, Scaling.point_at(~F, ~field, first, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field)),
    Scaling.containment_at(~F, ~field, first, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.zero(~F, ~field), Scaling.negative_half_at_most(~F, ~field, h_nonnegative), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))), h_nonnegative, Scaling.negative_half_below_zero(~F, ~field, h_nonnegative)))
  +inside_2: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field))> = S.Packings.fits(F, field, count, side, packing)(0n, nonempty, Scaling.point_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field)),
    Scaling.containment_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.half(~F, ~field), h_nonnegative, Scaling.negative_half_below_zero(~F, ~field, h_nonnegative), K.Field.le_reflexive(F, field)(A.Algebra.half(~F, ~field)), Scaling.negative_half_at_most(~F, ~field, h_nonnegative)))
  +inside_3: P.Problem.InContainer<F, field, side, Scaling.point_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)))> = S.Packings.fits(F, field, count, side, packing)(0n, nonempty, Scaling.point_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))),
    Scaling.containment_at(~F, ~field, first, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), h_nonnegative, Scaling.negative_half_below_zero(~F, ~field, h_nonnegative), Scaling.negative_half_at_most(~F, ~field, h_nonnegative), K.Field.le_reflexive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)))))
  nonpositive => Scaling.side_positive_at(~F, ~field, first, side, target, less, inside_0, inside_1, inside_2, inside_3, nonpositive)

def Scaling.side_cancel(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, side, A.Algebra.inverse(~F, ~field, side)), A.Algebra.one(~F, ~field)):
  A.Algebra.mul_inverse(~F, ~field, side, Scaling.side_positive(~F, ~field, ~count, ~side, ~packing, target, less, nonempty))

def Scaling.greater(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side))):
  +factor: F = A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side))
  +side_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), side) = S.Packings.side_nonnegative(F, field, count, side, packing)
  O.FieldOrder.strict_of(~F, ~field, A.Algebra.one(~F, ~field), factor,
    below => O.FieldOrder.lt_of(~F, ~field, side, target, less)(Scaling.factor_not_above(~F, ~field, target, side, side_nonnegative,
      Scaling.factor_spans(~F, ~field, target, side, Scaling.side_cancel(~F, ~field, ~count, ~side, ~packing, target, less, nonempty)), below)))

def Scaling.closed_square(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +index: Nat) -> P.Problem.Square<F, field>:
  Scaling.scale_center(~F, ~field, A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side)), S.Packings.squares(F, field, count, side, packing)(index))

def Scaling.closed_fits(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count),
  +index: Nat, +bound: N.Natural.Le(1n+index, count)) -> Y.Symmetry.Fits(~F, ~field, Scaling.closed_square(~F, ~field, ~count, ~side, ~packing, target, index), target):
  +factor: F = A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side))
  +greater: O.FieldOrder.Strict(~F, ~field, A.Algebra.one(~F, ~field), factor) = Scaling.greater(~F, ~field, ~count, ~side, ~packing, target, less, nonempty)
  +at_least: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), factor) = O.FieldOrder.le_of_lt(~F, ~field, A.Algebra.one(~F, ~field), factor, O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), factor, greater))
  +point => inside => Scaling.family_fits(~F, ~field, ~count, ~side, ~packing, target, factor, Scaling.factor_spans(~F, ~field, target, side, Scaling.side_cancel(~F, ~field, ~count, ~side, ~packing, target, less, nonempty)),
    at_least, below => O.FieldOrder.lt_of(~F, ~field, A.Algebra.one(~F, ~field), factor, greater)(K.Field.le_transitive(F, field)(factor, A.Algebra.zero(~F, ~field), A.Algebra.one(~F, ~field), below, K.Field.zero_le_one(F, field))),
    index, bound, point, inside)

def Scaling.closed_disjoint(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count),
  +left: Nat, +right: Nat, +left_bound: N.Natural.Le(1n+left, count), +right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty) -> @point: P.Problem.Point<F> ->
  P.Problem.Containment<F, field, Scaling.closed_square(~F, ~field, ~count, ~side, ~packing, target, left), point> ->
  P.Problem.Containment<F, field, Scaling.closed_square(~F, ~field, ~count, ~side, ~packing, target, right), point> -> Empty:
  +point => first => second => Scaling.family_disjoint(~F, ~field, ~count, ~side, ~packing, A.Algebra.mul(~F, ~field, target, A.Algebra.inverse(~F, ~field, side)), Scaling.greater(~F, ~field, ~count, ~side, ~packing, target, less, nonempty),
    left, right, left_bound, right_bound, different, point, first, second)

def Scaling.closed_family(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +target: F, +less: O.FieldOrder.Strict(~F, ~field, side, target), +nonempty: N.Natural.Le(1n, count)) ->
  Scaling.ClosedFamily<F, field, count, target>:
  ClosedFamily{
    index => Scaling.closed_square(~F, ~field, ~count, ~side, ~packing, target, index),
    index => bound => Scaling.closed_fits(~F, ~field, ~count, ~side, ~packing, target, less, nonempty, index, bound),
    left => right => left_bound => right_bound => different =>
      Scaling.closed_disjoint(~F, ~field, ~count, ~side, ~packing, target, less, nonempty, left, right, left_bound, right_bound, different)
  }
