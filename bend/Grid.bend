import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./Problem.bend as P

def Grid.unit(~F: Kind(&2), ~field: K.Field<F>) -> F:
  R.FieldRing.of_nat(~F, ~field, 1n)

def Grid.unit_below(~F: Kind(&2), ~field: K.Field<F>,
  unit: A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), Grid.unit(~F, ~field)),
  unit_is_one: A.Algebra.Same(~F, ~field, Grid.unit(~F, ~field), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), A.Algebra.one(~F, ~field)):
  (below, above) = unit
  (unit_below, unit_above) = unit_is_one
  K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), Grid.unit(~F, ~field), A.Algebra.one(~F, ~field), below, unit_below)

def Grid.unit_above(~F: Kind(&2), ~field: K.Field<F>,
  unit: A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), Grid.unit(~F, ~field)),
  unit_is_one: A.Algebra.Same(~F, ~field, Grid.unit(~F, ~field), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field)))):
  (below, above) = unit
  (unit_below, unit_above) = unit_is_one
  K.Field.le_transitive(F, field)(A.Algebra.one(~F, ~field), Grid.unit(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), unit_above, above)

def Grid.unit_sum(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, Grid.unit(~F, ~field), Grid.unit(~F, ~field)), A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))), Grid.unit(~F, ~field)):
  R.FieldRing.equal(~F, ~field, R.NoValues{},
    R.Plus{R.Multiply{R.Number{1n}, R.Number{1n}}, R.Multiply{R.Number{0n}, R.Number{0n}}}, R.Number{1n}, {==})

def Grid.identity_frame(~F: Kind(&2), ~field: K.Field<F>) -> P.Problem.Frame<F, field>:
  P.Frame{Grid.unit(~F, ~field), A.Algebra.zero(~F, ~field),
    Grid.unit_below(~F, ~field, Grid.unit_sum(~F, ~field), R.FieldRing.of_nat_one(~F, ~field)),
    Grid.unit_above(~F, ~field, Grid.unit_sum(~F, ~field), R.FieldRing.of_nat_one(~F, ~field))}

def Grid.square(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F) -> P.Problem.Square<F, field>:
  P.Square{P.Point{x, y}, Grid.identity_frame(~F, ~field)}

def Grid.cell(~F: Kind(&2), ~field: K.Field<F>, +column: Nat, +row: Nat) -> P.Problem.Square<F, field>:
  Grid.square(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, column)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, row)))

def Grid.local_x(~F: Kind(&2), ~field: K.Field<F>, +center: F, +local_x: F, +local_y: F) ->
  A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, center, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, Grid.unit(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, A.Algebra.zero(~F, ~field))))), A.Algebra.add(~F, ~field, center, local_x)):
  R.FieldRing.equal(~F, ~field, R.Value{center, R.Value{local_x, R.Value{local_y, R.NoValues{}}}},
    R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{1n}, R.Number{1n}}, R.Negate{R.Multiply{R.Variable{2n}, R.Number{0n}}}}},
    R.Plus{R.Variable{0n}, R.Variable{1n}}, {==})

def Grid.local_y(~F: Kind(&2), ~field: K.Field<F>, +center: F, +local_x: F, +local_y: F) ->
  A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, center, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, local_y, Grid.unit(~F, ~field)))), A.Algebra.add(~F, ~field, center, local_y)):
  R.FieldRing.equal(~F, ~field, R.Value{center, R.Value{local_x, R.Value{local_y, R.NoValues{}}}},
    R.Plus{R.Variable{0n}, R.Plus{R.Multiply{R.Variable{1n}, R.Number{0n}}, R.Multiply{R.Variable{2n}, R.Number{1n}}}},
    R.Plus{R.Variable{0n}, R.Variable{2n}}, {==})

def Grid.regroup(~F: Kind(&2), ~field: K.Field<F>, +h: F, +k: F, +l: F) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, k), l), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, l), k)):
  R.FieldRing.equal(~F, ~field, R.Value{h, R.Value{k, R.Value{l, R.NoValues{}}}},
    R.Plus{R.Plus{R.Variable{0n}, R.Variable{1n}}, R.Variable{2n}},
    R.Plus{R.Plus{R.Variable{0n}, R.Variable{2n}}, R.Variable{1n}}, {==})

def Grid.coordinate_bounds(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +offset: Nat, +local: F, +coordinate: F,
  offset_small: N.Natural.Le(offset, size),
  at_most: A.Algebra.le(~F, ~field, local, A.Algebra.half(~F, ~field)), at_least: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local),
  below: A.Algebra.le(~F, ~field, coordinate, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, offset)), local)),
  above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, offset)), local), coordinate)) ->
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), coordinate) & A.Algebra.le(~F, ~field, coordinate, R.FieldRing.of_nat(~F, ~field, 1n+size)):
  +h: F = A.Algebra.half(~F, ~field)
  +k: F = R.FieldRing.of_nat(~F, ~field, offset)
  +center: F = A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, k), local)
  +moved: F = A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, local), k)
  (
    K.Field.le_transitive(F, field)(A.Algebra.zero(~F, ~field), center, coordinate,
      A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field)), moved, A.Algebra.zero(~F, ~field), center,
        O.FieldOrder.le_add_both(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, h, local), A.Algebra.zero(~F, ~field), k,
          A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, h), h), A.Algebra.add(~F, ~field, local, h), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, h, local), K.Field.le_add(F, field)(A.Algebra.neg(~F, ~field, h), local, h, at_least),
            A.Algebra.neg_add(~F, ~field, h), A.Algebra.add_commutes(~F, ~field, local, h)),
          O.FieldOrder.zero_le_of_nat(~F, ~field, offset)),
        A.Algebra.add_zero(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.same_symmetric(~F, ~field, center, moved, Grid.regroup(~F, ~field, h, k, local))),
      above),
    K.Field.le_transitive(F, field)(coordinate, center, R.FieldRing.of_nat(~F, ~field, 1n+size), below,
      A.Algebra.le_respects(~F, ~field, moved, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, h), R.FieldRing.of_nat(~F, ~field, size)), center, R.FieldRing.of_nat(~F, ~field, 1n+size),
        O.FieldOrder.le_add_both(~F, ~field, A.Algebra.add(~F, ~field, h, local), A.Algebra.add(~F, ~field, h, h), k, R.FieldRing.of_nat(~F, ~field, size),
          O.FieldOrder.le_add_left(~F, ~field, local, h, h, at_most),
          O.FieldOrder.of_nat_le(~F, ~field, offset, size, offset_small)),
        A.Algebra.same_symmetric(~F, ~field, center, moved, Grid.regroup(~F, ~field, h, k, local)),
        A.Algebra.add_respects_left(~F, ~field, A.Algebra.add(~F, ~field, h, h), A.Algebra.one(~F, ~field), R.FieldRing.of_nat(~F, ~field, size), K.Field.half_double(F, field))))
  )

def Grid.in_container(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +point: P.Problem.Point<F>,
  x_bounds: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.x(F, point)) & A.Algebra.le(~F, ~field, P.Problem.x(F, point), R.FieldRing.of_nat(~F, ~field, 1n+size)),
  y_bounds: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.y(F, point)) & A.Algebra.le(~F, ~field, P.Problem.y(F, point), R.FieldRing.of_nat(~F, ~field, 1n+size))) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(~F, ~field, 1n+size), point>:
  (left, right) = x_bounds
  (bottom, top) = y_bounds
  P.InContainer{left, right, bottom, top}

def Grid.fits(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +column: Nat, +row: Nat, column_small: N.Natural.Le(column, size), row_small: N.Natural.Le(row, size),
  +point: P.Problem.Point<F>, containment: P.Problem.Containment<F, field, Grid.cell(~F, ~field, column, row), point>) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(~F, ~field, 1n+size), point>:
  match containment:
    case P.Containment{+local_x, +local_y, x_at_most, x_at_least, y_at_most, y_at_least, x_is_below, x_is_above, y_is_below, y_is_above}:
      +center_x: F = A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, column))
      +center_y: F = A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, row))
      +x: F = P.Problem.x(F, point)
      +y: F = P.Problem.y(F, point)
      +offset_x: F = A.Algebra.add(~F, ~field, center_x, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, Grid.unit(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, local_y, A.Algebra.zero(~F, ~field)))))
      +offset_y: F = A.Algebra.add(~F, ~field, center_y, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, local_x, A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, local_y, Grid.unit(~F, ~field))))
      Grid.in_container(~F, ~field, size, point,
        Grid.coordinate_bounds(~F, ~field, size, column, local_x, x, column_small, x_at_most, x_at_least,
          A.Algebra.le_respects(~F, ~field, x, offset_x, x, A.Algebra.add(~F, ~field, center_x, local_x), x_is_below, A.Algebra.same_reflexive(~F, ~field, x), Grid.local_x(~F, ~field, center_x, local_x, local_y)),
          A.Algebra.le_respects(~F, ~field, offset_x, x, A.Algebra.add(~F, ~field, center_x, local_x), x, x_is_above, Grid.local_x(~F, ~field, center_x, local_x, local_y), A.Algebra.same_reflexive(~F, ~field, x))),
        Grid.coordinate_bounds(~F, ~field, size, row, local_y, y, row_small, y_at_most, y_at_least,
          A.Algebra.le_respects(~F, ~field, y, offset_y, y, A.Algebra.add(~F, ~field, center_y, local_y), y_is_below, A.Algebra.same_reflexive(~F, ~field, y), Grid.local_y(~F, ~field, center_y, local_x, local_y)),
          A.Algebra.le_respects(~F, ~field, offset_y, y, A.Algebra.add(~F, ~field, center_y, local_y), y, y_is_above, Grid.local_y(~F, ~field, center_y, local_x, local_y), A.Algebra.same_reflexive(~F, ~field, y))))

def Grid.shift_out(~F: Kind(&2), ~field: K.Field<F>, +a: F, +gap: F, +local: F, +h: F) ->
  A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, gap), local), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, gap))), local) & A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, h), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, gap))), A.Algebra.add(~F, ~field, h, A.Algebra.neg(~F, ~field, gap))):
  (
    R.FieldRing.equal(~F, ~field, R.Value{a, R.Value{gap, R.Value{local, R.NoValues{}}}},
      R.Plus{R.Plus{R.Plus{R.Variable{0n}, R.Variable{1n}}, R.Variable{2n}}, R.Plus{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{1n}}}},
      R.Variable{2n}, {==}),
    R.FieldRing.equal(~F, ~field, R.Value{a, R.Value{gap, R.Value{h, R.NoValues{}}}},
      R.Plus{R.Plus{R.Variable{0n}, R.Variable{2n}}, R.Plus{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{1n}}}},
      R.Plus{R.Variable{2n}, R.Negate{R.Variable{1n}}}, {==})
  )

def Grid.half_less_one(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field))), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))):
  +h: F = A.Algebra.half(~F, ~field)
  A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, h, A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field))), A.Algebra.add(~F, ~field, h, A.Algebra.neg(~F, ~field, A.Algebra.add(~F, ~field, h, h))), A.Algebra.neg(~F, ~field, h),
    A.Algebra.add_respects_right(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.add(~F, ~field, h, h)), h,
      A.Algebra.neg_respects(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, h, h), A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, h, h), A.Algebra.one(~F, ~field), K.Field.half_double(F, field)))),
    R.FieldRing.equal(~F, ~field, R.Value{h, R.NoValues{}},
      R.Plus{R.Variable{0n}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{0n}}}}, R.Negate{R.Variable{0n}}, {==}))

def Grid.squeeze(~F: Kind(&2), ~field: K.Field<F>, +a: F, +local: F, +other_local: F,
  chain: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), other_local), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field))),
  shifted: A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), other_local), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))), other_local) &
    A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))),
  other_above: A.Algebra.le(~F, ~field, other_local, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field))) -> Empty) -> Empty:
  (low, high) = shifted
  other_above(
    A.Algebra.le_respects(~F, ~field,
      A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), other_local), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))),
      other_local, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)),
      K.Field.le_add(F, field)(A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), other_local), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field))), chain),
      low,
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field)))), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.one(~F, ~field))), A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), high, Grid.half_less_one(~F, ~field))))

def Grid.separated_x(~F: Kind(&2), ~field: K.Field<F>, +a: F, +a_y: F, +b: F, +b_y: F, gap: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), b), +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Grid.square(~F, ~field, a, a_y), point>,
  second: P.Problem.InteriorContainment<F, field, Grid.square(~F, ~field, b, b_y), point>) -> Empty:
  match first second:
    case P.InteriorContainment{+first_x, +first_y, first_x_below, first_x_above, first_y_below, first_y_above, first_is_below, first_is_above, first_y_is_below, first_y_is_above}
      P.InteriorContainment{+second_x, +second_y, second_x_below, second_x_above, second_y_below, second_y_above, second_is_below, second_is_above, second_y_is_below, second_y_is_above}:
      +x: F = P.Problem.x(F, point)
      +first_offset: F = A.Algebra.add(~F, ~field, a, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, first_x, Grid.unit(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, first_y, A.Algebra.zero(~F, ~field)))))
      +second_offset: F = A.Algebra.add(~F, ~field, b, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, second_x, Grid.unit(~F, ~field)), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, second_y, A.Algebra.zero(~F, ~field)))))
      Grid.squeeze(~F, ~field, a, first_x, second_x,
        K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), second_x), A.Algebra.add(~F, ~field, b, second_x), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
          K.Field.le_add(F, field)(A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), b, second_x, gap),
          K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, b, second_x), x, A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
            A.Algebra.le_respects(~F, ~field, second_offset, x, A.Algebra.add(~F, ~field, b, second_x), x, second_is_above, Grid.local_x(~F, ~field, b, second_x, second_y), A.Algebra.same_reflexive(~F, ~field, x)),
            K.Field.le_transitive(F, field)(x, A.Algebra.add(~F, ~field, a, first_x), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
              A.Algebra.le_respects(~F, ~field, x, first_offset, x, A.Algebra.add(~F, ~field, a, first_x), first_is_below, A.Algebra.same_reflexive(~F, ~field, x), Grid.local_x(~F, ~field, a, first_x, first_y)),
              O.FieldOrder.le_add_left(~F, ~field, first_x, A.Algebra.half(~F, ~field), a, O.FieldOrder.le_of_lt(~F, ~field, first_x, A.Algebra.half(~F, ~field), first_x_below))))),
        Grid.shift_out(~F, ~field, a, A.Algebra.one(~F, ~field), second_x, A.Algebra.half(~F, ~field)),
        second_x_above)

def Grid.separated_y(~F: Kind(&2), ~field: K.Field<F>, +a_x: F, +a: F, +b_x: F, +b: F, gap: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), b), +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Grid.square(~F, ~field, a_x, a), point>,
  second: P.Problem.InteriorContainment<F, field, Grid.square(~F, ~field, b_x, b), point>) -> Empty:
  match first second:
    case P.InteriorContainment{+first_x, +first_y, first_x_below, first_x_above, first_y_below, first_y_above, first_x_is_below, first_x_is_above, first_is_below, first_is_above}
      P.InteriorContainment{+second_x, +second_y, second_x_below, second_x_above, second_y_below, second_y_above, second_x_is_below, second_x_is_above, second_is_below, second_is_above}:
      +y: F = P.Problem.y(F, point)
      +first_offset: F = A.Algebra.add(~F, ~field, a, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, first_x, A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, first_y, Grid.unit(~F, ~field))))
      +second_offset: F = A.Algebra.add(~F, ~field, b, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, second_x, A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, second_y, Grid.unit(~F, ~field))))
      Grid.squeeze(~F, ~field, a, first_y, second_y,
        K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), second_y), A.Algebra.add(~F, ~field, b, second_y), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
          K.Field.le_add(F, field)(A.Algebra.add(~F, ~field, a, A.Algebra.one(~F, ~field)), b, second_y, gap),
          K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, b, second_y), y, A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
            A.Algebra.le_respects(~F, ~field, second_offset, y, A.Algebra.add(~F, ~field, b, second_y), y, second_is_above, Grid.local_y(~F, ~field, b, second_x, second_y), A.Algebra.same_reflexive(~F, ~field, y)),
            K.Field.le_transitive(F, field)(y, A.Algebra.add(~F, ~field, a, first_y), A.Algebra.add(~F, ~field, a, A.Algebra.half(~F, ~field)),
              A.Algebra.le_respects(~F, ~field, y, first_offset, y, A.Algebra.add(~F, ~field, a, first_y), first_is_below, A.Algebra.same_reflexive(~F, ~field, y), Grid.local_y(~F, ~field, a, first_x, first_y)),
              O.FieldOrder.le_add_left(~F, ~field, first_y, A.Algebra.half(~F, ~field), a, O.FieldOrder.le_of_lt(~F, ~field, first_y, A.Algebra.half(~F, ~field), first_y_below))))),
        Grid.shift_out(~F, ~field, a, A.Algebra.one(~F, ~field), second_y, A.Algebra.half(~F, ~field)),
        second_y_above)

def Grid.offset_gap(~F: Kind(&2), ~field: K.Field<F>, +first: Nat, +second: Nat, apart: N.Natural.Le(1n+first, second)) ->
  A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, first)), A.Algebra.one(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, second))):
  +h: F = A.Algebra.half(~F, ~field)
  +k: F = R.FieldRing.of_nat(~F, ~field, first)
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, h, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), k)), A.Algebra.add(~F, ~field, h, R.FieldRing.of_nat(~F, ~field, second)), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, h, k), A.Algebra.one(~F, ~field)), A.Algebra.add(~F, ~field, h, R.FieldRing.of_nat(~F, ~field, second)),
    O.FieldOrder.le_add_left(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n+first), R.FieldRing.of_nat(~F, ~field, second), h, O.FieldOrder.of_nat_le(~F, ~field, 1n+first, second, apart)),
    R.FieldRing.equal(~F, ~field, R.Value{h, R.Value{k, R.Value{A.Algebra.one(~F, ~field), R.NoValues{}}}},
      R.Plus{R.Variable{0n}, R.Plus{R.Variable{2n}, R.Variable{1n}}},
      R.Plus{R.Plus{R.Variable{0n}, R.Variable{1n}}, R.Variable{2n}}, {==}),
    A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, h, R.FieldRing.of_nat(~F, ~field, second))))
