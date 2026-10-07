import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/Natural.bend as N
import ./Problem.bend as P

law grid_baseline:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~size: Nat
  for ~count: Nat
  for +fits: N.Natural.Le(count, Nat.mul(1n+size, 1n+size))
  P.Problem.Packing<F, field, count, R.FieldRing.of_nat(~F, ~field, 1n+size)>

law exact_1_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 1n, R.FieldRing.of_nat(~F, ~field, 1n)>

law exact_1_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(1n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n), side)

law exact_2_goebel_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 2n, R.FieldRing.of_nat(~F, ~field, 2n)>

law exact_2_goebel_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(2n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), side)

law exact_3_goebel_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 3n, R.FieldRing.of_nat(~F, ~field, 2n)>

law exact_3_goebel_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(3n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), side)

law exact_4_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 4n, R.FieldRing.of_nat(~F, ~field, 2n)>

law exact_4_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(4n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), side)

law exact_6_kearney_shiu_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 6n, R.FieldRing.of_nat(~F, ~field, 3n)>

law exact_6_kearney_shiu_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(6n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 3n), side)

law exact_7_friedman_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 7n, R.FieldRing.of_nat(~F, ~field, 3n)>

law exact_7_friedman_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(7n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 3n), side)

law exact_8_friedman_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 8n, R.FieldRing.of_nat(~F, ~field, 3n)>

law exact_8_friedman_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(8n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 3n), side)

law exact_9_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 9n, R.FieldRing.of_nat(~F, ~field, 3n)>

law exact_9_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(9n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 3n), side)
