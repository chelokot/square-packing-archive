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

law exact_5_goebel_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~root: F
  for +root_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, root, root), R.FieldRing.of_nat(~F, ~field, 2n))
  for +root_above: A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), A.Algebra.mul(~F, ~field, root, root))
  for +root_sign: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), root)
  P.Problem.Packing<F, field, 5n, A.Algebra.add(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), A.Algebra.mul(~F, ~field, root, A.Algebra.half(~F, ~field)))>

law exact_5_goebel_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for ~root: F
  for +root_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, root, root), R.FieldRing.of_nat(~F, ~field, 2n))
  for +root_above: A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), A.Algebra.mul(~F, ~field, root, root))
  for +root_sign: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), root)
  for +at_least: N.Natural.Le(5n, count)
  A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), A.Algebra.mul(~F, ~field, root, A.Algebra.half(~F, ~field))), side)

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

law exact_16_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 16n, R.FieldRing.of_nat(~F, ~field, 4n)>

law exact_16_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(16n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 4n), side)

law exact_25_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 25n, R.FieldRing.of_nat(~F, ~field, 5n)>

law exact_25_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(25n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 5n), side)

law exact_36_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 36n, R.FieldRing.of_nat(~F, ~field, 6n)>

law exact_36_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(36n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 6n), side)

law exact_49_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 49n, R.FieldRing.of_nat(~F, ~field, 7n)>

law exact_49_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(49n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 7n), side)

law exact_64_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 64n, R.FieldRing.of_nat(~F, ~field, 8n)>

law exact_64_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(64n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 8n), side)

law exact_81_grid_upper:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 81n, R.FieldRing.of_nat(~F, ~field, 9n)>

law exact_81_grid_lower:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +at_least: N.Natural.Le(81n, count)
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 9n), side)
