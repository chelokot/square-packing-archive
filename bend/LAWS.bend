import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldRing.bend as R
import ./Problem.bend as P

law square6_has_packing_at_three:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 6n, R.FieldRing.of_nat(~F, ~field, 3n)>
