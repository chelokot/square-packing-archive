import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldRing.bend as R
import ./Problem.bend as P
import ./Geometry.bend as G

law square6_has_packing_at_three:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, 6n, R.FieldRing.of_nat(~F, ~field, 3n)>

law contains_iff_local_coordinates_forward:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for containment: P.Problem.Containment<F, field, square, point>
  G.Geometry.Local<F, field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point)>

law contains_iff_local_coordinates_backward:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for local: G.Geometry.Local<F, field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point)>
  P.Problem.Containment<F, field, square, point>

law interior_iff_local_coordinates_forward:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for interior: P.Problem.InteriorContainment<F, field, square, point>
  G.Geometry.StrictLocal<F, field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point)>

law interior_iff_local_coordinates_backward:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for local: G.Geometry.StrictLocal<F, field, G.Geometry.local_x(~F, ~field, square, point), G.Geometry.local_y(~F, ~field, square, point)>
  P.Problem.InteriorContainment<F, field, square, point>
