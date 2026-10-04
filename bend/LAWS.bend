import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldRing.bend as R
import ./Problem.bend as P
import ./Geometry.bend as G
import ./Symmetry.bend as Y

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

law translate_contains:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +horizontal: F
  for +vertical: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.Containment<F, field, square, point>
  P.Problem.Containment<F, field, Y.Symmetry.translate(~F, ~field, horizontal, vertical, square), Y.Symmetry.translate_point(~F, ~field, horizontal, vertical, point)>

law translate_interior:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +horizontal: F
  for +vertical: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.InteriorContainment<F, field, square, point>
  P.Problem.InteriorContainment<F, field, Y.Symmetry.translate(~F, ~field, horizontal, vertical, square), Y.Symmetry.translate_point(~F, ~field, horizontal, vertical, point)>

law swap_contains:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.Containment<F, field, square, point>
  P.Problem.Containment<F, field, Y.Symmetry.swap(~F, ~field, square), Y.Symmetry.swap_point(F, point)>

law swap_interior:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.InteriorContainment<F, field, square, point>
  P.Problem.InteriorContainment<F, field, Y.Symmetry.swap(~F, ~field, square), Y.Symmetry.swap_point(F, point)>

law turn_contains:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.Containment<F, field, square, point>
  P.Problem.Containment<F, field, Y.Symmetry.turn(~F, ~field, square), point>

law turn_interior:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.InteriorContainment<F, field, square, point>
  P.Problem.InteriorContainment<F, field, Y.Symmetry.turn(~F, ~field, square), point>

law reflect_x_contains:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +sum: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.Containment<F, field, square, point>
  P.Problem.Containment<F, field, Y.Symmetry.reflect_x(~F, ~field, sum, square), Y.Symmetry.reflect_x_point(~F, ~field, sum, point)>

law reflect_x_interior:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +sum: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.InteriorContainment<F, field, square, point>
  P.Problem.InteriorContainment<F, field, Y.Symmetry.reflect_x(~F, ~field, sum, square), Y.Symmetry.reflect_x_point(~F, ~field, sum, point)>

law reflect_y_contains:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +sum: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.Containment<F, field, square, point>
  P.Problem.Containment<F, field, Y.Symmetry.reflect_y(~F, ~field, sum, square), Y.Symmetry.reflect_y_point(~F, ~field, sum, point)>

law reflect_y_interior:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +sum: F
  for +square: P.Problem.Square<F, field>
  for +point: P.Problem.Point<F>
  for inside: P.Problem.InteriorContainment<F, field, square, point>
  P.Problem.InteriorContainment<F, field, Y.Symmetry.reflect_y(~F, ~field, sum, square), Y.Symmetry.reflect_y_point(~F, ~field, sum, point)>
