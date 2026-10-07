import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldRing.bend as R
import ./Problem.bend as P
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Packings.bend as S
import ./Scaling.bend as Z
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./bend-math/Certificate.bend as C
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/Intervals.bend as I
import ./Chords.bend as Ch

law fewer_squares:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for ~fewer: Nat
  for +at_most: N.Natural.Le(fewer, count)
  P.Problem.Packing<F, field, fewer, side>

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

law swap_fits:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, square, side)
  Y.Symmetry.Fits(~F, ~field, Y.Symmetry.swap(~F, ~field, square), side)

law swap_fits_back:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, Y.Symmetry.swap(~F, ~field, square), side)
  Y.Symmetry.Fits(~F, ~field, square, side)

law reflect_x_fits:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, square, side)
  Y.Symmetry.Fits(~F, ~field, Y.Symmetry.reflect_x(~F, ~field, side, square), side)

law reflect_x_fits_back:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, Y.Symmetry.reflect_x(~F, ~field, side, square), side)
  Y.Symmetry.Fits(~F, ~field, square, side)

law reflect_y_fits:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, square, side)
  Y.Symmetry.Fits(~F, ~field, Y.Symmetry.reflect_y(~F, ~field, side, square), side)

law reflect_y_fits_back:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, Y.Symmetry.reflect_y(~F, ~field, side, square), side)
  Y.Symmetry.Fits(~F, ~field, square, side)

law turn_fits:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, square, side)
  Y.Symmetry.Fits(~F, ~field, Y.Symmetry.turn(~F, ~field, square), side)

law turn_fits_back:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, Y.Symmetry.turn(~F, ~field, square), side)
  Y.Symmetry.Fits(~F, ~field, square, side)

law first_quadrant_fits:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, square, side)
  Y.Symmetry.Fits(~F, ~field, Y.Symmetry.first_quadrant(~F, ~field, square), side)

law first_quadrant_fits_back:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  for +side: F
  for fits: Y.Symmetry.Fits(~F, ~field, Y.Symmetry.first_quadrant(~F, ~field, square), side)
  Y.Symmetry.Fits(~F, ~field, square, side)

law first_quadrant_signs:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for +square: P.Problem.Square<F, field>
  C.Certificate.Both<K.Field.le(F, field)(K.Field.zero(F, field), P.Problem.cosine(F, field, Y.Symmetry.first_quadrant(~F, ~field, square))),
    K.Field.le(F, field)(K.Field.zero(F, field), P.Problem.sine(F, field, Y.Symmetry.first_quadrant(~F, ~field, square)))>

law swap_packing:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  P.Problem.Packing<F, field, count, side>

law reflect_x_packing:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  P.Problem.Packing<F, field, count, side>

law reflect_y_packing:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  P.Problem.Packing<F, field, count, side>

law closed_disjoint_family_in_larger_container:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +target: F
  for +less: O.FieldOrder.Strict(~F, ~field, side, target)
  for +nonempty: N.Natural.Le(1n, count)
  Z.Scaling.ClosedFamily<F, field, count, target>

law vertical_chords_fit_the_side:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  for +x: F
  A.Algebra.le(~F, ~field, I.Intervals.total(~F, ~field, Ch.Chords.chords(~F, ~field, ~count, ~side, ~packing, x, count)),
    I.Intervals.minus(~F, ~field, side, A.Algebra.zero(~F, ~field)))

law squares_fit_by_area:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, count), A.Algebra.mul(~F, ~field, side, side))
