import Base
import ./LAWS.bend as Laws
import ./Square1.bend as S1
import ./Square4.bend as S4
import ./Square6.bend as S
import ./Square9.bend as S9
import ./Small.bend as Sm
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Packings.bend as Q
import ./Scaling.bend as Z
import ./StromquistSix.bend as Six

def Laws.square1_has_packing_at_one(F, field):
  S1.Square1.packing(~F, ~field)

def Laws.square1_lower_bound(F, field, count, side, packing, one):
  Sm.Small.lower_bound_one(~F, ~field, ~count, ~side, ~packing, one)

def Laws.square4_has_packing_at_two(F, field):
  S4.Square4.packing(~F, ~field)

def Laws.square2_lower_bound(F, field, count, side, packing, two):
  Sm.Small.lower_bound_two(~F, ~field, ~count, ~side, ~packing, two)

def Laws.square6_has_packing_at_three(F, field):
  S.Square6.packing(~F, ~field)

def Laws.square6_lower_bound(F, field, count, side, packing, six):
  Six.StromquistSix.lower_bound(~F, ~field, ~count, ~side, ~packing, six)

def Laws.square9_has_packing_at_three(F, field):
  S9.Square9.packing(~F, ~field)

def Laws.fewer_squares(F, field, count, side, packing, fewer, at_most):
  Q.Packings.restrict(~F, ~field, ~count, ~side, ~packing, ~fewer, at_most)

def Laws.contains_iff_local_coordinates_forward(F, field, square, point, containment):
  G.Geometry.contains_local(~F, ~field, square, point, containment)

def Laws.contains_iff_local_coordinates_backward(F, field, square, point, local):
  G.Geometry.local_contains(~F, ~field, square, point, local)

def Laws.interior_iff_local_coordinates_forward(F, field, square, point, interior):
  G.Geometry.interior_local(~F, ~field, square, point, interior)

def Laws.interior_iff_local_coordinates_backward(F, field, square, point, local):
  G.Geometry.local_interior(~F, ~field, square, point, local)

def Laws.translate_contains(F, field, horizontal, vertical, square, point, inside):
  Y.Symmetry.translate_contains(~F, ~field, horizontal, vertical, square, point, inside)

def Laws.translate_interior(F, field, horizontal, vertical, square, point, inside):
  Y.Symmetry.translate_interior(~F, ~field, horizontal, vertical, square, point, inside)

def Laws.swap_contains(F, field, square, point, inside):
  Y.Symmetry.swap_contains(~F, ~field, square, point, inside)

def Laws.swap_interior(F, field, square, point, inside):
  Y.Symmetry.swap_interior(~F, ~field, square, point, inside)

def Laws.turn_contains(F, field, square, point, inside):
  Y.Symmetry.turn_contains(~F, ~field, square, point, inside)

def Laws.turn_interior(F, field, square, point, inside):
  Y.Symmetry.turn_interior(~F, ~field, square, point, inside)

def Laws.reflect_x_contains(F, field, sum, square, point, inside):
  Y.Symmetry.reflect_x_contains(~F, ~field, sum, square, point, inside)

def Laws.reflect_x_interior(F, field, sum, square, point, inside):
  Y.Symmetry.reflect_x_interior(~F, ~field, sum, square, point, inside)

def Laws.reflect_y_contains(F, field, sum, square, point, inside):
  Y.Symmetry.reflect_y_contains(~F, ~field, sum, square, point, inside)

def Laws.reflect_y_interior(F, field, sum, square, point, inside):
  Y.Symmetry.reflect_y_interior(~F, ~field, sum, square, point, inside)

def Laws.swap_fits(F, field, square, side, fits):
  Y.Symmetry.swap_fits(~F, ~field, square, side, fits)

def Laws.swap_fits_back(F, field, square, side, fits):
  Y.Symmetry.swap_fits_back(~F, ~field, square, side, fits)

def Laws.reflect_x_fits(F, field, square, side, fits):
  Y.Symmetry.reflect_x_fits(~F, ~field, square, side, fits)

def Laws.reflect_x_fits_back(F, field, square, side, fits):
  Y.Symmetry.reflect_x_fits_back(~F, ~field, square, side, fits)

def Laws.reflect_y_fits(F, field, square, side, fits):
  Y.Symmetry.reflect_y_fits(~F, ~field, square, side, fits)

def Laws.reflect_y_fits_back(F, field, square, side, fits):
  Y.Symmetry.reflect_y_fits_back(~F, ~field, square, side, fits)

def Laws.turn_fits(F, field, square, side, fits):
  Y.Symmetry.turn_fits(~F, ~field, square, side, fits)

def Laws.turn_fits_back(F, field, square, side, fits):
  Y.Symmetry.turn_fits_back(~F, ~field, square, side, fits)

def Laws.first_quadrant_fits(F, field, square, side, fits):
  Y.Symmetry.first_quadrant_fits(~F, ~field, square, side, fits)

def Laws.first_quadrant_fits_back(F, field, square, side, fits):
  Y.Symmetry.first_quadrant_fits_back(~F, ~field, square, side, fits)

def Laws.first_quadrant_signs(F, field, square):
  Y.Symmetry.first_quadrant_signs(~F, ~field, square)

def Laws.swap_packing(F, field, count, side, packing):
  Q.Packings.swap(~F, ~field, ~count, ~side, ~packing)

def Laws.reflect_x_packing(F, field, count, side, packing):
  Q.Packings.reflect_x(~F, ~field, ~count, ~side, ~packing)

def Laws.reflect_y_packing(F, field, count, side, packing):
  Q.Packings.reflect_y(~F, ~field, ~count, ~side, ~packing)

def Laws.closed_disjoint_family_in_larger_container(F, field, count, side, packing, target, less, nonempty):
  Z.Scaling.closed_family(~F, ~field, ~count, ~side, ~packing, target, less, nonempty)
