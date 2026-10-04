import Base
import ./LAWS.bend as Laws
import ./Square6.bend as S
import ./Geometry.bend as G
import ./Symmetry.bend as Y

def Laws.square6_has_packing_at_three(F, field):
  S.Square6.packing(~F, ~field)

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
