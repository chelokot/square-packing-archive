import Base
import ./LAWS.bend as Laws
import ./MANIFEST.bend as Manifest
import ./Grids.bend as Gs
import ./Small.bend as Sm
import ./Geometry.bend as G
import ./Symmetry.bend as Y
import ./Packings.bend as Q
import ./bend-math/FieldRing.bend as R
import ./bend-math/Natural.bend as N
import ./Scaling.bend as Z
import ./StromquistSix.bend as Six
import ./Chords.bend as Ch

def Manifest.grid_baseline(F, field, size, count, fits):
  Gs.Grids.packing(~F, ~field, size, count, fits)

def Manifest.exact_1_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 0n, 1n, Unit{})

def Manifest.exact_1_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 1n, at_least)

def Manifest.exact_2_goebel_upper(F, field):
  Gs.Grids.packing(~F, ~field, 1n, 2n, Unit{})

def Manifest.exact_2_goebel_lower(F, field, count, side, packing, at_least):
  Sm.Small.lower_bound_two(~F, ~field, ~count, ~side, ~packing, at_least)

def Manifest.exact_3_goebel_upper(F, field):
  Gs.Grids.packing(~F, ~field, 1n, 3n, Unit{})

def Manifest.exact_3_goebel_lower(F, field, count, side, packing, at_least):
  Sm.Small.lower_bound_two(~F, ~field, ~count, ~side, ~packing, N.Natural.le_transitive(2n, 3n, count, Unit{}, at_least))

def Manifest.exact_4_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 1n, 4n, Unit{})

def Manifest.exact_4_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 2n, at_least)

def Manifest.exact_6_kearney_shiu_upper(F, field):
  Gs.Grids.packing(~F, ~field, 2n, 6n, Unit{})

def Manifest.exact_6_kearney_shiu_lower(F, field, count, side, packing, at_least):
  Six.StromquistSix.lower_bound(~F, ~field, ~count, ~side, ~packing, at_least)

def Manifest.exact_7_friedman_upper(F, field):
  Gs.Grids.packing(~F, ~field, 2n, 7n, Unit{})

def Manifest.exact_7_friedman_lower(F, field, count, side, packing, at_least):
  Six.StromquistSix.lower_bound(~F, ~field, ~count, ~side, ~packing, N.Natural.le_transitive(6n, 7n, count, Unit{}, at_least))

def Manifest.exact_8_friedman_upper(F, field):
  Gs.Grids.packing(~F, ~field, 2n, 8n, Unit{})

def Manifest.exact_8_friedman_lower(F, field, count, side, packing, at_least):
  Six.StromquistSix.lower_bound(~F, ~field, ~count, ~side, ~packing, N.Natural.le_transitive(6n, 8n, count, Unit{}, at_least))

def Manifest.exact_9_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 2n, 9n, Unit{})

def Manifest.exact_9_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 3n, at_least)

def Manifest.exact_16_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 3n, 16n, Unit{})

def Manifest.exact_16_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 4n, at_least)

def Manifest.exact_25_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 4n, 25n, Unit{})

def Manifest.exact_25_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 5n, at_least)

def Manifest.exact_36_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 5n, 36n, Unit{})

def Manifest.exact_36_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 6n, at_least)

def Manifest.exact_49_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 6n, 49n, Unit{})

def Manifest.exact_49_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 7n, at_least)

def Manifest.exact_64_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 7n, 64n, Unit{})

def Manifest.exact_64_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 8n, at_least)

def Manifest.exact_81_grid_upper(F, field):
  Gs.Grids.packing(~F, ~field, 8n, 81n, Unit{})

def Manifest.exact_81_grid_lower(F, field, count, side, packing, at_least):
  Ch.Chords.lower_bound(~F, ~field, ~count, ~side, ~packing, 9n, at_least)

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

def Laws.vertical_chords_fit_the_side(F, field, count, side, packing, x):
  Ch.Chords.covered(~F, ~field, ~count, ~side, ~packing, x)

def Laws.squares_fit_by_area(F, field, count, side, packing):
  Ch.Chords.count_bound(~F, ~field, ~count, ~side, ~packing)
