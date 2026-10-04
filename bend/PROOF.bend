import Base
import ./LAWS.bend as Laws
import ./Square6.bend as S
import ./Geometry.bend as G

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
