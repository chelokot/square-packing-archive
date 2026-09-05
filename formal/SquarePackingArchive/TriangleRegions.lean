import SquarePackingArchive.Triangle

namespace SquarePackingArchive

def Point.orientedArea (first second third : Point) : ℝ :=
  (second.x - first.x) * (third.y - first.y) -
    (second.y - first.y) * (third.x - first.x)

lemma PlacedSquare.contains_triangleVertex_of_cross_nonnegative
    (square : PlacedSquare) (first second third : Point)
    (triangle_positive : 0 < Point.orientedArea first second third)
    (first_half_plane : 0 ≤ Point.orientedArea first second square.center)
    (second_half_plane : 0 ≤ Point.orientedArea second third square.center)
    (third_half_plane : 0 ≤ Point.orientedArea third first square.center)
    (first_second_distance :
      (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2 ≤ 1)
    (first_third_distance :
      (first.x - third.x) ^ 2 + (first.y - third.y) ^ 2 ≤ 1)
    (second_third_distance :
      (second.x - third.x) ^ 2 + (second.y - third.y) ^ 2 ≤ 1) :
    square.Contains first ∨ square.Contains second ∨ square.Contains third := by
  apply square.contains_triangleVertex first second third
    (Point.orientedArea second third square.center / Point.orientedArea first second third)
    (Point.orientedArea third first square.center / Point.orientedArea first second third)
    (Point.orientedArea first second square.center / Point.orientedArea first second third)
    (div_nonneg second_half_plane triangle_positive.le)
    (div_nonneg third_half_plane triangle_positive.le)
    (div_nonneg first_half_plane triangle_positive.le)
    _ _ _ first_second_distance first_third_distance second_third_distance
  · field_simp
    dsimp [Point.orientedArea]
    ring
  · field_simp
    dsimp [Point.orientedArea]
    ring
  · field_simp
    dsimp [Point.orientedArea]
    ring

lemma PlacedSquare.contains_indexed_triangleVertex
    (square : PlacedSquare) {pointCount : ℕ}
    (points : Fin pointCount → Point) (vertices : Fin 3 → Fin pointCount)
    (valid :
      0 < Point.orientedArea (points (vertices 0)) (points (vertices 1)) (points (vertices 2)) ∧
      ((points (vertices 0)).x - (points (vertices 1)).x) ^ 2 +
        ((points (vertices 0)).y - (points (vertices 1)).y) ^ 2 ≤ 1 ∧
      ((points (vertices 0)).x - (points (vertices 2)).x) ^ 2 +
        ((points (vertices 0)).y - (points (vertices 2)).y) ^ 2 ≤ 1 ∧
      ((points (vertices 1)).x - (points (vertices 2)).x) ^ 2 +
        ((points (vertices 1)).y - (points (vertices 2)).y) ^ 2 ≤ 1)
    (first_halfplane : 0 ≤ Point.orientedArea
      (points (vertices 0)) (points (vertices 1)) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (points (vertices 1)) (points (vertices 2)) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (points (vertices 2)) (points (vertices 0)) square.center) :
    ∃ index, square.Contains (points index) := by
  obtain ⟨orientation, first_edge, second_edge, third_edge⟩ := valid
  rcases square.contains_triangleVertex_of_cross_nonnegative _ _ _ orientation
    first_halfplane second_halfplane third_halfplane first_edge second_edge third_edge with
      first_inside | second_inside | third_inside
  · exact ⟨vertices 0, first_inside⟩
  · exact ⟨vertices 1, second_inside⟩
  · exact ⟨vertices 2, third_inside⟩

end SquarePackingArchive
