import SquarePackingArchive.StromquistRingSideExterior

namespace SquarePackingArchive.Stromquist.TenPoints

def ringRotation (turns : Fin 4) : Fin 8 := ⟨2 * turns.val, by omega⟩

lemma ringSquareTransform_center (index : Fin 8) (square : PlacedSquare) :
    (ringSquareTransform index square).center = ringTransform index square.center := by
  fin_cases index <;> rfl

lemma ringTransform_ringCenter (index : Fin 8) :
    ringTransform index ringCenter = ringCenter := by
  fin_cases index <;>
    norm_num [ringTransform, ringCenter, side, Point.swap, Point.reflectX, Point.reflectY] <;> ring_nf

lemma ringInverse_contains (index : Fin 8) (square : PlacedSquare) (point : Point) :
    (ringSquareTransform (ringInverse index) square).Contains point ↔
      square.Contains (ringTransform index point) := by
  have inverse_inverse := (by decide : ∀ index, ringInverse (ringInverse index) = index) index
  have equivalence := ringTransform_contains (ringInverse index) square (ringTransform index point)
  have inverse_point := ringTransform_inverse (ringInverse index) point
  rw [inverse_inverse] at inverse_point
  simpa only [inverse_point] using equivalence

set_option maxHeartbeats 1000000 in
lemma ringTransform_rotation_point (turns : Fin 4) (index : Fin 8) (parameter : ℝ) :
    ringTransform (ringRotation turns) (ringPoint index parameter) =
      ringPoint (index + ringRotation turns) parameter := by
  fin_cases turns <;> fin_cases index <;>
    simp [ringTransform, ringPoint, ringStart, ringEnd, ringRotation, Point.interpolate,
      Point.swap, Point.reflectX, Point.reflectY, side, Point.mk.injEq] <;> ring_nf
  all_goals simp

lemma ringTransform_rotation_corner (turns : Fin 4) (index : Fin 4) :
    ringTransform (ringRotation turns) (ringCorner index) = ringCorner (index + turns) := by
  fin_cases turns <;> fin_cases index <;>
    norm_num [ringTransform, ringCorner, ringRotation, points,
      Point.swap, Point.reflectX, Point.reflectY, side, Fin.val_add] <;> ring_nf

lemma ringTransform_rotation_area (turns : Fin 4) (first second third : Point) :
    Point.orientedArea (ringTransform (ringRotation turns) first)
      (ringTransform (ringRotation turns) second) (ringTransform (ringRotation turns) third) =
      Point.orientedArea first second third := by
  fin_cases turns <;>
    norm_num [ringTransform, ringRotation, Point.orientedArea, Point.swap, Point.reflectX, Point.reflectY] <;> ring

lemma ringInverse_area (turns : Fin 4) (square : PlacedSquare) (first second : Point) :
    Point.orientedArea first second (ringSquareTransform (ringInverse (ringRotation turns)) square).center =
      Point.orientedArea (ringTransform (ringRotation turns) first)
        (ringTransform (ringRotation turns) second) square.center := by
  have invariant := ringTransform_rotation_area turns first second
    (ringSquareTransform (ringInverse (ringRotation turns)) square).center
  rw [ringSquareTransform_center, ringTransform_inverse] at invariant
  simpa only [ringSquareTransform_center] using invariant.symm

lemma ring_hit_rotated_ring
    (parameters : Fin 8 → ℝ) (square : PlacedSquare) (turns : Fin 4) (index : Fin 8)
    (inside : (ringSquareTransform (ringInverse (ringRotation turns)) square).Contains
      (ringPoint index (parameters (index + ringRotation turns)))) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  refine ⟨(index + ringRotation turns).castLE (by decide), ?_⟩
  rw [ringArchivePoints_ring, ← ringTransform_rotation_point]
  exact (ringInverse_contains _ _ _).1 inside

lemma ring_hit_rotated_corner
    (parameters : Fin 8 → ℝ) (square : PlacedSquare) (turns : Fin 4) (index : Fin 4)
    (inside : (ringSquareTransform (ringInverse (ringRotation turns)) square).Contains (ringCorner index)) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  refine ⟨⟨8 + (index + turns).val, by omega⟩, ?_⟩
  rw [ringArchivePoints_corner, ← ringTransform_rotation_corner]
  exact (ringInverse_contains _ _ _).1 inside

set_option maxHeartbeats 1000000 in
theorem ring_hit_side_exterior
    (parameters : Fin 8 → ℝ) (valid : RingParametersValid parameters)
    (square : PlacedSquare) (fits : square.Fits side) (turns : Fin 4)
    (first_cone : 0 ≤ Point.orientedArea ringCenter
      (ringPoint (7 + ringRotation turns) (parameters (7 + ringRotation turns))) square.center)
    (second_cone : 0 ≤ Point.orientedArea
      (ringPoint (ringRotation turns) (parameters (ringRotation turns))) ringCenter square.center)
    (outside : Point.orientedArea
      (ringPoint (7 + ringRotation turns) (parameters (7 + ringRotation turns)))
      (ringPoint (ringRotation turns) (parameters (ringRotation turns))) square.center ≤ 0) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  let transformed := ringSquareTransform (ringInverse (ringRotation turns)) square
  let first := ringPoint 7 (parameters (7 + ringRotation turns))
  let second := ringPoint 0 (parameters (ringRotation turns))
  have first_valid := valid (7 + ringRotation turns)
  have second_valid := valid (ringRotation turns)
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have first_coordinates :
      first.x = 2 * gap - (3 / 25) * parameters (7 + ringRotation turns) ∧
      first.y = 1 - parameters (7 + ringRotation turns) / 10 := by
    norm_num [first, ringPoint, ringStart, ringEnd, ringTransform, Point.interpolate, Point.reflectX, side]
    constructor <;> ring
  have second_coordinates :
      second.x = 2 + (3 / 25) * parameters (ringRotation turns) ∧
      second.y = 1 - parameters (ringRotation turns) / 10 := by
    norm_num [second, ringPoint, ringStart, ringEnd, ringTransform, Point.interpolate]
    constructor <;> ring
  have result := contains_bottom_sector transformed
    ((ringTransform_fits _ _).2 fits) first second
    (by linarith [first_coordinates.1])
    (by dsimp [ringCenter]; linarith [first_coordinates.1])
    (by dsimp [ringCenter]; linarith [second_coordinates.1])
    (by dsimp [side]; linarith [second_coordinates.1])
    (by linarith [first_coordinates.2]) (by linarith [first_coordinates.2])
    (by linarith [second_coordinates.2]) (by linarith [second_coordinates.2])
    (by linarith [first_coordinates.1])
    (by linarith [first_coordinates.1, second_coordinates.1])
    (by dsimp [side]; linarith [second_coordinates.1])
    (by
      change 0 ≤ Point.orientedArea ringCenter first
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center
      rw [ringInverse_area, ringTransform_ringCenter]
      dsimp [first]
      rw [ringTransform_rotation_point]
      exact first_cone)
    (by
      change 0 ≤ Point.orientedArea second ringCenter
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center
      rw [ringInverse_area, ringTransform_ringCenter]
      dsimp [second]
      rw [ringTransform_rotation_point, zero_add]
      exact second_cone)
    (by
      change Point.orientedArea first second
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center ≤ 0
      rw [ringInverse_area]
      dsimp [first, second]
      rw [ringTransform_rotation_point, ringTransform_rotation_point, zero_add]
      exact outside)
  rcases result with left_corner | first_inside | second_inside | right_corner
  · exact ring_hit_rotated_corner parameters square turns 3 left_corner
  · exact ring_hit_rotated_ring parameters square turns 7 first_inside
  · exact ring_hit_rotated_ring parameters square turns 0 (by simpa only [zero_add] using second_inside)
  · apply ring_hit_rotated_corner parameters square turns 0
    convert right_corner using 1
    norm_num [ringCorner, points, side]
    ring_nf

end SquarePackingArchive.Stromquist.TenPoints
