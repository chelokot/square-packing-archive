import SquarePackingArchive.StromquistRingRotations
import SquarePackingArchive.StromquistRingCornerExterior
import SquarePackingArchive.StromquistRingRouting

namespace SquarePackingArchive.Stromquist.TenPoints

set_option maxHeartbeats 1000000 in
theorem ring_hit_corner_exterior
    (parameters : Fin 8 → ℝ) (valid : RingParametersValid parameters)
    (square : PlacedSquare) (fits : square.Fits side) (turns : Fin 4)
    (first_cone : 0 ≤ Point.orientedArea ringCenter
      (ringPoint (ringRotation turns) (parameters (ringRotation turns))) square.center)
    (second_cone : 0 ≤ Point.orientedArea
      (ringPoint (1 + ringRotation turns) (parameters (1 + ringRotation turns))) ringCenter square.center)
    (outside : Point.orientedArea
      (ringPoint (ringRotation turns) (parameters (ringRotation turns)))
      (ringPoint (1 + ringRotation turns) (parameters (1 + ringRotation turns))) square.center ≤ 0) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  let transformed := ringSquareTransform (ringInverse (ringRotation turns)) square
  let first := ringPoint 0 (parameters (ringRotation turns))
  let second := ringPoint 1 (parameters (1 + ringRotation turns))
  have first_valid := valid (ringRotation turns)
  have second_valid := valid (1 + ringRotation turns)
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have first_coordinates :
      first.x = 2 + (3 / 25) * parameters (ringRotation turns) ∧
      first.y = 1 - parameters (ringRotation turns) / 10 := by
    norm_num [first, ringPoint, ringStart, ringEnd, ringTransform, Point.interpolate]
    constructor <;> ring
  have second_coordinates :
      second.x = 1 + 2 * gap + parameters (1 + ringRotation turns) / 10 ∧
      second.y = 2 * gap - (3 / 25) * parameters (1 + ringRotation turns) := by
    norm_num [second, ringPoint, ringStart, ringEnd, ringTransform, Point.interpolate,
      Point.swap, Point.reflectX, Point.reflectY, side]
    constructor <;> ring
  have corner_equal : ringCorner 0 = ⟨side - 1, 1⟩ := by
    norm_num [ringCorner, points, side, Point.mk.injEq]
    ring
  have fan_orientation := ring_fan_orientation 0 first_valid.1 first_valid.2 second_valid.1 second_valid.2
  have corner_orientation := ring_corner_orientation 0 second_valid.1 second_valid.2 first_valid.1 first_valid.2
  rw [corner_equal] at corner_orientation
  change 1 / 5 ≤ Point.orientedArea ringCenter
    (ringPoint 0 (parameters (ringRotation turns)))
    (ringPoint 1 (parameters (1 + ringRotation turns))) at fan_orientation
  change 1 / 5 ≤ Point.orientedArea ⟨side - 1, 1⟩
    (ringPoint 1 (parameters (1 + ringRotation turns)))
    (ringPoint 0 (parameters (ringRotation turns))) at corner_orientation
  have first_distance := ring_corner_distance 0 false first_valid.1 first_valid.2
  have second_distance := ring_corner_distance 0 true second_valid.1 second_valid.2
  rw [Point.squaredDistance_comm, corner_equal] at first_distance second_distance
  have pair_distance := ring_neighbor_distance 0 first_valid.1 first_valid.2 second_valid.1 second_valid.2
  have result := contains_bottom_right_sector transformed
    ((ringTransform_fits _ _).2 fits) first second
    (by dsimp [ringCenter]; linarith [first_coordinates.1])
    (by dsimp [side]; linarith [first_coordinates.1])
    (by linarith [first_coordinates.2]) (by linarith [first_coordinates.2])
    (by dsimp [side]; linarith [second_coordinates.1])
    (by dsimp [side]; linarith [second_coordinates.1])
    (by linarith [second_coordinates.2])
    (by dsimp [ringCenter]; linarith [second_coordinates.2])
    (by dsimp [side]; linarith [first_coordinates.1])
    (by linarith [second_coordinates.2])
    (by change 0 < Point.orientedArea ringCenter
          (ringPoint 0 (parameters (ringRotation turns)))
          (ringPoint 1 (parameters (1 + ringRotation turns))); linarith only [fan_orientation])
    (by change 0 < Point.orientedArea ⟨side - 1, 1⟩
          (ringPoint 1 (parameters (1 + ringRotation turns)))
          (ringPoint 0 (parameters (ringRotation turns))); linarith only [corner_orientation])
    first_distance second_distance pair_distance
    (by
      change 0 ≤ Point.orientedArea ringCenter first
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center
      rw [ringInverse_area, ringTransform_ringCenter]
      dsimp [first]
      rw [ringTransform_rotation_point, zero_add]
      exact first_cone)
    (by
      change 0 ≤ Point.orientedArea second ringCenter
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center
      rw [ringInverse_area, ringTransform_ringCenter]
      dsimp [second]
      rw [ringTransform_rotation_point]
      exact second_cone)
    (by
      change Point.orientedArea first second
        (ringSquareTransform (ringInverse (ringRotation turns)) square).center ≤ 0
      rw [ringInverse_area]
      dsimp [first, second]
      rw [ringTransform_rotation_point, ringTransform_rotation_point, zero_add]
      exact outside)
  rcases result with first_inside | second_inside | corner_inside
  · exact ring_hit_rotated_ring parameters square turns 0 (by simpa only [zero_add] using first_inside)
  · exact ring_hit_rotated_ring parameters square turns 1 second_inside
  · exact ring_hit_rotated_corner parameters square turns 0 (by rw [corner_equal]; exact corner_inside)

theorem ring_unavoidable (parameters : Fin 8 → ℝ) (valid : RingParametersValid parameters) :
    Unavoidable (ringArchivePoints parameters) side := by
  intro square fits
  rcases ring_hit_or_exterior parameters valid square with inside | ⟨index, first_cone, second_cone, outside⟩
  · exact inside
  · have second_cone' : 0 ≤ Point.orientedArea
        (ringPoint (index + 1) (parameters (index + 1))) ringCenter square.center := by
      dsimp [Point.orientedArea] at second_cone ⊢
      nlinarith only [second_cone]
    have outside' := le_of_lt outside
    fin_cases index
    · exact ring_hit_corner_exterior parameters valid square fits 0 first_cone second_cone' outside'
    · exact ring_hit_side_exterior parameters valid square fits 1 first_cone second_cone' outside'
    · exact ring_hit_corner_exterior parameters valid square fits 1 first_cone second_cone' outside'
    · exact ring_hit_side_exterior parameters valid square fits 2 first_cone second_cone' outside'
    · exact ring_hit_corner_exterior parameters valid square fits 2 first_cone second_cone' outside'
    · exact ring_hit_side_exterior parameters valid square fits 3 first_cone second_cone' outside'
    · exact ring_hit_corner_exterior parameters valid square fits 3 first_cone second_cone' outside'
    · exact ring_hit_side_exterior parameters valid square fits 0 first_cone second_cone' outside'

end SquarePackingArchive.Stromquist.TenPoints
