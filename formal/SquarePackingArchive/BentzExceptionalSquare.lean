import SquarePackingArchive.BentzLineCuts

namespace SquarePackingArchive

lemma PlacedSquare.contained_point_distance_sq_le_half
    (square : PlacedSquare) {point : Point} (contained : square.Contains point) :
    (point.x - square.center.x)^2 + (point.y - square.center.y)^2 ≤ 1 / 2 := by
  have bounds := (square.contains_iff_localCoordinates point).1 contained
  rw [abs_le, abs_le] at bounds
  have identity := square.local_coordinate_distance_sq point square.center
  have center_x : square.localX square.center = 0 := by simp [PlacedSquare.localX]
  have center_y : square.localY square.center = 0 := by simp [PlacedSquare.localY]
  rw [center_x, center_y, sub_zero, sub_zero] at identity
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - square.localX point)
    (by linarith : 0 ≤ 1 / 2 + square.localX point),
    mul_nonneg (by linarith : 0 ≤ 1 / 2 - square.localY point)
    (by linarith : 0 ≤ 1 / 2 + square.localY point)]

lemma PlacedSquare.missing_interior_point_distance_sq_ge_quarter
    (square : PlacedSquare) {point : Point} (missing : ¬ square.InteriorContains point) :
    1 / 4 ≤ (point.x - square.center.x)^2 + (point.y - square.center.y)^2 := by
  by_contra! distance
  apply missing
  rw [square.interiorContains_iff_localCoordinates, abs_lt, abs_lt]
  have identity := square.local_coordinate_distance_sq point square.center
  have center_x : square.localX square.center = 0 := by simp [PlacedSquare.localX]
  have center_y : square.localY square.center = 0 := by simp [PlacedSquare.localY]
  rw [center_x, center_y, sub_zero, sub_zero] at identity
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (square.localX point), sq_nonneg (square.localY point)]

namespace Bentz

set_option maxHeartbeats 1000000 in
theorem middle_exception_impossible (square : PlacedSquare) {ratio : ℝ}
    (ratio_lower : 4999 / 5000 ≤ ratio) (ratio_upper : ratio ≤ 1)
    (left : square.Contains ⟨ratio / 2, 5 * ratio / 2⟩)
    (right_missing : ¬ square.InteriorContains ⟨3 * ratio / 2, 5 * ratio / 2⟩)
    (low_missing : ¬ square.InteriorContains ⟨451 / 500, 2⟩)
    (high_missing : ¬ square.InteriorContains ⟨451 / 500, 3⟩)
    (center_right : 11 / 10 ≤ square.center.x) : False := by
  have left_distance := square.contained_point_distance_sq_le_half left
  have right_distance := square.missing_interior_point_distance_sq_ge_quarter right_missing
  have low_distance := square.missing_interior_point_distance_sq_ge_quarter low_missing
  have high_distance := square.missing_interior_point_distance_sq_ge_quarter high_missing
  dsimp only at left_distance right_distance low_distance high_distance
  have horizontal_upper : square.center.x ≤ 121 / 100 := by
    have displacement_upper : square.center.x - ratio / 2 ≤ 71 / 100 := by
      nlinarith only [left_distance, sq_nonneg (5 * ratio / 2 - square.center.y),
        sq_nonneg (square.center.x - ratio / 2 - 71 / 100)]
    linarith only [displacement_upper, ratio_upper]
  have horizontal_distance_lower : (ratio / 2 - square.center.x)^2 ≥ (3 / 5 : ℝ)^2 := by
    nlinarith only [center_right, ratio_upper,
      sq_nonneg (square.center.x - ratio / 2 - 3 / 5)]
  have vertical_distance_upper : (5 * ratio / 2 - square.center.y)^2 ≤ 7 / 50 := by
    nlinarith only [left_distance, horizontal_distance_lower]
  have vertical_lower : 21 / 10 ≤ square.center.y := by
    have displacement : 5 * ratio / 2 - square.center.y ≤ 39 / 100 := by
      nlinarith only [vertical_distance_upper, sq_nonneg (5 * ratio / 2 - square.center.y - 39 / 100)]
    linarith only [displacement, ratio_lower]
  have vertical_upper : square.center.y ≤ 29 / 10 := by
    have displacement : square.center.y - 5 * ratio / 2 ≤ 39 / 100 := by
      nlinarith only [vertical_distance_upper, sq_nonneg (square.center.y - 5 * ratio / 2 - 39 / 100)]
    linarith only [displacement, ratio_upper]
  have horizontal_green_bound : (451 / 500 - square.center.x)^2 ≤ (77 / 250 : ℝ)^2 := by
    nlinarith only [center_right, horizontal_upper, mul_nonneg (show 0 ≤ square.center.x - 11 / 10 by linarith)
      (show 0 ≤ 121 / 100 - square.center.x by linarith)]
  have middle_lower : 239 / 100 ≤ square.center.y := by
    nlinarith only [low_distance, horizontal_green_bound, vertical_lower,
      mul_nonneg (show 0 ≤ square.center.y - 2 by linarith) (show 0 ≤ square.center.y - 2 by linarith)]
  have middle_upper : square.center.y ≤ 261 / 100 := by
    nlinarith only [high_distance, horizontal_green_bound, vertical_upper]
  have horizontal_right_bound : (3 * ratio / 2 - square.center.x)^2 ≤ (2 / 5 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * ratio / 2 - square.center.x by linarith)
      (show 0 ≤ 2 / 5 - (3 * ratio / 2 - square.center.x) by linarith)]
  have vertical_right_bound : (5 * ratio / 2 - square.center.y)^2 ≤ (3 / 25 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 / 25 - (5 * ratio / 2 - square.center.y) by linarith)
      (show 0 ≤ 3 / 25 + (5 * ratio / 2 - square.center.y) by linarith)]
  nlinarith only [right_distance, horizontal_right_bound, vertical_right_bound]

theorem bottom_exception_impossible (square : PlacedSquare) {ratio side : ℝ}
    (ratio_upper : ratio ≤ 1)
    (fits : square.Fits side)
    (left : square.Contains ⟨ratio / 2, 9 * ratio / 10⟩)
    (green_missing : ¬ square.InteriorContains ⟨451 / 500, 1⟩)
    (center_right : 11 / 10 ≤ square.center.x) : False := by
  have left_distance := square.contained_point_distance_sq_le_half left
  have green_distance := square.missing_interior_point_distance_sq_ge_quarter green_missing
  dsimp only at left_distance green_distance
  have center_above : square.center.x - ratio / 2 ≤ square.center.y := by
    let normalized := square.firstQuadrant
    have normalized_fits : normalized.Fits side := (square.firstQuadrant_fits_iff side).2 fits
    have cosine_nonnegative : 0 ≤ normalized.frame.cosine := square.firstQuadrant_cosine_nonnegative
    have sine_nonnegative : 0 ≤ normalized.frame.sine := square.firstQuadrant_sine_nonnegative
    have bottom_bound := (normalized.center_bounds normalized_fits).2.2.1
    simp only [frameExtent, abs_of_nonneg cosine_nonnegative, abs_of_nonneg sine_nonnegative] at bottom_bound
    have normalized_left : normalized.Contains ⟨ratio / 2, 9 * ratio / 10⟩ :=
      (square.firstQuadrant_contains_iff _).2 left
    obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ := normalized_left
    have horizontal_eq := congrArg Point.x point_eq
    dsimp [PlacedSquare.point, Frame.place] at horizontal_eq
    have lower_x := (abs_le.1 horizontal_bound).1
    have upper_y := (abs_le.1 vertical_bound).2
    have result : normalized.center.x - ratio / 2 ≤ normalized.center.y := by
      nlinarith only [horizontal_eq, bottom_bound,
        mul_nonneg cosine_nonnegative (show 0 ≤ localX + 1 / 2 by linarith),
        mul_nonneg sine_nonnegative (show 0 ≤ 1 / 2 - localY by linarith)]
    simpa [normalized] using result
  have horizontal_comparison := mul_nonneg
    (show 0 ≤ 451 / 250 - ratio by linarith)
    (show 0 ≤ square.center.x - 11 / 10 by linarith)
  have vertical_comparison := mul_nonneg
    (show 0 ≤ 2 - 9 * ratio / 5 by linarith)
    (show 0 ≤ square.center.y - 11 / 10 + ratio / 2 by linarith)
  nlinarith only [left_distance, green_distance, horizontal_comparison,
    vertical_comparison, ratio_upper, sq_nonneg (1 - ratio)]

lemma near_edge_center_offset_bound {cosine sine center : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine^2 + sine^2 = 1)
    (center_lower : (cosine + sine) / 2 ≤ center)
    (center_upper : center ≤ 11 / 10) :
    |451 / 500 - center| < (cosine + sine) / 2 - cosine * sine := by
  have product_nonnegative := mul_nonneg cosine_nonnegative sine_nonnegative
  have sum_lower : 1 ≤ cosine + sine := by nlinarith
  have sum_upper : cosine + sine < 71 / 50 := by nlinarith [sq_nonneg (cosine - sine)]
  have interval_product := mul_nonneg (show 0 ≤ cosine + sine - 1 by linarith)
    (show 0 ≤ 71 / 50 - (cosine + sine) by linarith)
  have full_sum_clearance : 451 / 500 < cosine + sine - cosine * sine := by nlinarith
  have half_sum_clearance : 99 / 500 < (cosine + sine) / 2 - cosine * sine := by nlinarith
  rw [abs_lt]
  constructor <;> linarith

theorem horizontal_unit_chord_of_center_le_eleven_tenths
    (square : PlacedSquare) {side : ℝ} (fits : square.Fits side)
    (center_below : square.center.y ≤ 11 / 10) :
    ∃ intervalStart intervalEnd : ℝ, 1 ≤ intervalEnd - intervalStart ∧
      ∀ horizontal ∈ Set.Ioo intervalStart intervalEnd,
        square.InteriorContains ⟨horizontal, 451 / 500⟩ := by
  apply horizontal_unit_chord_of_normalized_offset_bound
  let normalized := square.firstQuadrant
  have normalized_fits : normalized.Fits side := (square.firstQuadrant_fits_iff side).2 fits
  have cosine_nonnegative : 0 ≤ normalized.frame.cosine := square.firstQuadrant_cosine_nonnegative
  have sine_nonnegative : 0 ≤ normalized.frame.sine := square.firstQuadrant_sine_nonnegative
  have center_lower := (normalized.center_bounds normalized_fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative, abs_of_nonneg sine_nonnegative] at center_lower
  exact near_edge_center_offset_bound cosine_nonnegative sine_nonnegative normalized.frame.unit
    center_lower (by simpa [normalized] using center_below)

theorem vertical_unit_chord_of_center_le_eleven_tenths
    (square : PlacedSquare) {side : ℝ} (fits : square.Fits side)
    (center_left : square.center.x ≤ 11 / 10) :
    ∃ intervalStart intervalEnd : ℝ, 1 ≤ intervalEnd - intervalStart ∧
      ∀ vertical ∈ Set.Ioo intervalStart intervalEnd,
        square.InteriorContains ⟨451 / 500, vertical⟩ := by
  obtain ⟨intervalStart, intervalEnd, length_bound, inside⟩ :=
    horizontal_unit_chord_of_center_le_eleven_tenths square.swap
      ((square.swap_fits_iff side).2 fits) center_left
  refine ⟨intervalStart, intervalEnd, length_bound, ?_⟩
  intro vertical vertical_mem
  exact (square.interiorContains_swap_iff ⟨451 / 500, vertical⟩).1 (inside vertical vertical_mem)

end Bentz

end SquarePackingArchive
