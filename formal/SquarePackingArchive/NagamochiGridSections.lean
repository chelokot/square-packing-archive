import SquarePackingArchive.NagamochiBoundaryAnchor

namespace SquarePackingArchive.Nagamochi

open Set

lemma grid_height_offset_bound
    {cosine sine factor center : ℝ}
    (cosine_nonnegative : 0 ≤ cosine)
    (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (factor_gt_one : 1 < factor)
    (center_lower : factor * (cosine + sine) / 2 ≤ center)
    (center_upper : center ≤ 1) :
    |9 / 10 - center| < factor * ((cosine + sine) / 2 - cosine * sine) := by
  have product_nonnegative : 0 ≤ cosine * sine := mul_nonneg cosine_nonnegative sine_nonnegative
  have sum_at_least_one : 1 ≤ cosine + sine := by nlinarith
  have sum_lt_ten_sevenths : cosine + sine < 10 / 7 := by
    nlinarith [sq_nonneg (cosine - sine)]
  have interval_product : 0 ≤ (cosine + sine - 1) * (10 / 7 - (cosine + sine)) :=
    mul_nonneg (by linarith) (by linarith)
  have sum_sub_product : 9 / 10 < cosine + sine - cosine * sine := by
    nlinarith
  have half_sum_sub_product : 1 / 10 < (cosine + sine) / 2 - cosine * sine := by
    nlinarith
  have scaled_sum := mul_lt_mul_of_pos_right factor_gt_one (by linarith :
    0 < cosine + sine - cosine * sine)
  have scaled_half_sum := mul_lt_mul_of_pos_right factor_gt_one (by linarith :
    0 < (cosine + sine) / 2 - cosine * sine)
  rw [abs_lt]
  constructor <;> nlinarith

lemma horizontal_chord_longer_than_side_of_offset_bound
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (offset_bound : |height - factor * square.center.y| <
      factor * ((square.frame.cosine + square.frame.sine) / 2 -
        square.frame.cosine * square.frame.sine)) :
    ∃ intervalStart intervalEnd : ℝ,
      factor < intervalEnd - intervalStart ∧
        ∀ horizontal ∈ Ioo intervalStart intervalEnd,
          ![horizontal, height] ∈ square.dilatedInteriorRegion factor := by
  let lower := max (square.horizontalAdjacentChordStart factor height)
    (square.horizontalAdjacentOtherLower factor height)
  let upper := min (square.horizontalAdjacentOtherUpper factor height)
    (square.horizontalAdjacentChordEnd factor height)
  refine ⟨lower, upper, ?_, square.horizontalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive (le_max_left _ _) (le_max_right _ _)
    (min_le_left _ _) (min_le_right _ _)⟩
  have cosine_lt_one : square.frame.cosine < 1 := by nlinarith [square.frame.unit]
  have sine_lt_one : square.frame.sine < 1 := by nlinarith [square.frame.unit]
  have offset_limits := abs_lt.mp offset_bound
  have pair_bounds :
      square.horizontalAdjacentChordStart factor height + factor <
          square.horizontalAdjacentOtherUpper factor height ∧
      square.horizontalAdjacentChordStart factor height + factor <
          square.horizontalAdjacentChordEnd factor height ∧
      square.horizontalAdjacentOtherLower factor height + factor <
          square.horizontalAdjacentOtherUpper factor height ∧
      square.horizontalAdjacentOtherLower factor height + factor <
          square.horizontalAdjacentChordEnd factor height := by
    dsimp [PlacedSquare.horizontalAdjacentChordStart, PlacedSquare.horizontalAdjacentChordEnd,
      PlacedSquare.horizontalAdjacentOtherLower, PlacedSquare.horizontalAdjacentOtherUpper]
    have scaled_unit :
        (height - factor * square.center.y) * square.frame.cosine ^ 2 +
          (height - factor * square.center.y) * square.frame.sine ^ 2 =
            height - factor * square.center.y := by
      linear_combination (height - factor * square.center.y) * square.frame.unit
    constructor
    · field_simp
      nlinarith [mul_pos factor_positive (sub_pos.mpr cosine_lt_one)]
    constructor
    · field_simp
      nlinarith
    constructor
    · field_simp
      nlinarith
    · field_simp
      nlinarith [mul_pos factor_positive (sub_pos.mpr sine_lt_one)]
  dsimp [lower, upper]
  rw [lt_sub_iff_add_lt, add_comm factor, ← max_add_add_right, lt_min_iff,
    max_lt_iff, max_lt_iff]
  exact ⟨⟨pair_bounds.1, pair_bounds.2.2.1⟩, ⟨pair_bounds.2.1, pair_bounds.2.2.2⟩⟩

theorem bottom_grid_chord_at_least_side
    (square : PlacedSquare) {factor side : ℝ}
    (fits : square.Fits side)
    (factor_gt_one : 1 < factor)
    (center_below : factor * square.center.y ≤ 1) :
    ∃ intervalStart intervalEnd : ℝ,
      factor ≤ intervalEnd - intervalStart ∧
        ∀ horizontal ∈ Ioo intervalStart intervalEnd,
          ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let normalized := square.firstQuadrant
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_fits : normalized.Fits side := (square.firstQuadrant_fits_iff side).2 fits
  have cosine_nonnegative : 0 ≤ normalized.frame.cosine := square.firstQuadrant_cosine_nonnegative
  have sine_nonnegative : 0 ≤ normalized.frame.sine := square.firstQuadrant_sine_nonnegative
  have center_bound := (normalized.center_bounds normalized_fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative,
    abs_of_nonneg sine_nonnegative] at center_bound
  have center_lower : factor * (normalized.frame.cosine + normalized.frame.sine) / 2 ≤
      factor * normalized.center.y := by
    nlinarith [mul_le_mul_of_nonneg_left center_bound factor_positive.le]
  have normalized_below : factor * normalized.center.y ≤ 1 := by simpa [normalized] using center_below
  by_cases axis_aligned : normalized.frame.cosine = 0 ∨ normalized.frame.sine = 0
  · have anchor : ![factor * normalized.center.x, (9 / 10 : ℝ)] ∈
        normalized.dilatedInteriorRegion factor := by
      have offset_bound := grid_height_offset_bound cosine_nonnegative sine_nonnegative
        normalized.frame.unit factor_gt_one center_lower normalized_below
      apply normalized.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
      all_goals
        rcases axis_aligned with cosine_zero | sine_zero
        all_goals
          have other_one : normalized.frame.cosine = 1 ∨ normalized.frame.sine = 1 := by
            first
            | right; nlinarith [normalized.frame.unit]
            | left; nlinarith [normalized.frame.unit]
          rcases other_one with cosine_one | sine_one <;>
            simp_all [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint,
              div_eq_mul_inv]
    obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
      exists_horizontal_chord_of_axis_aligned normalized factor_positive cosine_nonnegative
        sine_nonnegative axis_aligned ⟨_, anchor⟩
    exact ⟨intervalStart, intervalEnd, length_bound, by simpa [normalized, region_eq] using chord_inside⟩
  push Not at axis_aligned
  obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
    horizontal_chord_longer_than_side_of_offset_bound normalized factor_positive
      (lt_of_le_of_ne cosine_nonnegative axis_aligned.1.symm)
      (lt_of_le_of_ne sine_nonnegative axis_aligned.2.symm)
      (grid_height_offset_bound cosine_nonnegative sine_nonnegative normalized.frame.unit
        factor_gt_one center_lower normalized_below)
  exact ⟨intervalStart, intervalEnd, length_bound.le, by simpa [normalized, region_eq] using chord_inside⟩

end SquarePackingArchive.Nagamochi
