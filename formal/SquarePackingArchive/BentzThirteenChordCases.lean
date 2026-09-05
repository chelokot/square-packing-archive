import SquarePackingArchive.BentzRectangleBoundary

namespace SquarePackingArchive.Bentz

theorem interval_length_le_of_missed
    (contains : ℝ → Prop) {bottom top lower upper target : ℝ}
    (lower_bound : bottom ≤ lower) (upper_bound : upper ≤ top)
    (inside : ∀ coordinate ∈ Set.Icc lower upper, contains coordinate)
    (missing : ¬ contains target) : upper - lower ≤ max (target - bottom) (top - target) := by
  by_cases below : lower ≤ target
  · by_cases above : target ≤ upper
    · exact (missing (inside target ⟨below, above⟩)).elim
    · exact (show upper - lower ≤ target - bottom by linarith).trans (le_max_left _ _)
  · exact (show upper - lower ≤ top - target by linarith).trans (le_max_right _ _)

theorem point_inside_of_long_interval
    (contains : ℝ → Prop) {bottom top lower upper target : ℝ}
    (lower_bound : bottom ≤ lower) (upper_bound : upper ≤ top)
    (inside : ∀ coordinate ∈ Set.Icc lower upper, contains coordinate)
    (length_bound : max (target - bottom) (top - target) < upper - lower) : contains target := by
  by_contra missing
  exact (not_lt_of_ge (interval_length_le_of_missed contains lower_bound upper_bound inside missing)) length_bound

theorem short_rectangle_forces_both_side_points
    (square : PlacedSquare) {left bottom : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + 27 / 50)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + (27 / 50) * row⟩) :
    square.Contains ⟨left, bottom + 7 / 25⟩ ∧ square.Contains ⟨left + 1, bottom + 7 / 25⟩ := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_lower, _, first_upper,
      second_lower, _, second_upper, _, first_length, second_length, first_inside, second_inside⟩ :=
    rectangle_vertical_chords square (height := 27 / 50) (by norm_num) (by nlinarith)
      center_left center_right center_bottom center_top corners_missing
  have cap : max (bottom + 7 / 25 - bottom) (bottom + 27 / 50 - (bottom + 7 / 25)) = 7 / 25 := by
    rw [max_eq_left (by linarith)]
    ring
  constructor
  · apply point_inside_of_long_interval (fun vertical => square.Contains ⟨left, vertical⟩)
      first_lower.le first_upper.le first_inside
    rw [cap]
    nlinarith
  · apply point_inside_of_long_interval (fun vertical => square.Contains ⟨left + 1, vertical⟩)
      second_lower.le second_upper.le second_inside
    rw [cap]
    nlinarith

theorem short_rectangle_forces_additional_side_point
    (square : PlacedSquare) {left bottom : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + 27 / 50)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + (27 / 50) * row⟩) :
    square.Contains ⟨left, bottom + 8 / 25⟩ ∨ square.Contains ⟨left + 1, bottom + 1 / 25⟩ := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_lower, _, first_upper,
      second_lower, _, second_upper, total_length, _, _, first_inside, second_inside⟩ :=
    rectangle_vertical_chords square (height := 27 / 50) (by norm_num) (by nlinarith)
      center_left center_right center_bottom center_top corners_missing
  by_cases first_point : square.Contains ⟨left, bottom + 8 / 25⟩
  · exact Or.inl first_point
  apply Or.inr
  have first_bound := interval_length_le_of_missed (fun vertical => square.Contains ⟨left, vertical⟩)
    first_lower.le first_upper.le first_inside first_point
  have first_cap : max (bottom + 8 / 25 - bottom) (bottom + 27 / 50 - (bottom + 8 / 25)) = 8 / 25 := by
    rw [max_eq_left (by linarith)]
    ring
  rw [first_cap] at first_bound
  apply point_inside_of_long_interval (fun vertical => square.Contains ⟨left + 1, vertical⟩)
    second_lower.le second_upper.le second_inside
  rw [max_eq_right (by linarith)]
  nlinarith

theorem tall_rectangle_missing_left_forces_right
    (square : PlacedSquare) {left bottom : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + 73 / 100)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + (73 / 100) * row⟩)
    (left_missing : ¬ square.Contains ⟨left, bottom + 9 / 25⟩) :
    square.Contains ⟨left + 1, bottom + 7 / 25⟩ := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_lower, _, first_upper,
      second_lower, _, second_upper, total_length, _, _, first_inside, second_inside⟩ :=
    rectangle_vertical_chords square (height := 73 / 100) (by norm_num) (by nlinarith)
      center_left center_right center_bottom center_top corners_missing
  have first_bound := interval_length_le_of_missed (fun vertical => square.Contains ⟨left, vertical⟩)
    first_lower.le first_upper.le first_inside left_missing
  have first_cap : max (bottom + 9 / 25 - bottom) (bottom + 73 / 100 - (bottom + 9 / 25)) = 37 / 100 := by
    rw [max_eq_right (by linarith)]
    ring
  rw [first_cap] at first_bound
  apply point_inside_of_long_interval (fun vertical => square.Contains ⟨left + 1, vertical⟩)
    second_lower.le second_upper.le second_inside
  rw [max_eq_right (by linarith)]
  nlinarith

theorem tall_rectangle_forces_left_sliding_point
    (square : PlacedSquare) {left bottom : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + 73 / 100)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + (73 / 100) * row⟩) :
    square.Contains ⟨left, bottom + 16 / 25⟩ ∨
      ∃ vertical ∈ Set.Icc (bottom + 9 / 100) (bottom + 11 / 20),
        square.Contains ⟨left, vertical⟩ := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_lower, first_positive,
      first_upper, _, _, _, _, first_length, _, first_inside, _⟩ :=
    rectangle_vertical_chords square (height := 73 / 100) (by norm_num) (by nlinarith)
      center_left center_right center_bottom center_top corners_missing
  by_cases target_inside : square.Contains ⟨left, bottom + 16 / 25⟩
  · exact Or.inl target_inside
  apply Or.inr
  have length_nine : 9 / 100 < firstUpper - firstLower := by nlinarith
  have lower_target : firstLower ≤ bottom + 16 / 25 := by
    by_contra! outside
    linarith
  have upper_target : firstUpper < bottom + 16 / 25 := by
    by_contra! outside
    exact target_inside (first_inside _ ⟨lower_target, outside⟩)
  have lower_sliding : firstLower ≤ bottom + 11 / 20 := by linarith
  have upper_sliding : bottom + 9 / 100 ≤ firstUpper := by linarith
  refine ⟨max firstLower (bottom + 9 / 100), ⟨le_max_right _ _, ?_⟩, ?_⟩
  · exact max_le lower_sliding (by linarith)
  · exact first_inside _ ⟨le_max_left _ _, max_le first_positive.le upper_sliding⟩

theorem tall_rectangle_forces_left_grid_point
    (square : PlacedSquare) {left bottom : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + 73 / 100)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + (73 / 100) * row⟩) :
    ∃ index : Fin 8, square.Contains ⟨left, bottom + (2 / 25) * (index + 1)⟩ := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_lower, _,
      first_upper, _, _, _, _, first_length, _, first_inside, _⟩ :=
    rectangle_vertical_chords square (height := 73 / 100) (by norm_num) (by nlinarith)
      center_left center_right center_bottom center_top corners_missing
  have length_nine : 9 / 100 < firstUpper - firstLower := by nlinarith
  by_contra! missing
  have after (index : Fin 8) (previous : bottom + (2 / 25) * (index : ℝ) ≤ firstLower) :
      bottom + (2 / 25) * (index + 1) < firstLower := by
    by_contra! before
    exact missing index (first_inside _ ⟨before, by linarith⟩)
  have step0 := after 0 (by norm_num; linarith)
  have step1 := after 1 (by norm_num at step0 ⊢; linarith)
  have step2 := after 2 (by norm_num at step1 ⊢; linarith)
  have step3 := after 3 (by norm_num at step2 ⊢; linarith)
  have step4 := after 4 (by norm_num at step3 ⊢; linarith)
  have step5 := after 5 (by norm_num at step4 ⊢; linarith)
  have step6 := after 6 (by norm_num at step5 ⊢; linarith)
  have step7 := after 7 (by norm_num at step6 ⊢; linarith)
  norm_num at step7
  linarith

end SquarePackingArchive.Bentz
