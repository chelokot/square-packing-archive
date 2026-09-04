import SquarePackingArchive.Friedman

namespace SquarePackingArchive

lemma Frame.height_add_product_le_sum_of_height_le_sqrt_two_sub_half
    (frame : Frame) {height : ℝ}
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine)
    (height_upper : height ≤ Real.sqrt 2 - 1 / 2) :
    height + frame.cosine * frame.sine ≤ frame.cosine + frame.sine := by
  have sqrt_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have sqrt_squared := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have sqrt_at_least_one : 1 ≤ Real.sqrt 2 := by nlinarith
  have sum_at_least_one : 1 ≤ frame.cosine + frame.sine := by
    nlinarith [frame.unit]
  have sum_at_most_sqrt : frame.cosine + frame.sine ≤ Real.sqrt 2 := by
    nlinarith [frame.unit, sq_nonneg (frame.cosine - frame.sine)]
  have product_nonpositive :
      (Real.sqrt 2 - (frame.cosine + frame.sine)) *
        (2 - Real.sqrt 2 - (frame.cosine + frame.sine)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith [frame.unit]

lemma PlacedSquare.contains_bottomUnitPair
    {square : PlacedSquare} {side left targetHeight : ℝ}
    (fits : square.Fits side)
    (target_height_upper : targetHeight ≤ Real.sqrt 2 - 1 / 2)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 1)
    (center_y_upper : square.center.y ≤ targetHeight) :
    square.Contains ⟨left, targetHeight⟩ ∨
      square.Contains ⟨left + 1, targetHeight⟩ := by
  apply square.contains_bottomPairWith fits ?_ (by norm_num) (by norm_num)
    ?_ center_x_lower center_x_upper center_y_upper
  · have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · intro frame cosine_nonnegative sine_nonnegative
    simpa only [one_mul] using
      frame.height_add_product_le_sum_of_height_le_sqrt_two_sub_half
        cosine_nonnegative sine_nonnegative target_height_upper

lemma rationalStripHeight_le_sqrt_two_sub_half :
    (451 : ℝ) / 500 ≤ Real.sqrt 2 - 1 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg (2 : ℝ)]

lemma PlacedSquare.contains_bottomSpacedRow
    {square : PlacedSquare} {side left targetHeight : ℝ}
    (lastColumn : ℕ)
    (fits : square.Fits side)
    (left_upper : left ≤ 1)
    (right_upper : side - (left + lastColumn) ≤ 1)
    (target_height_upper : targetHeight ≤ Real.sqrt 2 - 1 / 2)
    (center_y_upper : square.center.y ≤ targetHeight) :
    ∃ column : Fin (lastColumn + 1),
      square.Contains ⟨left + (column : ℝ), targetHeight⟩ := by
  have height_le_one : targetHeight ≤ 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  by_cases center_left : square.center.x ≤ left
  · exact ⟨0, by
      simpa using square.contains_cornerPoint fits
        left_upper height_le_one center_left center_y_upper⟩
  by_cases center_right : left + lastColumn ≤ square.center.x
  · have contained := (square.reflectX side).contains_cornerPoint
      ((square.reflectX_fits_iff side).2 fits) right_upper height_le_one
      (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    refine ⟨Fin.last lastColumn, (square.reflectX_contains_iff side _).mp ?_⟩
    simpa [Point.reflectX] using contained
  have offset_nonnegative : 0 ≤ square.center.x - left := by linarith
  let column : Fin lastColumn := ⟨⌊square.center.x - left⌋₊,
    (Nat.floor_lt offset_nonnegative).2 (by linarith)⟩
  have column_lower : (column : ℝ) ≤ square.center.x - left :=
    Nat.floor_le offset_nonnegative
  have column_upper : square.center.x - left < (column : ℝ) + 1 :=
    Nat.lt_floor_add_one (square.center.x - left)
  obtain left_mem | right_mem := square.contains_bottomUnitPair fits target_height_upper
    (left := left + (column : ℝ)) (by linarith) (by linarith) center_y_upper
  · exact ⟨column.castSucc, left_mem⟩
  · exact ⟨column.succ, by simpa [add_assoc] using right_mem⟩

lemma PlacedSquare.contains_topSpacedRow
    {square : PlacedSquare} {side left targetHeight : ℝ}
    (lastColumn : ℕ)
    (fits : square.Fits side)
    (left_upper : left ≤ 1)
    (right_upper : side - (left + lastColumn) ≤ 1)
    (target_height_lower : side - targetHeight ≤ Real.sqrt 2 - 1 / 2)
    (center_y_lower : targetHeight ≤ square.center.y) :
    ∃ column : Fin (lastColumn + 1),
      square.Contains ⟨left + (column : ℝ), targetHeight⟩ := by
  obtain ⟨column, contained⟩ := (square.reflectY side).contains_bottomSpacedRow
    lastColumn ((square.reflectY_fits_iff side).2 fits) left_upper right_upper
    target_height_lower (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  exact ⟨column, (square.reflectY_contains_iff side _).mp contained⟩

end SquarePackingArchive
