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

end SquarePackingArchive
