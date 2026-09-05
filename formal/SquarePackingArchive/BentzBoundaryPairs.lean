import SquarePackingArchive.StromquistRingBoundary
import SquarePackingArchive.FriedmanStrip

namespace SquarePackingArchive

lemma Frame.height_add_scaled_product_le_sum
    (frame : Frame) {height width : ℝ}
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine)
    (height_upper : height ≤ 1)
    (width_upper : width ≤ 2 * Real.sqrt 2 - 2) :
    height + width * (frame.cosine * frame.sine) ≤ frame.cosine + frame.sine := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have product_nonnegative := mul_nonneg cosine_nonnegative sine_nonnegative
  have sum_lower : 1 ≤ frame.cosine + frame.sine := by
    nlinarith [frame.unit]
  have sum_upper : frame.cosine + frame.sine ≤ Real.sqrt 2 := by
    nlinarith [frame.unit, sq_nonneg (frame.cosine - frame.sine)]
  have width_product := mul_le_mul width_upper (show
      frame.cosine + frame.sine + 1 ≤ Real.sqrt 2 + 1 by linarith)
    (show 0 ≤ frame.cosine + frame.sine + 1 by linarith)
    (show 0 ≤ 2 * Real.sqrt 2 - 2 by nlinarith)
  have factor_nonnegative : 0 ≤ 2 - width * (frame.cosine + frame.sine + 1) := by
    nlinarith only [width_product, root_square]
  have product := mul_nonneg (show 0 ≤ frame.cosine + frame.sine - 1 by linarith)
    factor_nonnegative
  have scaled_unit := congrArg (fun value : ℝ => width * value) frame.unit
  nlinarith only [product, scaled_unit, height_upper]

lemma PlacedSquare.contains_bottomSharpPair
    {square : PlacedSquare} {side left targetHeight gap : ℝ}
    (fits : square.Fits side)
    (target_height_upper : targetHeight ≤ 1)
    (gap_positive : 0 < gap)
    (gap_upper : gap ≤ 2 * Real.sqrt 2 - 2)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + gap)
    (center_y_upper : square.center.y ≤ targetHeight) :
    square.Contains ⟨left, targetHeight⟩ ∨
      square.Contains ⟨left + gap, targetHeight⟩ := by
  apply square.contains_bottomPairWith fits target_height_upper gap_positive
    (show gap ≤ 1 by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)])
    _ center_x_lower center_x_upper center_y_upper
  intro frame cosine_nonnegative sine_nonnegative
  exact frame.height_add_scaled_product_le_sum cosine_nonnegative sine_nonnegative
    target_height_upper gap_upper

lemma PlacedSquare.contains_bottomLowPair
    {square : PlacedSquare} {side left targetHeight gap : ℝ}
    (fits : square.Fits side)
    (target_height_upper : targetHeight ≤ Real.sqrt 2 - 1 / 2)
    (gap_positive : 0 < gap) (gap_upper : gap ≤ 1)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + gap)
    (center_y_upper : square.center.y ≤ targetHeight) :
    square.Contains ⟨left, targetHeight⟩ ∨
      square.Contains ⟨left + gap, targetHeight⟩ := by
  apply square.contains_bottomPairWith fits
    (show targetHeight ≤ 1 by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)])
    gap_positive gap_upper _ center_x_lower center_x_upper center_y_upper
  intro frame cosine_nonnegative sine_nonnegative
  have bound := frame.height_add_product_le_sum_of_height_le_sqrt_two_sub_half
    cosine_nonnegative sine_nonnegative target_height_upper
  have product := mul_nonneg (show 0 ≤ 1 - gap by linarith)
    (mul_nonneg cosine_nonnegative sine_nonnegative)
  nlinarith only [bound, product]

namespace Bentz

def BoundaryWeightBound (width height : ℝ) : Prop :=
  ∀ frame : Frame, 0 ≤ frame.cosine → 0 ≤ frame.sine →
    frame.cosine ^ 2 + height * frame.sine ^ 2 + width * frame.cosine * frame.sine ≤
      frame.cosine + frame.sine

lemma BoundaryWeightBound.mono {width height largerWidth largerHeight : ℝ}
    (bound : BoundaryWeightBound largerWidth largerHeight)
    (width_upper : width ≤ largerWidth) (height_upper : height ≤ largerHeight) :
    BoundaryWeightBound width height := by
  intro frame cosine_nonnegative sine_nonnegative
  have original := bound frame cosine_nonnegative sine_nonnegative
  have width_product := mul_nonneg (show 0 ≤ largerWidth - width by linarith)
    (mul_nonneg cosine_nonnegative sine_nonnegative)
  have height_product := mul_nonneg (show 0 ≤ largerHeight - height by linarith)
    (sq_nonneg frame.sine)
  nlinarith only [original, width_product, height_product]

lemma weighted_bound_first {width height : ℝ}
    (width_upper : width ≤ 89 / 100) (height_upper : height ≤ 921 / 1000) :
    BoundaryWeightBound width height := by
  apply BoundaryWeightBound.mono (largerWidth := 89 / 100)
    (largerHeight := 921 / 1000) _ width_upper height_upper
  intro frame cosine_nonnegative sine_nonnegative
  apply Stromquist.weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
  exact Stromquist.boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    (by norm_num) (by norm_num)
    (Stromquist.clearancePolynomial_bentz_first_nonnegative cosine_nonnegative)

lemma weighted_bound_second {width height : ℝ}
    (width_upper : width ≤ 9 / 10) (height_upper : height ≤ 9 / 10) :
    BoundaryWeightBound width height := by
  apply BoundaryWeightBound.mono (largerWidth := 9 / 10)
    (largerHeight := 9 / 10) _ width_upper height_upper
  intro frame cosine_nonnegative sine_nonnegative
  apply Stromquist.weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
  exact Stromquist.boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    (by norm_num) (by norm_num)
    (Stromquist.clearancePolynomial_bentz_second_nonnegative cosine_nonnegative)

lemma weighted_bound_third {width height : ℝ}
    (width_upper : width ≤ 24 / 25) (height_upper : height ≤ 19 / 25) :
    BoundaryWeightBound width height := by
  apply BoundaryWeightBound.mono (largerWidth := 24 / 25)
    (largerHeight := 19 / 25) _ width_upper height_upper
  intro frame cosine_nonnegative sine_nonnegative
  apply Stromquist.weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
  exact Stromquist.boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    (by norm_num) (by norm_num)
    (Stromquist.clearancePolynomial_bentz_third_nonnegative cosine_nonnegative)

lemma clearancePolynomial_r3_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ Stromquist.clearancePolynomial (43 / 50) (19 / 20) cosine := by
  have cubic_nonnegative := mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 4 / 5))
  have square_nonnegative := sq_nonneg (cosine - 49361 / 54730)
  dsimp [Stromquist.clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma weighted_bound_r3 {width height : ℝ}
    (width_upper : width ≤ 43 / 50) (height_upper : height ≤ 19 / 20) :
    BoundaryWeightBound width height := by
  apply BoundaryWeightBound.mono (largerWidth := 43 / 50)
    (largerHeight := 19 / 20) _ width_upper height_upper
  intro frame cosine_nonnegative sine_nonnegative
  apply Stromquist.weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
  exact Stromquist.boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    (by norm_num) (by norm_num) (clearancePolynomial_r3_nonnegative cosine_nonnegative)

theorem contains_descending_pair
    {square : PlacedSquare} {side left width firstHeight secondHeight : ℝ}
    (fits : square.Fits side)
    (width_positive : 0 < width)
    (normalized_height_lower : 1 / 2 ≤ 1 + secondHeight - firstHeight)
    (height_order : secondHeight ≤ firstHeight) (first_height_upper : firstHeight ≤ 1)
    (distance_upper : width ^ 2 + (firstHeight - secondHeight) ^ 2 ≤ 1)
    (weighted_bound : BoundaryWeightBound width (1 + secondHeight - firstHeight))
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below : width * square.center.y ≤
      width * firstHeight + (secondHeight - firstHeight) * (square.center.x - left)) :
    square.Contains ⟨left, firstHeight⟩ ∨ square.Contains ⟨left + width, secondHeight⟩ := by
  have pair := Stromquist.contains_quadrilateral_pair (left := left) (width := width)
    (height := secondHeight + (1 - firstHeight))
    (square.translate_up_fits fits (show 0 ≤ 1 - firstHeight by linarith))
    width_positive (by linarith) (by linarith)
    (by nlinarith only [distance_upper])
    (by
      rw [show secondHeight + (1 - firstHeight) = 1 + secondHeight - firstHeight by ring]
      exact weighted_bound)
    (by simpa [PlacedSquare.translate, Point.translate] using center_x_lower)
    (by simpa [PlacedSquare.translate, Point.translate] using center_x_upper)
    (by dsimp [PlacedSquare.translate, Point.translate]; nlinarith only [center_below])
  rcases pair with first | second
  · apply Or.inl
    apply (square.translate_contains_iff 0 (1 - firstHeight) ⟨left, firstHeight⟩).1
    simpa [Point.translate] using first
  · apply Or.inr
    apply (square.translate_contains_iff 0 (1 - firstHeight) ⟨left + width, secondHeight⟩).1
    simpa [Point.translate] using second

end Bentz

end SquarePackingArchive
