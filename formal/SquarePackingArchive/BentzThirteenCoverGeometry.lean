import SquarePackingArchive.BentzBoundaryPairs
import SquarePackingArchive.Records.Square13

namespace SquarePackingArchive.BentzThirteen

theorem contains_of_center_box {square : PlacedSquare} {point : Point}
    {horizontalRadius verticalRadius : ℝ}
    (radius_bound : horizontalRadius ^ 2 + verticalRadius ^ 2 ≤ 1 / 4)
    (horizontal_lower : point.x - horizontalRadius ≤ square.center.x)
    (horizontal_upper : square.center.x ≤ point.x + horizontalRadius)
    (vertical_lower : point.y - verticalRadius ≤ square.center.y)
    (vertical_upper : square.center.y ≤ point.y + verticalRadius) :
    square.Contains point := by
  apply Records.Square13.contains_of_center_distance_sq_le_quarter
  have horizontal_product := mul_nonneg
    (show 0 ≤ square.center.x - point.x + horizontalRadius by linarith)
    (show 0 ≤ point.x + horizontalRadius - square.center.x by linarith)
  have vertical_product := mul_nonneg
    (show 0 ≤ square.center.y - point.y + verticalRadius by linarith)
    (show 0 ≤ point.y + verticalRadius - square.center.y by linarith)
  nlinarith only [horizontal_product, vertical_product, radius_bound]

theorem center_inside_half_margin {square : PlacedSquare} (fits : square.Fits 4) :
    1 / 2 ≤ square.center.x ∧ square.center.x ≤ 7 / 2 ∧
    1 / 2 ≤ square.center.y ∧ square.center.y ≤ 7 / 2 := by
  have bounds := square.center_bounds fits
  have unit := square.frame.unit
  have nonnegative : 0 ≤ |square.frame.cosine| + |square.frame.sine| := by positivity
  have extent_lower : 1 / 2 ≤ frameExtent square.frame := by
    dsimp [frameExtent]
    nlinarith [sq_abs square.frame.cosine, sq_abs square.frame.sine,
      mul_nonneg (abs_nonneg square.frame.cosine) (abs_nonneg square.frame.sine)]
  exact ⟨by linarith [bounds.1], by linarith [bounds.2.1],
    by linarith [bounds.2.2.1], by linarith [bounds.2.2.2]⟩

end SquarePackingArchive.BentzThirteen
