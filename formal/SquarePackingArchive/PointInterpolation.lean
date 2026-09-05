import SquarePackingArchive.TriangleRegions

namespace SquarePackingArchive

def Point.interpolate (first second : Point) (parameter : ℝ) : Point :=
  ⟨(1 - parameter) * first.x + parameter * second.x,
    (1 - parameter) * first.y + parameter * second.y⟩

def Point.squaredDistance (first second : Point) : ℝ :=
  (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2

lemma Point.squaredDistance_comm (first second : Point) :
    first.squaredDistance second = second.squaredDistance first := by
  dsimp [Point.squaredDistance]
  ring

lemma Point.interpolate_squaredDistance_le
    (first second target : Point) {parameter bound : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_upper : parameter ≤ 1)
    (first_bound : first.squaredDistance target ≤ bound)
    (second_bound : second.squaredDistance target ≤ bound) :
    (first.interpolate second parameter).squaredDistance target ≤ bound := by
  have gap_nonnegative := mul_nonneg
    (mul_nonneg parameter_nonnegative (show 0 ≤ 1 - parameter by linarith))
    (show 0 ≤ first.squaredDistance second by dsimp [Point.squaredDistance]; positivity)
  have first_weighted := mul_nonneg (show 0 ≤ 1 - parameter by linarith)
    (show 0 ≤ bound - first.squaredDistance target by linarith)
  have second_weighted := mul_nonneg parameter_nonnegative
    (show 0 ≤ bound - second.squaredDistance target by linarith)
  have identity :
      (first.interpolate second parameter).squaredDistance target =
      (1 - parameter) * first.squaredDistance target + parameter * second.squaredDistance target -
        parameter * (1 - parameter) * first.squaredDistance second := by
    dsimp [Point.interpolate, Point.squaredDistance]
    ring
  nlinarith only [gap_nonnegative, first_weighted, second_weighted, identity]

lemma Point.interpolate_pair_squaredDistance_le
    (firstStart firstEnd secondStart secondEnd : Point) {firstParameter secondParameter bound : ℝ}
    (first_nonnegative : 0 ≤ firstParameter) (first_upper : firstParameter ≤ 1)
    (second_nonnegative : 0 ≤ secondParameter) (second_upper : secondParameter ≤ 1)
    (start_start : firstStart.squaredDistance secondStart ≤ bound)
    (start_end : firstStart.squaredDistance secondEnd ≤ bound)
    (end_start : firstEnd.squaredDistance secondStart ≤ bound)
    (end_end : firstEnd.squaredDistance secondEnd ≤ bound) :
    (firstStart.interpolate firstEnd firstParameter).squaredDistance
      (secondStart.interpolate secondEnd secondParameter) ≤ bound := by
  apply Point.interpolate_squaredDistance_le _ _ _ first_nonnegative first_upper
  · rw [Point.squaredDistance_comm]
    exact Point.interpolate_squaredDistance_le _ _ _ second_nonnegative second_upper
      (by simpa only [Point.squaredDistance_comm] using start_start)
      (by simpa only [Point.squaredDistance_comm] using start_end)
  · rw [Point.squaredDistance_comm]
    exact Point.interpolate_squaredDistance_le _ _ _ second_nonnegative second_upper
      (by simpa only [Point.squaredDistance_comm] using end_start)
      (by simpa only [Point.squaredDistance_comm] using end_end)

lemma Point.interpolate_pair_orientedArea_lower
    (origin firstStart firstEnd secondStart secondEnd : Point)
    {firstParameter secondParameter bound : ℝ}
    (first_nonnegative : 0 ≤ firstParameter) (first_upper : firstParameter ≤ 1)
    (second_nonnegative : 0 ≤ secondParameter) (second_upper : secondParameter ≤ 1)
    (start_start : bound ≤ Point.orientedArea origin firstStart secondStart)
    (start_end : bound ≤ Point.orientedArea origin firstStart secondEnd)
    (end_start : bound ≤ Point.orientedArea origin firstEnd secondStart)
    (end_end : bound ≤ Point.orientedArea origin firstEnd secondEnd) :
    bound ≤ Point.orientedArea origin (firstStart.interpolate firstEnd firstParameter)
      (secondStart.interpolate secondEnd secondParameter) := by
  have first_complement : 0 ≤ 1 - firstParameter := by linarith
  have second_complement : 0 ≤ 1 - secondParameter := by linarith
  have first_weighted := mul_nonneg (mul_nonneg first_complement second_complement)
    (sub_nonneg.mpr start_start)
  have second_weighted := mul_nonneg (mul_nonneg first_complement second_nonnegative)
    (sub_nonneg.mpr start_end)
  have third_weighted := mul_nonneg (mul_nonneg first_nonnegative second_complement)
    (sub_nonneg.mpr end_start)
  have fourth_weighted := mul_nonneg (mul_nonneg first_nonnegative second_nonnegative)
    (sub_nonneg.mpr end_end)
  have identity :
      Point.orientedArea origin (firstStart.interpolate firstEnd firstParameter)
        (secondStart.interpolate secondEnd secondParameter) - bound =
      (1 - firstParameter) * (1 - secondParameter) *
        (Point.orientedArea origin firstStart secondStart - bound) +
      (1 - firstParameter) * secondParameter *
        (Point.orientedArea origin firstStart secondEnd - bound) +
      firstParameter * (1 - secondParameter) *
        (Point.orientedArea origin firstEnd secondStart - bound) +
      firstParameter * secondParameter *
        (Point.orientedArea origin firstEnd secondEnd - bound) := by
    dsimp [Point.interpolate, Point.orientedArea]
    ring
  linarith only [identity, first_weighted, second_weighted, third_weighted, fourth_weighted]

end SquarePackingArchive
