import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69

/-!
Historical upper-bound values certified by enlarging stronger verified packings.
These proofs do not reconstruct the historical coordinate sets.
-/

namespace SquarePackingArchive.Records.HistoricalRadicalBounds

theorem s68_le_stenlund_1980 : HasPacking 68 (6 + 2 * Real.sqrt 2) := by
  apply HasPacking.enlarge Square68.s68_le_8_80339
  have sqrt_two_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have sqrt_two_squared : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  norm_num
  nlinarith

theorem s68_le_cantrell_2002 : HasPacking 68 (15 / 2 + Real.sqrt 7 / 2) := by
  apply HasPacking.enlarge Square68.s68_le_8_80339
  have sqrt_seven_nonnegative := Real.sqrt_nonneg (7 : ℝ)
  have sqrt_seven_squared : (Real.sqrt 7) ^ 2 = 7 := by norm_num
  norm_num
  nlinarith

theorem s68_le_brendberg_2023 : HasPacking 68 (13 / 3 + 2 * Real.sqrt 5) := by
  apply HasPacking.enlarge Square68.s68_le_8_80339
  have sqrt_five_nonnegative := Real.sqrt_nonneg (5 : ℝ)
  have sqrt_five_squared : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  norm_num
  nlinarith

theorem s69_le_friedman_1997 : HasPacking 69 (5 / 2 + 9 * Real.sqrt 2 / 2) := by
  apply HasPacking.enlarge Square69.s69_le_8_8272
  have sqrt_two_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have sqrt_two_squared : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  norm_num
  nlinarith

end SquarePackingArchive.Records.HistoricalRadicalBounds
