import SquarePackingArchive.Records.Square11
import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.HistoricalUpperBounds

theorem s12_le_four : HasPacking 12 4 := by
  exact (SquareNumbers.squareNumber_hasPacking 4).mono (by norm_num)

theorem s11_le_goebel_1979 :
    HasPacking 11 (5 / 2 + Real.sqrt 2) := by
  apply HasPacking.enlarge Square11TrumpRationalized.s11_le_3_88
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have sqrt_two_squared : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith

theorem s11_le_hamalainen_1980 :
    HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) := by
  apply HasPacking.enlarge Square11TrumpRationalized.s11_le_3_88
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have sqrt_two_squared : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith

theorem s68_le_schadt_2025 :
    HasPacking 68 (((880357394752856 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square68.s68_le_8_80339 (by norm_num)

theorem s68_le_schadt_ellsworth_2025 :
    HasPacking 68 (((880345993651653 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square68.s68_le_8_80339 (by norm_num)

theorem s69_le_morandi_cantrell_2023 :
    HasPacking 69 (((882721205592900 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square69.s69_le_8_8272 (by norm_num)

end SquarePackingArchive.Records.HistoricalUpperBounds
