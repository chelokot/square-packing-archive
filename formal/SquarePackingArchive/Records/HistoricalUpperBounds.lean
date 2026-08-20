import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.HistoricalUpperBounds

theorem s12_le_four : HasPacking 12 4 := by
  exact (SquareNumbers.squareNumber_hasPacking 4).mono (by norm_num)

theorem s68_le_brendberg_2023 :
    HasPacking 68 (((880357394752856 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square68.s68_le_8_80339 (by norm_num)

theorem s68_le_schadt_ellsworth_2025 :
    HasPacking 68 (((880345993651653 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square68.s68_le_8_80339 (by norm_num)

theorem s69_le_morandi_cantrell_2023 :
    HasPacking 69 (((882721205592900 : ℚ) / 100000000000000) : ℝ) := by
  exact HasPacking.enlarge Square69.s69_le_8_8272 (by norm_num)

end SquarePackingArchive.Records.HistoricalUpperBounds
