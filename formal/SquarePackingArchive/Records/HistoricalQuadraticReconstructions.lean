import SquarePackingArchive.Records.Square11Goebel1979
import SquarePackingArchive.Records.Square11Hamalainen1980
import SquarePackingArchive.Records.Square68Stenlund1980
import SquarePackingArchive.Records.Square69Friedman1997

namespace SquarePackingArchive.Records.HistoricalQuadraticReconstructions

theorem s11_le_goebel_1979 : HasPacking 11 (5 / 2 + Real.sqrt 2) := by
  convert Square11Goebel1979.upper_bound using 1
  norm_num

theorem s11_le_hamalainen_1980 : HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) := by
  convert Square11Hamalainen1980.upper_bound using 1
  norm_num
  ring

theorem s68_le_stenlund_1980 : HasPacking 68 (6 + 2 * Real.sqrt 2) := by
  convert Square68Stenlund1980.upper_bound using 1
  norm_num

theorem s69_le_friedman_1997 : HasPacking 69 (5 / 2 + 9 * Real.sqrt 2 / 2) := by
  convert Square69Friedman1997.upper_bound using 1
  norm_num
  ring

end SquarePackingArchive.Records.HistoricalQuadraticReconstructions
