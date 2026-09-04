import SquarePackingArchive.Records.Basic
import SquarePackingArchive.Records.HistoricalUpperBounds
import SquarePackingArchive.Records.NearSquare
import SquarePackingArchive.Records.Square11
import SquarePackingArchive.Records.Square15
import SquarePackingArchive.Records.Square24
import SquarePackingArchive.Records.Square46
import SquarePackingArchive.Records.Square5
import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.Square8
import SquarePackingArchive.Records.SquareNumbers

example : SquarePackingArchive.IsMinimumSide 1 (1) :=
  SquarePackingArchive.Records.Basic.s1_eq_one

example : SquarePackingArchive.IsMinimumSide 2 (2) :=
  SquarePackingArchive.Records.NearSquare.s2_eq_two

example : SquarePackingArchive.IsMinimumSide 3 (2) :=
  SquarePackingArchive.Records.NearSquare.s3_eq_two

example : SquarePackingArchive.IsMinimumSide 4 (2) :=
  SquarePackingArchive.Records.SquareNumbers.s4_eq_two

example : SquarePackingArchive.HasPacking 5 (2 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square5.s5_le_goebel

example : SquarePackingArchive.IsMinimumSide 5 (2 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square5.s5_eq_goebel

example : SquarePackingArchive.IsMinimumSide 8 (3) :=
  SquarePackingArchive.Records.Square8.s8_eq_three

example : SquarePackingArchive.IsMinimumSide 9 (3) :=
  SquarePackingArchive.Records.SquareNumbers.s9_eq_three

example : SquarePackingArchive.HasPacking 11 (5 / 2 + Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_goebel_1979

example : SquarePackingArchive.HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_hamalainen_1980

example : SquarePackingArchive.HasPacking 11 (((97 : ℚ) / 25 : ℝ)) :=
  SquarePackingArchive.Records.Square11TrumpRationalized.s11_le_3_88

example : SquarePackingArchive.HasPacking 12 (4) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s12_le_four

example : SquarePackingArchive.IsMinimumSide 15 (4) :=
  SquarePackingArchive.Records.Square15.s15_eq_four

example : SquarePackingArchive.IsMinimumSide 16 (4) :=
  SquarePackingArchive.Records.SquareNumbers.s16_eq_four

example : SquarePackingArchive.IsMinimumSide 24 (5) :=
  SquarePackingArchive.Records.Square24.s24_eq_five

example : SquarePackingArchive.IsMinimumSide 25 (5) :=
  SquarePackingArchive.Records.SquareNumbers.s25_eq_five

example : SquarePackingArchive.IsMinimumSide 36 (6) :=
  SquarePackingArchive.Records.SquareNumbers.s36_eq_six

example : SquarePackingArchive.IsMinimumSide 46 (7) :=
  SquarePackingArchive.Records.Square46.s46_eq_seven

example : SquarePackingArchive.IsMinimumSide 47 (7) :=
  SquarePackingArchive.Records.Square46.s47_eq_seven

example : SquarePackingArchive.IsMinimumSide 48 (7) :=
  SquarePackingArchive.Records.Square46.s48_eq_seven

example : SquarePackingArchive.IsMinimumSide 49 (7) :=
  SquarePackingArchive.Records.SquareNumbers.s49_eq_seven

example : SquarePackingArchive.IsMinimumSide 64 (8) :=
  SquarePackingArchive.Records.SquareNumbers.s64_eq_eight

example : SquarePackingArchive.HasPacking 68 (((880357394752856 : ℚ) / 100000000000000 : ℝ)) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s68_le_brendberg_2023

example : SquarePackingArchive.HasPacking 68 (((880345993651653 : ℚ) / 100000000000000 : ℝ)) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s68_le_schadt_ellsworth_2025

example : SquarePackingArchive.HasPacking 68 (((880339 : ℚ) / 100000 : ℝ)) :=
  SquarePackingArchive.Records.Square68.s68_le_8_80339

example : SquarePackingArchive.HasPacking 69 (((882721205592900 : ℚ) / 100000000000000 : ℝ)) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s69_le_morandi_cantrell_2023

example : SquarePackingArchive.HasPacking 69 (((5517 : ℚ) / 625 : ℝ)) :=
  SquarePackingArchive.Records.Square69.s69_le_8_8272

example : SquarePackingArchive.IsMinimumSide 81 (9) :=
  SquarePackingArchive.Records.SquareNumbers.s81_eq_nine
