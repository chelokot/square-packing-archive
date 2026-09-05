import SquarePackingArchive.NagamochiAugmented
import SquarePackingArchive.NagamochiPackingTheorem
import SquarePackingArchive.Records.Basic
import SquarePackingArchive.Records.HistoricalUpperBounds
import SquarePackingArchive.Records.NearSquare
import SquarePackingArchive.Records.Square10
import SquarePackingArchive.Records.Square11
import SquarePackingArchive.Records.Square15
import SquarePackingArchive.Records.Square23
import SquarePackingArchive.Records.Square24
import SquarePackingArchive.Records.Square34
import SquarePackingArchive.Records.Square46
import SquarePackingArchive.Records.Square5
import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.Square7
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

example : SquarePackingArchive.IsMinimumSide 7 (3) :=
  SquarePackingArchive.Records.Square7.s7_eq_three

example : SquarePackingArchive.IsMinimumSide 8 (3) :=
  SquarePackingArchive.Records.Square8.s8_eq_three

example : SquarePackingArchive.IsMinimumSide 9 (3) :=
  SquarePackingArchive.Records.SquareNumbers.s9_eq_three

example : SquarePackingArchive.HasPacking 10 (3 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square10.s10_le_goebel

example : SquarePackingArchive.HasPacking 11 (5 / 2 + Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_goebel_1979

example : SquarePackingArchive.HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_hamalainen_1980

example : SquarePackingArchive.HasPacking 11 (((97 : ℚ) / 25 : ℝ)) :=
  SquarePackingArchive.Records.Square11TrumpRationalized.s11_le_3_88

example : SquarePackingArchive.HasPacking 12 (4) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s12_le_four

example : SquarePackingArchive.IsMinimumSide 14 (4) :=
  SquarePackingArchive.Records.NearSquare.s14_eq_four

example : SquarePackingArchive.IsMinimumSide 15 (4) :=
  SquarePackingArchive.Records.Square15.s15_eq_four

example : SquarePackingArchive.IsMinimumSide 16 (4) :=
  SquarePackingArchive.Records.SquareNumbers.s16_eq_four

example : SquarePackingArchive.IsMinimumSide 23 (5) :=
  SquarePackingArchive.Records.Square23.s23_eq_five

example : SquarePackingArchive.IsMinimumSide 24 (5) :=
  SquarePackingArchive.Records.Square24.s24_eq_five

example : SquarePackingArchive.IsMinimumSide 25 (5) :=
  SquarePackingArchive.Records.SquareNumbers.s25_eq_five

example : SquarePackingArchive.IsMinimumSide 34 (6) :=
  SquarePackingArchive.Records.Square34.s34_eq_six

example : SquarePackingArchive.IsMinimumSide 35 (6) :=
  SquarePackingArchive.Records.Square34.s35_eq_six

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

example : SquarePackingArchive.IsMinimumSide 62 (8) :=
  SquarePackingArchive.Records.NearSquare.s62_eq_eight

example : SquarePackingArchive.IsMinimumSide 63 (8) :=
  SquarePackingArchive.Records.NearSquare.s63_eq_eight

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

example : SquarePackingArchive.IsMinimumSide 79 (9) :=
  SquarePackingArchive.Records.NearSquare.s79_eq_nine

example : SquarePackingArchive.IsMinimumSide 80 (9) :=
  SquarePackingArchive.Records.NearSquare.s80_eq_nine

example : SquarePackingArchive.IsMinimumSide 81 (9) :=
  SquarePackingArchive.Records.SquareNumbers.s81_eq_nine

example : SquarePackingArchive.IsMinimumSide 98 (10) :=
  SquarePackingArchive.Records.NearSquare.s98_eq_ten

example : SquarePackingArchive.IsMinimumSide 99 (10) :=
  SquarePackingArchive.Records.NearSquare.s99_eq_ten

example : SquarePackingArchive.HasPacking 1 1 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 1) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 1) (by norm_num)

example : SquarePackingArchive.HasPacking 2 2 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 2) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 2) (by norm_num)

example : SquarePackingArchive.HasPacking 3 2 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 3) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 2) (by norm_num)

example : SquarePackingArchive.HasPacking 4 2 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 4) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 2) (by norm_num)

example : SquarePackingArchive.HasPacking 6 3 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 6) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 3) (by norm_num)

example : SquarePackingArchive.HasPacking 7 3 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 7) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 3) (by norm_num)

example : SquarePackingArchive.HasPacking 8 3 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 8) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 3) (by norm_num)

example : SquarePackingArchive.HasPacking 9 3 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 9) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 3) (by norm_num)

example : SquarePackingArchive.HasPacking 12 4 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 12) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 4) (by norm_num)

example : SquarePackingArchive.HasPacking 13 4 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 13) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 4) (by norm_num)

example : SquarePackingArchive.HasPacking 14 4 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 14) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 4) (by norm_num)

example : SquarePackingArchive.HasPacking 15 4 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 15) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 4) (by norm_num)

example : SquarePackingArchive.HasPacking 16 4 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 16) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 4) (by norm_num)

example : SquarePackingArchive.HasPacking 22 5 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 22) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 5) (by norm_num)

example : SquarePackingArchive.HasPacking 23 5 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 23) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 5) (by norm_num)

example : SquarePackingArchive.HasPacking 24 5 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 24) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 5) (by norm_num)

example : SquarePackingArchive.HasPacking 25 5 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 25) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 5) (by norm_num)

example : SquarePackingArchive.HasPacking 33 6 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 33) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 6) (by norm_num)

example : SquarePackingArchive.HasPacking 34 6 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 34) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 6) (by norm_num)

example : SquarePackingArchive.HasPacking 35 6 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 35) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 6) (by norm_num)

example : SquarePackingArchive.HasPacking 36 6 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 36) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 6) (by norm_num)

example : SquarePackingArchive.HasPacking 46 7 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 46) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 7) (by norm_num)

example : SquarePackingArchive.HasPacking 47 7 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 47) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 7) (by norm_num)

example : SquarePackingArchive.HasPacking 48 7 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 48) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 7) (by norm_num)

example : SquarePackingArchive.HasPacking 49 7 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 49) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 7) (by norm_num)

example : SquarePackingArchive.HasPacking 62 8 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 62) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 8) (by norm_num)

example : SquarePackingArchive.HasPacking 63 8 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 63) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 8) (by norm_num)

example : SquarePackingArchive.HasPacking 64 8 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 64) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 8) (by norm_num)

example : SquarePackingArchive.HasPacking 79 9 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 79) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 9) (by norm_num)

example : SquarePackingArchive.HasPacking 80 9 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 80) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 9) (by norm_num)

example : SquarePackingArchive.HasPacking 81 9 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 81) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 9) (by norm_num)

example : SquarePackingArchive.HasPacking 98 10 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 98) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 10) (by norm_num)

example : SquarePackingArchive.HasPacking 99 10 := by
  simpa using SquarePackingArchive.HasPacking.mono (targetCount := 99) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking 10) (by norm_num)
