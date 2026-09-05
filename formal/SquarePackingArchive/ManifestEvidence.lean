import SquarePackingArchive.NagamochiAugmented
import SquarePackingArchive.NagamochiPackingTheorem
import SquarePackingArchive.Records.Basic
import SquarePackingArchive.Records.GridBounds
import SquarePackingArchive.Records.HistoricalUpperBounds
import SquarePackingArchive.Records.NearSquare
import SquarePackingArchive.Records.Square10
import SquarePackingArchive.Records.Square10Exact
import SquarePackingArchive.Records.Square11
import SquarePackingArchive.Records.Square13Exact
import SquarePackingArchive.Records.Square15
import SquarePackingArchive.Records.Square22
import SquarePackingArchive.Records.Square23
import SquarePackingArchive.Records.Square24
import SquarePackingArchive.Records.Square33
import SquarePackingArchive.Records.Square34
import SquarePackingArchive.Records.Square46
import SquarePackingArchive.Records.Square5
import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.Square6Exact
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

example : SquarePackingArchive.IsMinimumSide 6 (3) :=
  SquarePackingArchive.Records.Square6.s6_eq_three

example : SquarePackingArchive.IsMinimumSide 7 (3) :=
  SquarePackingArchive.Records.Square7.s7_eq_three

example : SquarePackingArchive.IsMinimumSide 8 (3) :=
  SquarePackingArchive.Records.Square8.s8_eq_three

example : SquarePackingArchive.IsMinimumSide 9 (3) :=
  SquarePackingArchive.Records.SquareNumbers.s9_eq_three

example : SquarePackingArchive.HasPacking 10 (3 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square10.s10_le_goebel

example : SquarePackingArchive.IsMinimumSide 10 (3 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square10.s10_eq_goebel

example : SquarePackingArchive.HasPacking 11 (5 / 2 + Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_goebel_1979

example : SquarePackingArchive.HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_hamalainen_1980

example : SquarePackingArchive.HasPacking 11 (((97 : ℚ) / 25 : ℝ)) :=
  SquarePackingArchive.Records.Square11TrumpRationalized.s11_le_3_88

example : SquarePackingArchive.HasPacking 12 (4) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s12_le_four

example : SquarePackingArchive.IsMinimumSide 13 (4) :=
  SquarePackingArchive.Records.Square13.s13_eq_four

example : SquarePackingArchive.IsMinimumSide 14 (4) :=
  SquarePackingArchive.Records.NearSquare.s14_eq_four

example : SquarePackingArchive.IsMinimumSide 15 (4) :=
  SquarePackingArchive.Records.Square15.s15_eq_four

example : SquarePackingArchive.IsMinimumSide 16 (4) :=
  SquarePackingArchive.Records.SquareNumbers.s16_eq_four

example : SquarePackingArchive.IsMinimumSide 22 (5) :=
  SquarePackingArchive.Records.Square22.s22_eq_five

example : SquarePackingArchive.IsMinimumSide 23 (5) :=
  SquarePackingArchive.Records.Square23.s23_eq_five

example : SquarePackingArchive.IsMinimumSide 24 (5) :=
  SquarePackingArchive.Records.Square24.s24_eq_five

example : SquarePackingArchive.IsMinimumSide 25 (5) :=
  SquarePackingArchive.Records.SquareNumbers.s25_eq_five

example : SquarePackingArchive.IsMinimumSide 33 (6) :=
  SquarePackingArchive.Records.Square33.s33_eq_six

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

example : SquarePackingArchive.HasPacking 1 1 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 1) (side := 1) (by norm_num)

example : SquarePackingArchive.HasPacking 2 2 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 2) (side := 2) (by norm_num)

example : SquarePackingArchive.HasPacking 3 2 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 3) (side := 2) (by norm_num)

example : SquarePackingArchive.HasPacking 4 2 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 4) (side := 2) (by norm_num)

example : SquarePackingArchive.HasPacking 5 3 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 5) (side := 3) (by norm_num)

example : SquarePackingArchive.HasPacking 6 3 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 6) (side := 3) (by norm_num)

example : SquarePackingArchive.HasPacking 7 3 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 7) (side := 3) (by norm_num)

example : SquarePackingArchive.HasPacking 8 3 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 8) (side := 3) (by norm_num)

example : SquarePackingArchive.HasPacking 9 3 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 9) (side := 3) (by norm_num)

example : SquarePackingArchive.HasPacking 10 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 10) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 11 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 11) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 12 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 12) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 13 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 13) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 14 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 14) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 15 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 15) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 16 4 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 16) (side := 4) (by norm_num)

example : SquarePackingArchive.HasPacking 17 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 17) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 18 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 18) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 19 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 19) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 20 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 20) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 21 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 21) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 22 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 22) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 23 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 23) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 24 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 24) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 25 5 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 25) (side := 5) (by norm_num)

example : SquarePackingArchive.HasPacking 26 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 26) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 27 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 27) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 28 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 28) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 29 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 29) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 30 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 30) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 31 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 31) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 32 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 32) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 33 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 33) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 34 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 34) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 35 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 35) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 36 6 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 36) (side := 6) (by norm_num)

example : SquarePackingArchive.HasPacking 37 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 37) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 38 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 38) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 39 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 39) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 40 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 40) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 41 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 41) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 42 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 42) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 43 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 43) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 44 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 44) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 45 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 45) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 46 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 46) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 47 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 47) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 48 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 48) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 49 7 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 49) (side := 7) (by norm_num)

example : SquarePackingArchive.HasPacking 50 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 50) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 51 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 51) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 52 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 52) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 53 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 53) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 54 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 54) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 55 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 55) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 56 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 56) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 57 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 57) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 58 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 58) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 59 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 59) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 60 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 60) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 61 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 61) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 62 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 62) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 63 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 63) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 64 8 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 64) (side := 8) (by norm_num)

example : SquarePackingArchive.HasPacking 65 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 65) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 66 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 66) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 67 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 67) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 68 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 68) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 69 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 69) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 70 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 70) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 71 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 71) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 72 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 72) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 73 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 73) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 74 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 74) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 75 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 75) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 76 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 76) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 77 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 77) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 78 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 78) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 79 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 79) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 80 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 80) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 81 9 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 81) (side := 9) (by norm_num)

example : SquarePackingArchive.HasPacking 82 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 82) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 83 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 83) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 84 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 84) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 85 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 85) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 86 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 86) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 87 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 87) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 88 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 88) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 89 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 89) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 90 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 90) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 91 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 91) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 92 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 92) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 93 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 93) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 94 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 94) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 95 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 95) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 96 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 96) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 97 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 97) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 98 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 98) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 99 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 99) (side := 10) (by norm_num)

example : SquarePackingArchive.HasPacking 100 10 := by
  simpa using SquarePackingArchive.Records.GridBounds.grid_hasPacking (count := 100) (side := 10) (by norm_num)
