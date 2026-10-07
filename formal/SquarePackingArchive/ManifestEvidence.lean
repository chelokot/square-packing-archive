import SquarePackingArchive.EvidenceAudit
import SquarePackingArchive.NagamochiAugmented
import SquarePackingArchive.NagamochiPackingTheorem
import SquarePackingArchive.Records.GoebelStrip
import SquarePackingArchive.Records.HistoricalQuadraticReconstructions
import SquarePackingArchive.Records.HistoricalRadicalBounds
import SquarePackingArchive.Records.HistoricalUpperBounds
import SquarePackingArchive.Records.Square10
import SquarePackingArchive.Records.Square10Exact
import SquarePackingArchive.Records.Square11
import SquarePackingArchive.Records.Square13Exact
import SquarePackingArchive.Records.Square15
import SquarePackingArchive.Records.Square17Hamalainen1980
import SquarePackingArchive.Records.Square18Cantrell
import SquarePackingArchive.Records.Square18GensaneRyckelynck
import SquarePackingArchive.Records.Square18Gustafsson
import SquarePackingArchive.Records.Square18Hamalainen
import SquarePackingArchive.Records.Square19Cottingham1979
import SquarePackingArchive.Records.Square19Goebel1979
import SquarePackingArchive.Records.Square19Tracker
import SquarePackingArchive.Records.Square22
import SquarePackingArchive.Records.Square23
import SquarePackingArchive.Records.Square24
import SquarePackingArchive.Records.Square26Tracker
import SquarePackingArchive.Records.Square33
import SquarePackingArchive.Records.Square34
import SquarePackingArchive.Records.Square40Tracker
import SquarePackingArchive.Records.Square46
import SquarePackingArchive.Records.Square5
import SquarePackingArchive.Records.Square50SchadtEllsworth
import SquarePackingArchive.Records.Square53EllsworthReconstructed
import SquarePackingArchive.Records.Square65Tracker
import SquarePackingArchive.Records.Square66Tracker
import SquarePackingArchive.Records.Square68
import SquarePackingArchive.Records.Square69
import SquarePackingArchive.Records.Square82Tracker
import SquarePackingArchive.Records.Square85Tracker
import SquarePackingArchive.Records.Square86Friedman
import SquarePackingArchive.Records.Square89Tracker

example : SquarePackingArchive.HasPacking 5 (2 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square5.s5_le_goebel

example : SquarePackingArchive.IsMinimumSide 5 (2 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square5.s5_eq_goebel

example : SquarePackingArchive.HasPacking 10 (3 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square10.s10_le_goebel

example : SquarePackingArchive.IsMinimumSide 10 (3 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.Square10.s10_eq_goebel

example : SquarePackingArchive.HasPacking 11 (5 / 2 + Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_goebel_1979

example : SquarePackingArchive.HasPacking 11 (5 / 2 + Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s11_le_goebel_1979

example : SquarePackingArchive.HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_hamalainen_1980

example : SquarePackingArchive.HasPacking 11 (2 + 4 * Real.sqrt 2 / 3) :=
  SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s11_le_hamalainen_1980

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

example : SquarePackingArchive.IsMinimumSide 22 (5) :=
  SquarePackingArchive.Records.Square22.s22_eq_five

example : SquarePackingArchive.IsMinimumSide 23 (5) :=
  SquarePackingArchive.Records.Square23.s23_eq_five

example : SquarePackingArchive.IsMinimumSide 24 (5) :=
  SquarePackingArchive.Records.Square24.s24_eq_five

example : SquarePackingArchive.IsMinimumSide 33 (6) :=
  SquarePackingArchive.Records.Square33.s33_eq_six

example : SquarePackingArchive.IsMinimumSide 34 (6) :=
  SquarePackingArchive.Records.Square34.s34_eq_six

example : SquarePackingArchive.IsMinimumSide 35 (6) :=
  SquarePackingArchive.Records.Square34.s35_eq_six

example : SquarePackingArchive.IsMinimumSide 46 (7) :=
  SquarePackingArchive.Records.Square46.s46_eq_seven

example : SquarePackingArchive.IsMinimumSide 47 (7) :=
  SquarePackingArchive.Records.Square46.s47_eq_seven

example : SquarePackingArchive.IsMinimumSide 48 (7) :=
  SquarePackingArchive.Records.Square46.s48_eq_seven

example : SquarePackingArchive.IsMinimumSide 62 (8) :=
  SquarePackingArchive.Records.NearSquare.s62_eq_eight

example : SquarePackingArchive.IsMinimumSide 63 (8) :=
  SquarePackingArchive.Records.NearSquare.s63_eq_eight

example : SquarePackingArchive.HasPacking 68 (((880357394752856 : ℚ) / 100000000000000 : ℝ)) :=
  SquarePackingArchive.Records.HistoricalUpperBounds.s68_le_schadt_2025

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

example : SquarePackingArchive.IsMinimumSide 98 (10) :=
  SquarePackingArchive.Records.NearSquare.s98_eq_ten

example : SquarePackingArchive.IsMinimumSide 99 (10) :=
  SquarePackingArchive.Records.NearSquare.s99_eq_ten

example : SquarePackingArchive.HasPacking 50 (((53 : ℚ) / 7 : ℝ)) :=
  SquarePackingArchive.Records.Square50SchadtEllsworth.s50_le_7_57142857142857

example : SquarePackingArchive.HasPacking 27 (5 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.GoebelStrip.s27_le_goebel

example : SquarePackingArchive.HasPacking 38 (6 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.GoebelStrip.s38_le_goebel

example : SquarePackingArchive.HasPacking 52 (7 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.GoebelStrip.s52_le_goebel

example : SquarePackingArchive.HasPacking 67 (8 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.GoebelStrip.s67_le_goebel

example : SquarePackingArchive.HasPacking 84 (9 + Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.GoebelStrip.s84_le_goebel

example : SquarePackingArchive.HasPacking 68 (6 + 2 * Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_stenlund_1980

example : SquarePackingArchive.HasPacking 68 (6 + 2 * Real.sqrt 2) :=
  SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s68_le_stenlund_1980

example : SquarePackingArchive.HasPacking 68 (15 / 2 + Real.sqrt 7 / 2) :=
  SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_cantrell_2002

example : SquarePackingArchive.HasPacking 68 (13 / 3 + 2 * Real.sqrt 5) :=
  SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_brendberg_2023

example : SquarePackingArchive.HasPacking 69 (5 / 2 + 9 * Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.HistoricalRadicalBounds.s69_le_friedman_1997

example : SquarePackingArchive.HasPacking 69 (5 / 2 + 9 * Real.sqrt 2 / 2) :=
  SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s69_le_friedman_1997

example : SquarePackingArchive.HasPacking 17 ((((7 : ℚ) / 3) : ℝ) + (((5 : ℚ) / 3) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square17Hamalainen1980.upper_bound

example : SquarePackingArchive.HasPacking 18 ((((7 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square18Hamalainen.upper_bound

example : SquarePackingArchive.HasPacking 18 ((((7 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square18Gustafsson.upper_bound

example : SquarePackingArchive.HasPacking 18 ((((7 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square18Cantrell.upper_bound

example : SquarePackingArchive.HasPacking 18 ((((7 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square18GensaneRyckelynck.upper_bound

example : SquarePackingArchive.HasPacking 19 (((4 : ℚ) : ℝ) + (((2 : ℚ) / 3) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square19Goebel1979.upper_bound

example : SquarePackingArchive.HasPacking 19 ((((7 : ℚ) / 2) : ℝ) + ((1 : ℚ) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square19Cottingham1979.upper_bound

example : SquarePackingArchive.HasPacking 19 (((3 : ℚ) : ℝ) + (((4 : ℚ) / 3) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square19Tracker.upper_bound

example : SquarePackingArchive.HasPacking 26 ((((7 : ℚ) / 2) : ℝ) + (((3 : ℚ) / 2) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square26Tracker.upper_bound

example : SquarePackingArchive.HasPacking 40 (((4 : ℚ) : ℝ) + ((2 : ℚ) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square40Tracker.upper_bound

example : SquarePackingArchive.HasPacking 53 ((((13 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square53EllsworthReconstructed.upper_bound

example : SquarePackingArchive.HasPacking 65 (((5 : ℚ) : ℝ) + (((5 : ℚ) / 2) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square65Tracker.upper_bound

example : SquarePackingArchive.HasPacking 66 (((3 : ℚ) : ℝ) + ((4 : ℚ) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square66Tracker.upper_bound

example : SquarePackingArchive.HasPacking 82 (((6 : ℚ) : ℝ) + (((5 : ℚ) / 2) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square82Tracker.upper_bound

example : SquarePackingArchive.HasPacking 85 ((((11 : ℚ) / 2) : ℝ) + ((3 : ℚ) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square85Tracker.upper_bound

example : SquarePackingArchive.HasPacking 86 ((((17 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) :=
  SquarePackingArchive.Records.Square86Friedman.upper_bound

example : SquarePackingArchive.HasPacking 89 (((5 : ℚ) : ℝ) + (((7 : ℚ) / 2) : ℝ) * Real.sqrt 2) :=
  SquarePackingArchive.Records.Square89Tracker.upper_bound

assert_standard_axioms SquarePackingArchive.Records.GoebelStrip.s27_le_goebel
assert_standard_axioms SquarePackingArchive.Records.GoebelStrip.s38_le_goebel
assert_standard_axioms SquarePackingArchive.Records.GoebelStrip.s52_le_goebel
assert_standard_axioms SquarePackingArchive.Records.GoebelStrip.s67_le_goebel
assert_standard_axioms SquarePackingArchive.Records.GoebelStrip.s84_le_goebel
assert_standard_axioms SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s11_le_goebel_1979
assert_standard_axioms SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s11_le_hamalainen_1980
assert_standard_axioms SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s68_le_stenlund_1980
assert_standard_axioms SquarePackingArchive.Records.HistoricalQuadraticReconstructions.s69_le_friedman_1997
assert_standard_axioms SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_brendberg_2023
assert_standard_axioms SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_cantrell_2002
assert_standard_axioms SquarePackingArchive.Records.HistoricalRadicalBounds.s68_le_stenlund_1980
assert_standard_axioms SquarePackingArchive.Records.HistoricalRadicalBounds.s69_le_friedman_1997
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_goebel_1979
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s11_le_hamalainen_1980
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s12_le_four
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s68_le_schadt_2025
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s68_le_schadt_ellsworth_2025
assert_standard_axioms SquarePackingArchive.Records.HistoricalUpperBounds.s69_le_morandi_cantrell_2023
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s14_eq_four
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s62_eq_eight
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s63_eq_eight
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s79_eq_nine
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s80_eq_nine
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s98_eq_ten
assert_standard_axioms SquarePackingArchive.Records.NearSquare.s99_eq_ten
assert_standard_axioms SquarePackingArchive.Records.Square10.s10_eq_goebel
assert_standard_axioms SquarePackingArchive.Records.Square10.s10_le_goebel
assert_standard_axioms SquarePackingArchive.Records.Square11TrumpRationalized.s11_le_3_88
assert_standard_axioms SquarePackingArchive.Records.Square13.s13_eq_four
assert_standard_axioms SquarePackingArchive.Records.Square15.s15_eq_four
assert_standard_axioms SquarePackingArchive.Records.Square17Hamalainen1980.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square18Cantrell.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square18GensaneRyckelynck.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square18Gustafsson.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square18Hamalainen.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square19Cottingham1979.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square19Goebel1979.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square19Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square22.s22_eq_five
assert_standard_axioms SquarePackingArchive.Records.Square23.s23_eq_five
assert_standard_axioms SquarePackingArchive.Records.Square24.s24_eq_five
assert_standard_axioms SquarePackingArchive.Records.Square26Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square33.s33_eq_six
assert_standard_axioms SquarePackingArchive.Records.Square34.s34_eq_six
assert_standard_axioms SquarePackingArchive.Records.Square34.s35_eq_six
assert_standard_axioms SquarePackingArchive.Records.Square40Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square46.s46_eq_seven
assert_standard_axioms SquarePackingArchive.Records.Square46.s47_eq_seven
assert_standard_axioms SquarePackingArchive.Records.Square46.s48_eq_seven
assert_standard_axioms SquarePackingArchive.Records.Square5.s5_eq_goebel
assert_standard_axioms SquarePackingArchive.Records.Square5.s5_le_goebel
assert_standard_axioms SquarePackingArchive.Records.Square50SchadtEllsworth.s50_le_7_57142857142857
assert_standard_axioms SquarePackingArchive.Records.Square53EllsworthReconstructed.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square65Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square66Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square68.s68_le_8_80339
assert_standard_axioms SquarePackingArchive.Records.Square69.s69_le_8_8272
assert_standard_axioms SquarePackingArchive.Records.Square82Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square85Tracker.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square86Friedman.upper_bound
assert_standard_axioms SquarePackingArchive.Records.Square89Tracker.upper_bound
