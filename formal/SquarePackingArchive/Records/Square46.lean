import SquarePackingArchive.StaggeredLattice
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square46

noncomputable def lattice : StaggeredLattice 6 4 3 where
  evenHeight row := 451 / 500 + 2 * (row : ℝ) * (433 / 500)
  oddHeight row := 451 / 500 + (2 * (row : ℝ) + 1) * (433 / 500)

lemma strict_unavoidable (square : PlacedSquare) (strict : square.StrictFits ((6 : ℝ) + 1)) :
    lattice.HasPoint square := by
  by_cases bottom : square.center.y ≤ 451 / 500
  · apply lattice.bottom_even strict.fits (by norm_num) 0
    · simpa [lattice] using rationalStripHeight_le_sqrt_two_sub_half
    · simpa [lattice] using bottom
  by_cases top : 7 - 451 / 500 ≤ square.center.y
  · apply lattice.top_even strict.fits (by norm_num) 3
    · norm_num [lattice]
      exact rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [lattice]
      linarith
  by_cases band0 : square.center.y ≤ 884 / 500
  · apply lattice.band_has_latticePoint strict 0 0 ((square.center.y - (451 / 500)) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith
  by_cases band1 : square.center.y ≤ 1317 / 500
  · apply lattice.band_has_latticePoint strict 1 0 (((1317 / 500) - square.center.y) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith
  by_cases band2 : square.center.y ≤ 7 / 2
  · apply lattice.band_has_latticePoint strict 1 1 ((square.center.y - (1317 / 500)) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith
  by_cases band3 : square.center.y ≤ 2183 / 500
  · apply lattice.band_has_latticePoint strict 2 1 (((2183 / 500) - square.center.y) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith
  by_cases band4 : square.center.y ≤ 2616 / 500
  · apply lattice.band_has_latticePoint strict 2 2 ((square.center.y - (2183 / 500)) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith
  · apply lattice.band_has_latticePoint strict 3 2 (((3049 / 500) - square.center.y) / (433 / 500))
    all_goals norm_num [lattice] <;> linarith

noncomputable def points : Fin 45 → Point := lattice.points

theorem s46_ge_seven : IsLowerBound 46 7 := by
  convert lattice.lowerBound strict_unavoidable using 1; norm_num

theorem s_eq_seven {squareCount : ℕ}
    (lower : 46 ≤ squareCount) (upper : squareCount ≤ 49) :
    IsMinimumSide squareCount 7 := by
  exact ⟨SquareNumbers.s49_eq_seven.1.mono upper,
    fun candidateSide packing => s46_ge_seven candidateSide (packing.mono lower)⟩

theorem s46_eq_seven : IsMinimumSide 46 7 :=
  s_eq_seven (by norm_num) (by norm_num)

theorem s47_eq_seven : IsMinimumSide 47 7 :=
  s_eq_seven (by norm_num) (by norm_num)

theorem s48_eq_seven : IsMinimumSide 48 7 :=
  s_eq_seven (by norm_num) (by norm_num)

end SquarePackingArchive.Records.Square46
