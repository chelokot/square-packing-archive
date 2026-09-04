import SquarePackingArchive.StaggeredLattice
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square34

noncomputable def lattice : StaggeredLattice 5 3 3 where
  evenHeight row := 451 / 500 + 2 * (row : ℝ) * (1049 / 1250)
  oddHeight row := 451 / 500 + (2 * (row : ℝ) + 1) * (1049 / 1250)

lemma strict_unavoidable (square : PlacedSquare) (strict : square.StrictFits ((5 : ℝ) + 1)) :
    lattice.HasPoint square := by
  by_cases bottom : square.center.y ≤ 451 / 500
  · apply lattice.bottom_even strict.fits (by norm_num) 0
    · norm_num [lattice]
      exact le_trans (by norm_num) rationalStripHeight_le_sqrt_two_sub_half
    · simpa [lattice] using bottom
  by_cases top : 6 - (451 / 500) ≤ square.center.y
  · apply lattice.top_odd strict.fits 2
    · norm_num [lattice]
      exact le_trans (by norm_num) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [lattice]
      linarith
  by_cases band0 : square.center.y ≤ 4353 / 2500
  · apply lattice.band_has_latticePoint strict 0 0 ((square.center.y - (451 / 500)) / (1049 / 1250))
    all_goals norm_num [lattice] <;> linarith
  by_cases band1 : square.center.y ≤ 6451 / 2500
  · apply lattice.band_has_latticePoint strict 1 0 (((6451 / 2500) - square.center.y) / (1049 / 1250))
    all_goals norm_num [lattice] <;> linarith
  by_cases band2 : square.center.y ≤ 8549 / 2500
  · apply lattice.band_has_latticePoint strict 1 1 ((square.center.y - (6451 / 2500)) / (1049 / 1250))
    all_goals norm_num [lattice] <;> linarith
  by_cases band3 : square.center.y ≤ 10647 / 2500
  · apply lattice.band_has_latticePoint strict 2 1 (((10647 / 2500) - square.center.y) / (1049 / 1250))
    all_goals norm_num [lattice] <;> linarith
  · apply lattice.band_has_latticePoint strict 2 2 ((square.center.y - (10647 / 2500)) / (1049 / 1250))
    all_goals norm_num [lattice] <;> linarith

noncomputable def points : Fin 33 → Point := lattice.points

theorem s34_lower_bound : IsLowerBound 34 6 := by
  convert lattice.lowerBound strict_unavoidable using 1; norm_num

theorem s34_eq_six : IsMinimumSide 34 6 :=
  ⟨SquareNumbers.s36_eq_six.1.mono (by norm_num), s34_lower_bound⟩

theorem s35_eq_six : IsMinimumSide 35 6 :=
  ⟨SquareNumbers.s36_eq_six.1.mono (by norm_num),
    fun candidateSide packing => s34_lower_bound candidateSide (packing.mono (by norm_num))⟩

end SquarePackingArchive.Records.Square34
