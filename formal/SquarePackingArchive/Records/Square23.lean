import SquarePackingArchive.StaggeredLattice
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square23

noncomputable def lattice : StaggeredLattice 4 3 2 where
  evenHeight row := 9 / 10 + 2 * (row : ℝ) * (4 / 5)
  oddHeight row := 9 / 10 + (2 * (row : ℝ) + 1) * (4 / 5)

lemma strict_unavoidable (square : PlacedSquare) (strict : square.StrictFits ((4 : ℝ) + 1)) :
    lattice.HasPoint square := by
  by_cases bottom : square.center.y ≤ 9 / 10
  · apply lattice.bottom_even strict.fits (by norm_num) 0
    · norm_num [lattice]
      exact le_trans (by norm_num) rationalStripHeight_le_sqrt_two_sub_half
    · simpa [lattice] using bottom
  by_cases top : 5 - (9 / 10) ≤ square.center.y
  · apply lattice.top_even strict.fits (by norm_num) 2
    · norm_num [lattice]
      exact le_trans (by norm_num) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [lattice]
      linarith
  by_cases band0 : square.center.y ≤ 17 / 10
  · apply lattice.band_has_latticePoint strict 0 0 ((square.center.y - (9 / 10)) / (4 / 5))
    all_goals norm_num [lattice] <;> linarith
  by_cases band1 : square.center.y ≤ 5 / 2
  · apply lattice.band_has_latticePoint strict 1 0 (((5 / 2) - square.center.y) / (4 / 5))
    all_goals norm_num [lattice] <;> linarith
  by_cases band2 : square.center.y ≤ 33 / 10
  · apply lattice.band_has_latticePoint strict 1 1 ((square.center.y - (5 / 2)) / (4 / 5))
    all_goals norm_num [lattice] <;> linarith
  · apply lattice.band_has_latticePoint strict 2 1 (((5 - (9 / 10)) - square.center.y) / (4 / 5))
    all_goals norm_num [lattice] <;> linarith

noncomputable def points : Fin 22 → Point := lattice.points

theorem s23_lower_bound : IsLowerBound 23 5 := by
  convert lattice.lowerBound strict_unavoidable using 1; norm_num

theorem s23_eq_five : IsMinimumSide 23 5 :=
  ⟨SquareNumbers.s25_eq_five.1.mono (by norm_num), s23_lower_bound⟩

end SquarePackingArchive.Records.Square23
