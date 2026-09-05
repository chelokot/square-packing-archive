import SquarePackingArchive.ShiftedStaggeredLattice
import SquarePackingArchive.BentzExtraPoint
import SquarePackingArchive.Records.Square23

namespace SquarePackingArchive

namespace ShiftedStaggeredLattice

lemma bottom_odd
    {width evenRows oddRows : ℕ} (lattice : ShiftedStaggeredLattice width evenRows oddRows)
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (row : Fin oddRows)
    (offset_nonnegative : 0 ≤ lattice.oddOffset row) (offset_at_most_one : lattice.oddOffset row ≤ 1)
    (height_upper : lattice.oddHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_below : square.center.y ≤ lattice.oddHeight row) : lattice.HasPoint square := by
  obtain ⟨column, contained⟩ := square.contains_bottomSpacedRow width fits
    (left := lattice.oddOffset row) offset_at_most_one (by linarith) height_upper center_below
  exact ⟨.inr (row, column), by simpa [point, add_comm] using contained⟩

lemma top_even
    {width evenRows oddRows : ℕ} (lattice : ShiftedStaggeredLattice width evenRows oddRows)
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (width_positive : 0 < width) (row : Fin evenRows)
    (height_lower : (width : ℝ) + 1 - lattice.evenHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_above : lattice.evenHeight row ≤ square.center.y) : lattice.HasPoint square := by
  obtain ⟨column, contained⟩ := square.contains_topSpacedRow (width - 1) fits
    (left := 1) (by norm_num)
    (by rw [Nat.cast_sub width_positive]; norm_num) height_lower center_above
  exact ⟨.inl (row, Fin.cast (Nat.sub_add_cancel width_positive) column),
    by simpa [point, add_comm] using contained⟩

end ShiftedStaggeredLattice

namespace BentzFiveRows

noncomputable def height (row : Fin 5) : ℝ := 9 / 10 + (row : ℝ) * (4 / 5)

noncomputable def redLattice (offsets : Fin 2 → ℝ) : ShiftedStaggeredLattice 4 3 2 where
  toStaggeredLattice := Records.Square23.lattice
  oddOffset := offsets

noncomputable def blueLattice (offsets : Fin 3 → ℝ) : ShiftedStaggeredLattice 4 2 3 where
  evenHeight row := 17 / 10 + 2 * (row : ℝ) * (4 / 5)
  oddHeight row := 9 / 10 + 2 * (row : ℝ) * (4 / 5)
  oddOffset := offsets

lemma shifted_band_distances {offset : ℝ}
    (offset_lower : 2 / 5 ≤ offset) (offset_upper : offset ≤ 1 / 2) :
    offset ^ 2 + (4 / 5) ^ 2 ≤ 1 ∧ (1 - offset) ^ 2 + (4 / 5) ^ 2 ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg offset, sq_nonneg (1 / 2 - offset)]

theorem red_strict_unavoidable (offsets : Fin 2 → ℝ)
    (offset_bounds : ∀ row, 2 / 5 ≤ offsets row ∧ offsets row ≤ 1 / 2)
    (square : PlacedSquare) (strict : square.StrictFits ((4 : ℝ) + 1)) :
    (redLattice offsets).HasPoint square := by
  have offset0 := offset_bounds 0
  have offset1 := offset_bounds 1
  have distance0 := shifted_band_distances offset0.1 offset0.2
  have distance1 := shifted_band_distances offset1.1 offset1.2
  by_cases bottom : square.center.y ≤ 9 / 10
  · apply (redLattice offsets).bottom_even strict.fits (by norm_num) 0
    · exact le_trans (by norm_num [redLattice, Records.Square23.lattice]) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [redLattice, Records.Square23.lattice]
      exact bottom
  by_cases top : 41 / 10 ≤ square.center.y
  · apply (redLattice offsets).top_even strict.fits (by norm_num) 2
    · exact le_trans (by norm_num [redLattice, Records.Square23.lattice]) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [redLattice, Records.Square23.lattice]
      exact top
  by_cases band0 : square.center.y ≤ 17 / 10
  · apply (redLattice offsets).band_from_below strict 0 0 (by dsimp [redLattice]; linarith)
      (by dsimp [redLattice]; linarith)
    all_goals norm_num [redLattice, Records.Square23.lattice] <;>
      nlinarith only [distance0.1, distance0.2, bottom, band0]
  by_cases band1 : square.center.y ≤ 5 / 2
  · apply (redLattice offsets).band_from_above strict 1 0 (by dsimp [redLattice]; linarith)
      (by dsimp [redLattice]; linarith)
    all_goals norm_num [redLattice, Records.Square23.lattice] <;>
      nlinarith only [distance0.1, distance0.2, band0, band1]
  by_cases band2 : square.center.y ≤ 33 / 10
  · apply (redLattice offsets).band_from_below strict 1 1 (by dsimp [redLattice]; linarith)
      (by dsimp [redLattice]; linarith)
    all_goals norm_num [redLattice, Records.Square23.lattice] <;>
      nlinarith only [distance1.1, distance1.2, band1, band2]
  · apply (redLattice offsets).band_from_above strict 2 1 (by dsimp [redLattice]; linarith)
      (by dsimp [redLattice]; linarith)
    all_goals norm_num [redLattice, Records.Square23.lattice] <;>
      nlinarith only [distance1.1, distance1.2, band2, top]

theorem blue_strict_unavoidable (offsets : Fin 3 → ℝ)
    (offset_bounds : ∀ row, 2 / 5 ≤ offsets row ∧ offsets row ≤ 1 / 2)
    (square : PlacedSquare) (strict : square.StrictFits ((4 : ℝ) + 1)) :
    (blueLattice offsets).HasPoint square := by
  have offset0 := offset_bounds 0
  have offset1 := offset_bounds 1
  have offset2 := offset_bounds 2
  have distance0 := shifted_band_distances offset0.1 offset0.2
  have distance1 := shifted_band_distances offset1.1 offset1.2
  have distance2 := shifted_band_distances offset2.1 offset2.2
  by_cases bottom : square.center.y ≤ 9 / 10
  · apply (blueLattice offsets).bottom_odd strict.fits 0 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    · exact le_trans (by norm_num [blueLattice]) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [blueLattice]
      exact bottom
  by_cases top : 41 / 10 ≤ square.center.y
  · apply (blueLattice offsets).top_odd strict.fits 2 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    · exact le_trans (by norm_num [blueLattice]) rationalStripHeight_le_sqrt_two_sub_half
    · norm_num [blueLattice]
      exact top
  by_cases band0 : square.center.y ≤ 17 / 10
  · apply (blueLattice offsets).band_from_above strict 0 0 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    all_goals norm_num [blueLattice] <;>
      nlinarith only [distance0.1, distance0.2, bottom, band0]
  by_cases band1 : square.center.y ≤ 5 / 2
  · apply (blueLattice offsets).band_from_below strict 0 1 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    all_goals norm_num [blueLattice] <;>
      nlinarith only [distance1.1, distance1.2, band0, band1]
  by_cases band2 : square.center.y ≤ 33 / 10
  · apply (blueLattice offsets).band_from_above strict 1 1 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    all_goals norm_num [blueLattice] <;>
      nlinarith only [distance1.1, distance1.2, band1, band2]
  · apply (blueLattice offsets).band_from_below strict 1 2 (by dsimp [blueLattice]; linarith)
      (by dsimp [blueLattice]; linarith)
    all_goals norm_num [blueLattice] <;>
      nlinarith only [distance2.1, distance2.2, band2, top]

noncomputable def redPoints (offsets : Fin 2 → ℝ) : Fin 22 → Point := (redLattice offsets).points

noncomputable def bluePoints (offsets : Fin 3 → ℝ) : Fin 23 → Point := (blueLattice offsets).points

theorem red_interior_unavoidable (offsets : Fin 2 → ℝ)
    (offset_bounds : ∀ row, 2 / 5 ≤ offsets row ∧ offsets row ≤ 1 / 2)
    {side : ℝ} (side_positive : 0 < side) (side_lt_five : side < 5) :
    InteriorUnavoidable (fun index => (redPoints offsets index).scale (side / 5)) side := by
  apply strictUnavoidable_interior_scaled side_positive side_lt_five
  intro square strict
  obtain ⟨index, contained⟩ := red_strict_unavoidable offsets offset_bounds square
    (by norm_num only [Nat.cast_ofNat]; exact strict)
  refine ⟨Fin.cast (by simp [StaggeredLattice.Index])
    ((Fintype.equivFin (StaggeredLattice.Index 4 3 2)) index), ?_⟩
  simpa [redPoints, ShiftedStaggeredLattice.points] using contained

theorem blue_interior_unavoidable (offsets : Fin 3 → ℝ)
    (offset_bounds : ∀ row, 2 / 5 ≤ offsets row ∧ offsets row ≤ 1 / 2)
    {side : ℝ} (side_positive : 0 < side) (side_lt_five : side < 5) :
    InteriorUnavoidable (fun index => (bluePoints offsets index).scale (side / 5)) side := by
  apply strictUnavoidable_interior_scaled side_positive side_lt_five
  intro square strict
  obtain ⟨index, contained⟩ := blue_strict_unavoidable offsets offset_bounds square
    (by norm_num only [Nat.cast_ofNat]; exact strict)
  refine ⟨Fin.cast (by simp [StaggeredLattice.Index])
    ((Fintype.equivFin (StaggeredLattice.Index 4 2 3)) index), ?_⟩
  simpa [bluePoints, ShiftedStaggeredLattice.points] using contained

end BentzFiveRows

end SquarePackingArchive
