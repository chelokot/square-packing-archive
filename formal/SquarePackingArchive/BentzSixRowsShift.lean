import SquarePackingArchive.ShiftedStaggeredLattice
import SquarePackingArchive.BentzSixRowsPoints

namespace SquarePackingArchive.BentzSixRows

def oddRowIndex (row : Fin 3) : Fin 6 := ⟨2 * row.val + 1, by omega⟩

noncomputable def shiftOffset (selected row : Fin 3) (position : ℝ) : ℝ :=
  if row = selected then 1 / 2 - position / 10 else 1 / 2

noncomputable def shiftedLattice (selected : Fin 3) (position : ℝ) : ShiftedStaggeredLattice 5 3 3 where
  toStaggeredLattice := lattice (compressedHeights (oddRowIndex selected))
  oddOffset row := shiftOffset selected row position

theorem shiftOffset_bounds (selected row : Fin 3) {position : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1) :
    0 < shiftOffset selected row position ∧ shiftOffset selected row position < 1 := by
  dsimp [shiftOffset]
  split_ifs <;> constructor <;> linarith

theorem shifted_gap_distances (selected : Fin 3) (gap : Fin 5) {position : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1) :
    (shiftOffset selected ⟨gap.val / 2, by omega⟩ position) ^ 2 +
      (compressedHeights (oddRowIndex selected) gap.succ -
        compressedHeights (oddRowIndex selected) gap.castSucc) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected ⟨gap.val / 2, by omega⟩ position) ^ 2 +
      (compressedHeights (oddRowIndex selected) gap.succ -
        compressedHeights (oddRowIndex selected) gap.castSucc) ^ 2 ≤ 1 := by
  fin_cases selected <;> fin_cases gap <;>
    norm_num [shiftOffset, oddRowIndex, compressedHeights, Matrix.cons_val_two, Fin.ext_iff] <;>
    constructor <;> nlinarith [sq_nonneg position, sq_nonneg (1 - position)]

theorem shift_strict_unavoidable
    (selected : Fin 3) {position : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (square : PlacedSquare) (strict : square.StrictFits ((5 : ℝ) + 1)) :
    (shiftedLattice selected position).HasPoint square := by
  let heights := compressedHeights (oddRowIndex selected)
  let configuration := shiftedLattice selected position
  have admissible := compressedHeights_admissible (oddRowIndex selected)
  have offset_bounds := fun row => shiftOffset_bounds selected row position_lower position_upper
  have gap0 := admissible.2.2 0
  have gap1 := admissible.2.2 1
  have gap2 := admissible.2.2 2
  have gap3 := admissible.2.2 3
  have gap4 := admissible.2.2 4
  have distance0 := shifted_gap_distances selected 0 position_lower position_upper
  have distance1 := shifted_gap_distances selected 1 position_lower position_upper
  have distance2 := shifted_gap_distances selected 2 position_lower position_upper
  have distance3 := shifted_gap_distances selected 3 position_lower position_upper
  have distance4 := shifted_gap_distances selected 4 position_lower position_upper
  change (shiftOffset selected 0 position) ^ 2 + (heights 1 - heights 0) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected 0 position) ^ 2 + (heights 1 - heights 0) ^ 2 ≤ 1 at distance0
  change (shiftOffset selected 0 position) ^ 2 + (heights 2 - heights 1) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected 0 position) ^ 2 + (heights 2 - heights 1) ^ 2 ≤ 1 at distance1
  change (shiftOffset selected 1 position) ^ 2 + (heights 3 - heights 2) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected 1 position) ^ 2 + (heights 3 - heights 2) ^ 2 ≤ 1 at distance2
  change (shiftOffset selected 1 position) ^ 2 + (heights 4 - heights 3) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected 1 position) ^ 2 + (heights 4 - heights 3) ^ 2 ≤ 1 at distance3
  change (shiftOffset selected 2 position) ^ 2 + (heights 5 - heights 4) ^ 2 ≤ 1 ∧
    (1 - shiftOffset selected 2 position) ^ 2 + (heights 5 - heights 4) ^ 2 ≤ 1 at distance4
  by_cases bottom : square.center.y ≤ heights 0
  · apply configuration.bottom_even strict.fits (by norm_num) 0
    · exact admissible.1.trans rationalStripHeight_le_sqrt_two_sub_half
    · exact bottom
  by_cases top : heights 5 ≤ square.center.y
  · apply configuration.top_odd strict.fits 2 (offset_bounds 2).1.le (offset_bounds 2).2.le
    · change (5 : ℝ) + 1 - heights ⟨5, by decide⟩ ≤ _
      have last_eq : (⟨5, by decide⟩ : Fin 6) = 5 := by decide
      rw [last_eq]
      linarith [admissible.2.1.trans rationalStripHeight_le_sqrt_two_sub_half]
    · exact top
  by_cases band0 : square.center.y ≤ heights 1
  · apply configuration.band_from_below strict 0 0 (offset_bounds 0).1 (offset_bounds 0).2 gap0.1
    · change (shiftOffset selected 0 position) ^ 2 + (heights 0 - heights 1) ^ 2 ≤ 1
      nlinarith only [distance0.1]
    · change (1 - shiftOffset selected 0 position) ^ 2 + (heights 0 - heights 1) ^ 2 ≤ 1
      nlinarith only [distance0.2]
    · exact le_of_not_ge bottom
    · exact band0
  by_cases band1 : square.center.y ≤ heights 2
  · apply configuration.band_from_above strict 1 0 (offset_bounds 0).1 (offset_bounds 0).2 gap1.1
    · exact distance1.1
    · exact distance1.2
    · exact le_of_not_ge band0
    · exact band1
  by_cases band2 : square.center.y ≤ heights 3
  · apply configuration.band_from_below strict 1 1 (offset_bounds 1).1 (offset_bounds 1).2 gap2.1
    · change (shiftOffset selected 1 position) ^ 2 + (heights 2 - heights 3) ^ 2 ≤ 1
      nlinarith only [distance2.1]
    · change (1 - shiftOffset selected 1 position) ^ 2 + (heights 2 - heights 3) ^ 2 ≤ 1
      nlinarith only [distance2.2]
    · exact le_of_not_ge band1
    · exact band2
  by_cases band3 : square.center.y ≤ heights 4
  · apply configuration.band_from_above strict 2 1 (offset_bounds 1).1 (offset_bounds 1).2 gap3.1
    · exact distance3.1
    · exact distance3.2
    · exact le_of_not_ge band2
    · exact band3
  · apply configuration.band_from_below strict 2 2 (offset_bounds 2).1 (offset_bounds 2).2 gap4.1
    · change (shiftOffset selected 2 position) ^ 2 + (heights 4 - heights 5) ^ 2 ≤ 1
      nlinarith only [distance4.1]
    · change (1 - shiftOffset selected 2 position) ^ 2 + (heights 4 - heights 5) ^ 2 ≤ 1
      nlinarith only [distance4.2]
    · exact le_of_not_ge band3
    · exact le_of_not_ge top

noncomputable def shiftedPoints (selected : Fin 3) (position : ℝ) : Fin 33 → Point :=
  (shiftedLattice selected position).points

@[simp] theorem shiftedPoints_zero (selected : Fin 3) :
    shiftedPoints selected 0 = (lattice (compressedHeights (oddRowIndex selected))).points := by
  funext index
  unfold shiftedPoints ShiftedStaggeredLattice.points StaggeredLattice.points
  generalize (Fintype.equivFin (StaggeredLattice.Index 5 3 3)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index) = latticeIndex
  rcases latticeIndex with ⟨row, column⟩ | ⟨row, column⟩
  all_goals simp [ShiftedStaggeredLattice.point, StaggeredLattice.point, shiftedLattice, shiftOffset]

theorem shiftedPoints_continuous (selected : Fin 3) (index : Fin 33) (scale : ℝ) :
    Continuous fun position : ℝ => ((shiftedPoints selected position index).scale scale).toPlane := by
  unfold shiftedPoints ShiftedStaggeredLattice.points
  generalize (Fintype.equivFin (StaggeredLattice.Index 5 3 3)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index) = latticeIndex
  rcases latticeIndex with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;>
      dsimp [ShiftedStaggeredLattice.point, shiftedLattice, shiftOffset, Point.scale, Point.toPlane]
  all_goals first | fun_prop | (split_ifs <;> fun_prop)

theorem shiftedPoints_interior_unavoidable
    (selected : Fin 3) {position side : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (side_positive : 0 < side) (side_lt_six : side < 6) :
    InteriorUnavoidable (fun index => (shiftedPoints selected position index).scale (side / 6)) side := by
  apply strictUnavoidable_interior_scaled side_positive side_lt_six
  intro square strict
  obtain ⟨index, contained⟩ := shift_strict_unavoidable selected position_lower position_upper square
    (by norm_num only [Nat.cast_ofNat]; exact strict)
  exact ⟨pointIndex index, by simpa [shiftedPoints, pointIndex, ShiftedStaggeredLattice.points] using contained⟩

theorem shift_endpoint_same_owner
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (selected : Fin 3) (index owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      (((lattice (compressedHeights (oddRowIndex selected))).points index).scale (side / 6))) :
    (packing.squares owner).InteriorContains ((shiftedPoints selected 1 index).scale (side / 6)) := by
  have preserved := packing.moving_interiorUnavoidable_preserves_assignment
    (fun index (position : Set.Icc (0 : ℝ) 1) => (shiftedPoints selected position index).scale (side / 6))
    ⟨0, by norm_num⟩
    (fun index => (shiftedPoints_continuous selected index (side / 6)).comp continuous_subtype_val)
    (fun position => shiftedPoints_interior_unavoidable selected position.property.1 position.property.2
      side_positive side_lt_six) index owner
    (by simpa only [shiftedPoints_zero] using initially_inside) ⟨1, by norm_num⟩
  exact preserved

theorem odd_row_reaches_left
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (selected : Fin 3) (owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      ((rowPoint initialHeights (oddRowIndex selected)).scale (side / 6))) :
    (packing.squares owner).InteriorContains
      ((Point.mk (2 / 5) (compressedHeights (oddRowIndex selected) (oddRowIndex selected))).scale (side / 6)) := by
  have compressed := compressed_row_same_owner packing side_positive side_lt_six (oddRowIndex selected) owner
    initially_inside
  have shifted := shift_endpoint_same_owner packing side_positive side_lt_six selected
    (rowPointIndex (oddRowIndex selected)) owner
    (by simpa only [points_at_rowPointIndex] using compressed)
  convert shifted using 1
  congr 1
  fin_cases selected <;>
    simp [rowPointIndex, oddRowIndex, shiftedPoints, ShiftedStaggeredLattice.points,
      pointIndex, ShiftedStaggeredLattice.point, shiftedLattice, shiftOffset, lattice] <;>
    norm_num

end SquarePackingArchive.BentzSixRows
