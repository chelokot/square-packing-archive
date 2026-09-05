import SquarePackingArchive.StaggeredLattice
import SquarePackingArchive.MovingPacking

namespace SquarePackingArchive

namespace StaggeredLattice

lemma band_from_below
    {width evenRows oddRows : ℕ} (lattice : StaggeredLattice width evenRows oddRows)
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows)
    (gap_positive : 0 < lattice.oddHeight oddRow - lattice.evenHeight evenRow)
    (gap_upper : lattice.oddHeight oddRow - lattice.evenHeight evenRow ≤ 433 / 500)
    (center_lower : lattice.evenHeight evenRow ≤ square.center.y)
    (center_upper : square.center.y ≤ lattice.oddHeight oddRow) :
    lattice.HasPoint square := by
  apply lattice.band_has_latticePoint strict evenRow oddRow
    ((square.center.y - lattice.evenHeight evenRow) /
      (lattice.oddHeight oddRow - lattice.evenHeight evenRow))
  · exact div_nonneg (sub_nonneg.mpr center_lower) gap_positive.le
  · exact (div_le_one gap_positive).2 (by linarith)
  · field_simp
    ring
  · nlinarith [sq_nonneg (lattice.oddHeight oddRow - lattice.evenHeight evenRow - 433 / 500)]

lemma band_from_above
    {width evenRows oddRows : ℕ} (lattice : StaggeredLattice width evenRows oddRows)
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows)
    (gap_positive : 0 < lattice.evenHeight evenRow - lattice.oddHeight oddRow)
    (gap_upper : lattice.evenHeight evenRow - lattice.oddHeight oddRow ≤ 433 / 500)
    (center_lower : lattice.oddHeight oddRow ≤ square.center.y)
    (center_upper : square.center.y ≤ lattice.evenHeight evenRow) :
    lattice.HasPoint square := by
  apply lattice.band_has_latticePoint strict evenRow oddRow
    ((lattice.evenHeight evenRow - square.center.y) /
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow))
  · exact div_nonneg (sub_nonneg.mpr center_upper) gap_positive.le
  · exact (div_le_one gap_positive).2 (by linarith)
  · field_simp
    ring
  · nlinarith [sq_nonneg (lattice.evenHeight evenRow - lattice.oddHeight oddRow - 433 / 500)]

end StaggeredLattice

namespace BentzSixRows

def Admissible (heights : Fin 6 → ℝ) : Prop :=
  heights 0 ≤ 451 / 500 ∧ 6 - heights 5 ≤ 451 / 500 ∧
    ∀ row : Fin 5,
      0 < heights row.succ - heights row.castSucc ∧
        heights row.succ - heights row.castSucc ≤ 433 / 500

noncomputable def lattice (heights : Fin 6 → ℝ) : StaggeredLattice 5 3 3 where
  evenHeight row := heights ⟨2 * row.val, by omega⟩
  oddHeight row := heights ⟨2 * row.val + 1, by omega⟩

theorem strict_unavoidable
    {heights : Fin 6 → ℝ} (admissible : Admissible heights)
    (square : PlacedSquare) (strict : square.StrictFits ((5 : ℝ) + 1)) :
    (lattice heights).HasPoint square := by
  have first_gap := admissible.2.2 0
  have second_gap := admissible.2.2 1
  have third_gap := admissible.2.2 2
  have fourth_gap := admissible.2.2 3
  have fifth_gap := admissible.2.2 4
  by_cases bottom : square.center.y ≤ heights 0
  · apply (lattice heights).bottom_even strict.fits (by norm_num) 0
    · exact admissible.1.trans rationalStripHeight_le_sqrt_two_sub_half
    · exact bottom
  by_cases top : heights 5 ≤ square.center.y
  · apply (lattice heights).top_odd strict.fits 2
    · change (5 : ℝ) + 1 - heights ⟨5, by decide⟩ ≤ _
      have last_eq : (⟨5, by decide⟩ : Fin 6) = 5 := by decide
      rw [last_eq]
      linarith [admissible.2.1.trans rationalStripHeight_le_sqrt_two_sub_half]
    · exact top
  by_cases first_band : square.center.y ≤ heights 1
  · exact (lattice heights).band_from_below strict 0 0 first_gap.1 first_gap.2
      (le_of_not_ge bottom) first_band
  by_cases second_band : square.center.y ≤ heights 2
  · exact (lattice heights).band_from_above strict 1 0 second_gap.1 second_gap.2
      (le_of_not_ge first_band) second_band
  by_cases third_band : square.center.y ≤ heights 3
  · exact (lattice heights).band_from_below strict 1 1 third_gap.1 third_gap.2
      (le_of_not_ge second_band) third_band
  by_cases fourth_band : square.center.y ≤ heights 4
  · exact (lattice heights).band_from_above strict 2 1 fourth_gap.1 fourth_gap.2
      (le_of_not_ge third_band) fourth_band
  · exact (lattice heights).band_from_below strict 2 2 fifth_gap.1 fifth_gap.2
      (le_of_not_ge fourth_band) (le_of_not_ge top)

noncomputable def interpolate (start finish : Fin 6 → ℝ) (position : ℝ) : Fin 6 → ℝ :=
  fun row => (1 - position) * start row + position * finish row

@[simp] theorem interpolate_zero (start finish : Fin 6 → ℝ) :
    interpolate start finish 0 = start := by
  funext row
  simp [interpolate]

@[simp] theorem interpolate_one (start finish : Fin 6 → ℝ) :
    interpolate start finish 1 = finish := by
  funext row
  simp [interpolate]

theorem interpolate_admissible
    {start finish : Fin 6 → ℝ} (start_admissible : Admissible start)
    (finish_admissible : Admissible finish)
    {position : ℝ} (position_lower : 0 ≤ position) (position_upper : position ≤ 1) :
    Admissible (interpolate start finish position) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [interpolate]
    nlinarith [start_admissible.1, finish_admissible.1]
  · dsimp [interpolate]
    nlinarith [start_admissible.2.1, finish_admissible.2.1]
  · intro row
    obtain ⟨start_positive, start_upper⟩ := start_admissible.2.2 row
    obtain ⟨finish_positive, finish_upper⟩ := finish_admissible.2.2 row
    dsimp [interpolate]
    constructor
    · by_cases position_zero : position = 0
      · simpa [position_zero] using start_positive
      · have first_nonnegative := mul_nonneg (by linarith : 0 ≤ 1 - position) start_positive.le
        have second_positive := mul_pos (lt_of_le_of_ne position_lower (Ne.symm position_zero)) finish_positive
        nlinarith
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - position) (sub_nonneg.mpr start_upper),
        mul_nonneg position_lower (sub_nonneg.mpr finish_upper)]

noncomputable def initialHeights : Fin 6 → ℝ :=
  fun row => 451 / 500 + (row : ℝ) * (1049 / 1250)

noncomputable def compressedHeights (selected row : Fin 6) : ℝ := (![
  ![1353, 2553, 7653 / 2, 5100, 12747 / 2, 7647],
  ![1353, 2553, 3753, 5051, 6349, 7647],
  ![1353, 2651, 3851, 5051, 6349, 7647],
  ![1353, 2651, 3949, 5149, 6349, 7647],
  ![1353, 2651, 3949, 5247, 6447, 7647],
  ![1353, 5253 / 2, 3900, 10347 / 2, 6447, 7647]
  ] : Fin 6 → Fin 6 → ℝ) selected row / 1500

@[simp] theorem compressedHeights_last (selected : Fin 6) :
    compressedHeights selected 5 = 2549 / 500 := by
  fin_cases selected <;> change (7647 : ℝ) / 1500 = 2549 / 500 <;> norm_num

theorem initialHeights_admissible : Admissible initialHeights := by
  constructor
  · norm_num [initialHeights]
  constructor
  · norm_num [initialHeights]
  · intro row
    fin_cases row <;> norm_num [initialHeights]

theorem compressedHeights_admissible (selected : Fin 6) :
    Admissible (compressedHeights selected) := by
  fin_cases selected <;> unfold Admissible <;>
    norm_num [compressedHeights, Fin.forall_fin_succ]
  all_goals change (6 : ℝ) ≤ 451 / 500 + 7647 / 1500
  all_goals norm_num

theorem compressedHeights_adjacent_gap
    (selected : Fin 6) (gap : Fin 5)
    (adjacent : gap.castSucc = selected ∨ gap.succ = selected) :
    compressedHeights selected gap.succ - compressedHeights selected gap.castSucc ≤ 4 / 5 := by
  fin_cases selected <;> fin_cases gap <;>
    norm_num [compressedHeights, Matrix.cons_val_two, Fin.ext_iff] at *

theorem compression_strict_unavoidable
    (selected : Fin 6) {position : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (square : PlacedSquare) (strict : square.StrictFits ((5 : ℝ) + 1)) :
    (lattice (interpolate initialHeights (compressedHeights selected) position)).HasPoint square :=
  strict_unavoidable
    (interpolate_admissible initialHeights_admissible (compressedHeights_admissible selected)
      position_lower position_upper) square strict

noncomputable def compressionPoints (selected : Fin 6) (position : ℝ) : Fin 33 → Point :=
  (lattice (interpolate initialHeights (compressedHeights selected) position)).points

theorem compressionPoints_continuous (selected : Fin 6) (index : Fin 33) (scale : ℝ) :
    Continuous fun position : ℝ => ((compressionPoints selected position index).scale scale).toPlane := by
  unfold compressionPoints StaggeredLattice.points
  generalize (Fintype.equivFin (StaggeredLattice.Index 5 3 3)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index) = latticeIndex
  rcases latticeIndex with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;>
      dsimp [StaggeredLattice.point, lattice, interpolate, Point.scale, Point.toPlane] <;>
      fun_prop

theorem compressionPoints_interior_unavoidable
    (selected : Fin 6) {position side : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (side_positive : 0 < side) (side_lt_six : side < 6) :
    InteriorUnavoidable (fun index => (compressionPoints selected position index).scale (side / 6)) side := by
  apply strictUnavoidable_interior_scaled side_positive side_lt_six
  intro square strict
  have point_mem := compression_strict_unavoidable selected position_lower position_upper square
    (by norm_num only [Nat.cast_ofNat]; exact strict)
  obtain ⟨index, contained⟩ := point_mem
  refine ⟨Fin.cast (by simp [StaggeredLattice.Index])
    ((Fintype.equivFin (StaggeredLattice.Index 5 3 3)) index), ?_⟩
  simpa [compressionPoints, StaggeredLattice.points] using contained

theorem compression_preserves_assignment
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (selected : Fin 6) (index owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      ((compressionPoints selected 0 index).scale (side / 6))) :
    ∀ position : Set.Icc (0 : ℝ) 1, (packing.squares owner).InteriorContains
      ((compressionPoints selected position index).scale (side / 6)) := by
  apply packing.moving_interiorUnavoidable_preserves_assignment
    (fun index (position : Set.Icc (0 : ℝ) 1) =>
      (compressionPoints selected position index).scale (side / 6))
    ⟨0, by norm_num⟩
    (fun index => (compressionPoints_continuous selected index (side / 6)).comp continuous_subtype_val)
    (fun position => compressionPoints_interior_unavoidable selected position.property.1
      position.property.2 side_positive side_lt_six) index owner initially_inside

theorem compressed_endpoint_same_owner
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (selected : Fin 6) (index owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      ((lattice initialHeights).points index |>.scale (side / 6))) :
    (packing.squares owner).InteriorContains
      ((lattice (compressedHeights selected)).points index |>.scale (side / 6)) := by
  have preserved := compression_preserves_assignment packing side_positive side_lt_six selected index owner
    (by simpa only [compressionPoints, interpolate_zero] using initially_inside)
    ⟨1, by norm_num⟩
  simpa only [compressionPoints, interpolate_one] using preserved

end BentzSixRows

end SquarePackingArchive
