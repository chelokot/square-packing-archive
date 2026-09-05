import SquarePackingArchive.BentzFiveRowsExceptions
import SquarePackingArchive.BentzActiveMotion

namespace SquarePackingArchive.BentzFiveRows

def oddRedRowIndex (row : Fin 2) : Fin 5 := ⟨2 * row.val + 1, by omega⟩

def evenBlueRowIndex (row : Fin 3) : Fin 5 := ⟨2 * row.val, by omega⟩

noncomputable def rowOffsets {rows : ℕ} (selected row : Fin rows) (position : ℝ) : ℝ :=
  if row = selected then 1 / 2 - position / 10 else 1 / 2

theorem rowOffsets_bounds {rows : ℕ} (selected row : Fin rows) {position : ℝ}
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1) :
    2 / 5 ≤ rowOffsets selected row position ∧ rowOffsets selected row position ≤ 1 / 2 := by
  dsimp [rowOffsets]
  split_ifs <;> constructor <;> linarith

theorem rowOffsets_zero {rows : ℕ} (selected : Fin rows) :
    (fun row => rowOffsets selected row 0) = fun _ => 1 / 2 := by
  funext row
  simp [rowOffsets]

noncomputable def movingRedPoints (selected : Fin 2) (position : ℝ) : Fin 22 → Point :=
  redPoints (fun row => rowOffsets selected row position)

noncomputable def movingBluePoints (selected : Fin 3) (position : ℝ) : Fin 23 → Point :=
  bluePoints (fun row => rowOffsets selected row position)

theorem movingRedPoints_continuous (selected : Fin 2) (index : Fin 22) (scale : ℝ) :
    Continuous fun position : ℝ => ((movingRedPoints selected position index).scale scale).toPlane := by
  unfold movingRedPoints redPoints ShiftedStaggeredLattice.points
  generalize (Fintype.equivFin (StaggeredLattice.Index 4 3 2)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index) = latticeIndex
  rcases latticeIndex with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;>
      dsimp [ShiftedStaggeredLattice.point, redLattice, rowOffsets, Point.scale, Point.toPlane]
  all_goals first | fun_prop | (split_ifs <;> fun_prop)

theorem movingBluePoints_continuous (selected : Fin 3) (index : Fin 23) (scale : ℝ) :
    Continuous fun position : ℝ => ((movingBluePoints selected position index).scale scale).toPlane := by
  unfold movingBluePoints bluePoints ShiftedStaggeredLattice.points
  generalize (Fintype.equivFin (StaggeredLattice.Index 4 2 3)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index) = latticeIndex
  rcases latticeIndex with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;>
      dsimp [ShiftedStaggeredLattice.point, blueLattice, rowOffsets, Point.scale, Point.toPlane]
  all_goals first | fun_prop | (split_ifs <;> fun_prop)

theorem red_row_reaches_left
    {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5)
    (selected : Fin 2) (owner : Fin 22)
    (initially_inside : (packing.squares owner).InteriorContains
      ((redRowPoint (oddRedRowIndex selected)).scale (side / 5))) :
    (packing.squares owner).InteriorContains
      ((Point.mk (2 / 5) (height (oddRedRowIndex selected))).scale (side / 5)) := by
  have initial_point : (packing.squares owner).InteriorContains
      ((movingRedPoints selected 0 (redRowIndex (oddRedRowIndex selected))).scale (side / 5)) := by
    simp only [movingRedPoints, rowOffsets_zero]
    change (packing.squares owner).InteriorContains
      ((redBasePoints (redRowIndex (oddRedRowIndex selected))).scale (side / 5))
    simpa only [redBasePoints_at_row] using initially_inside
  have preserved := packing.moving_interiorUnavoidable_preserves_assignment
    (fun index (position : Set.Icc (0 : ℝ) 1) => (movingRedPoints selected position index).scale (side / 5))
    ⟨0, by norm_num⟩
    (fun index => (movingRedPoints_continuous selected index (side / 5)).comp continuous_subtype_val)
    (fun position => red_interior_unavoidable _
      (fun row => rowOffsets_bounds selected row position.property.1 position.property.2)
      side_positive side_lt_five)
    (redRowIndex (oddRedRowIndex selected)) owner initial_point ⟨1, by norm_num⟩
  convert preserved using 1
  congr 1
  fin_cases selected <;>
    norm_num [movingRedPoints, redRowIndex, oddRedRowIndex, rowOffsets, height] <;>
    norm_num [ShiftedStaggeredLattice.point, redLattice, Records.Square23.lattice]

noncomputable def blueActiveRow (selected : Fin 3) (index : Fin 23) : Prop :=
  match (Fintype.equivFin (StaggeredLattice.Index 4 2 3)).symm
      (Fin.cast (by simp [StaggeredLattice.Index]) index) with
  | .inl _ => False
  | .inr (row, _) => row = selected

theorem bluePointIndex_surjective : Function.Surjective bluePointIndex := by
  intro index
  exact ⟨(Fintype.equivFin (StaggeredLattice.Index 4 2 3)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index), by simp [bluePointIndex]⟩

theorem blue_inactive_stationary (selected : Fin 3) (index : Fin 23)
    (inactive : ¬ blueActiveRow selected index) (position : ℝ) :
    movingBluePoints selected position index = movingBluePoints selected 0 index := by
  obtain ⟨source, source_eq⟩ := bluePointIndex_surjective index
  subst index
  rcases source with ⟨row, column⟩ | ⟨row, column⟩
  · simp [movingBluePoints, bluePoints_at_index, ShiftedStaggeredLattice.point, blueLattice]
  · have different : row ≠ selected := by simpa [blueActiveRow, bluePointIndex] using inactive
    simp [movingBluePoints, bluePoints_at_index, ShiftedStaggeredLattice.point, blueLattice,
      rowOffsets, different]

theorem blue_unique_row_reaches_left
    {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5)
    (selected : Fin 3) (unique : BlueRowUnique packing selected) (owner : Fin 22)
    (initially_inside : (packing.squares owner).InteriorContains
      ((Point.mk (1 / 2) (height (evenBlueRowIndex selected))).scale (side / 5))) :
    (packing.squares owner).InteriorContains
      ((Point.mk (2 / 5) (height (evenBlueRowIndex selected))).scale (side / 5)) := by
  have initial_point : (packing.squares owner).InteriorContains
      ((movingBluePoints selected 0 (bluePointIndex (.inr (selected, 0)))).scale (side / 5)) := by
    convert initially_inside using 1
    congr 1
    fin_cases selected <;>
      norm_num [movingBluePoints, rowOffsets, height, evenBlueRowIndex] <;>
      norm_num [ShiftedStaggeredLattice.point, blueLattice]
  have preserved := packing.moving_interiorUnavoidable_preserves_unique_active
    (fun index (position : Set.Icc (0 : ℝ) 1) => (movingBluePoints selected position index).scale (side / 5))
    ⟨0, by norm_num⟩
    (fun index => (movingBluePoints_continuous selected index (side / 5)).comp continuous_subtype_val)
    (fun position => blue_interior_unavoidable _
      (fun row => rowOffsets_bounds selected row position.property.1 position.property.2)
      side_positive side_lt_five)
    (blueActiveRow selected)
    (fun index inactive position => congrArg (Point.scale (side / 5))
      (blue_inactive_stationary selected index inactive position))
    (by
      intro index active
      obtain ⟨source, source_eq⟩ := bluePointIndex_surjective index
      subst index
      rcases source with ⟨row, column⟩ | ⟨row, column⟩
      · simp [blueActiveRow, bluePointIndex] at active
      · have row_eq : row = selected := by simpa [blueActiveRow, bluePointIndex] using active
        subst row
        simpa only [movingBluePoints, rowOffsets_zero, blueBasePoints, Packing.PointUnique] using unique column)
    (bluePointIndex (.inr (selected, 0))) owner initial_point ⟨1, by norm_num⟩
  convert preserved using 1
  congr 1
  fin_cases selected <;>
    norm_num [movingBluePoints, rowOffsets, height, evenBlueRowIndex] <;>
    norm_num [ShiftedStaggeredLattice.point, blueLattice]

end SquarePackingArchive.BentzFiveRows
