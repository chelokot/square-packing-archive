import SquarePackingArchive.BentzFiveRowsReflection
import SquarePackingArchive.BentzSixRowsEndpoint

namespace SquarePackingArchive

theorem strictUnavoidable_update_of_forced
    {count : ℕ} {side : ℝ} (points : Fin count → Point) (selected : Fin count) (replacement : Point)
    (unavoidable : ∀ square : PlacedSquare, square.StrictFits side → ∃ index, square.Contains (points index))
    (forced : ∀ square : PlacedSquare, square.StrictFits side → square.Contains (points selected) →
      (∀ index, index ≠ selected → ¬ square.Contains (points index)) → square.Contains replacement) :
    ∀ square : PlacedSquare, square.StrictFits side →
      ∃ index, square.Contains (Function.update points selected replacement index) := by
  classical
  intro square strict
  by_cases retained : ∃ index, index ≠ selected ∧ square.Contains (points index)
  · obtain ⟨index, different, inside⟩ := retained
    exact ⟨index, by simpa [Function.update_of_ne different] using inside⟩
  obtain ⟨index, inside⟩ := unavoidable square strict
  have index_eq : index = selected := by
    by_contra different
    exact retained ⟨index, different, inside⟩
  subst index
  exact ⟨selected, by simpa using forced square strict inside (fun index different point_inside =>
    retained ⟨index, different, point_inside⟩)⟩

theorem Packing.unique_point_follows_replacement
    {count pointCount : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin pointCount → Point) (selected : Fin pointCount) (replacement : Point) (owner : Fin count)
    (unavoidable : InteriorUnavoidable (Function.update points selected replacement) side)
    (unique : ∀ index, (packing.squares owner).InteriorContains (points index) → index = selected) :
    (packing.squares owner).InteriorContains replacement := by
  classical
  obtain ⟨index, inside⟩ := unavoidable (packing.squares owner) (packing.fits owner)
  by_cases same : index = selected
  · simpa [same] using inside
  · exact (same (unique index (by simpa [Function.update_of_ne same] using inside))).elim

theorem scale_updated_points {count : ℕ} (points : Fin count → Point)
    (selected : Fin count) (replacement : Point) (factor : ℝ) :
    (fun index => (Function.update points selected replacement index).scale factor) =
      Function.update (fun index => (points index).scale factor) selected (replacement.scale factor) := by
  classical
  funext index
  by_cases same : index = selected <;> simp [same, Function.update_of_ne]

namespace BentzFiveRows

noncomputable def blueRowIndex (row : Fin 5) : Fin 23 :=
  if even : row.val % 2 = 0 then bluePointIndex (.inr (⟨row.val / 2, by omega⟩, 0))
  else bluePointIndex (.inl (⟨row.val / 2, by omega⟩, 0))

noncomputable def blueRowPoint (row : Fin 5) : Point :=
  ⟨if row.val % 2 = 0 then 1 / 2 else 1, height row⟩

@[simp] theorem blueBasePoints_at_row (row : Fin 5) : blueBasePoints (blueRowIndex row) = blueRowPoint row := by
  fin_cases row <;> norm_num [blueBasePoints, blueRowIndex, blueRowPoint, height] <;>
    norm_num [ShiftedStaggeredLattice.point, blueLattice]

theorem blueRowIndex_injective : Function.Injective blueRowIndex := by
  intro first second equality
  have height_eq := congrArg (fun index => (blueBasePoints index).y) equality
  simp only [blueBasePoints_at_row, blueRowPoint] at height_eq
  have val_eq : (first : ℝ) = (second : ℝ) := by dsimp [height] at height_eq; linarith
  exact Fin.ext (by exact_mod_cast val_eq)

theorem bottom_endpoint_forced
    (square : PlacedSquare) {side targetHeight : ℝ} (fits : square.Fits side)
    (height_upper : targetHeight ≤ 1)
    (point_mem : square.Contains ⟨1 / 2, targetHeight⟩)
    (above_missing : ¬ square.Contains ⟨1, targetHeight + 4 / 5⟩) :
    square.Contains ⟨1, targetHeight⟩ := by
  by_cases center_right : 1 ≤ square.center.x
  · exact BentzSixRows.half_point_forces_one_of_center_right square point_mem center_right
  by_cases below : square.center.y ≤ targetHeight
  · exact square.contains_cornerPoint fits (by norm_num) height_upper (by linarith) below
  have height_bounds := BentzSixRows.center_height_close_to_contained_point square point_mem
  have pair := square.contains_leftPair_of_gap_le_four_fifths fits
    (lowerHeight := targetHeight) (upperHeight := targetHeight + 4 / 5)
    (by norm_num) (by linarith) (by linarith) (by linarith) height_bounds.2.le
  exact pair.resolve_right above_missing

theorem top_endpoint_forced
    (square : PlacedSquare) {side targetHeight : ℝ} (fits : square.Fits side)
    (height_lower : side - targetHeight ≤ 1)
    (point_mem : square.Contains ⟨1 / 2, targetHeight⟩)
    (below_missing : ¬ square.Contains ⟨1, targetHeight - 4 / 5⟩) :
    square.Contains ⟨1, targetHeight⟩ := by
  have reflected := bottom_endpoint_forced (square.reflectY side)
    ((square.reflectY_fits_iff side).2 fits) height_lower
    ((square.reflectY_contains_iff side ⟨1 / 2, targetHeight⟩).2 point_mem)
    (by
      intro reflected_inside
      apply below_missing
      apply (square.reflectY_contains_iff side _).1
      convert reflected_inside using 1
      dsimp [Point.reflectY]
      congr 1
      ring)
  exact (square.reflectY_contains_iff side ⟨1, targetHeight⟩).1 reflected

theorem red_endpoint_forced
    (selected : Fin 2) (square : PlacedSquare) (fits : square.Fits 5)
    (inside : square.Contains (redRowPoint (oddRedRowIndex selected)))
    (others_missing : ∀ row, row ≠ oddRedRowIndex selected → ¬ square.Contains (redRowPoint row)) :
    square.Contains ⟨1, height (oddRedRowIndex selected)⟩ := by
  fin_cases selected
  · apply BentzSixRows.middle_endpoint_forced square fits
    · simpa [redRowPoint, oddRedRowIndex] using inside
    · convert others_missing 0 (by decide) using 1
      norm_num [redRowPoint, oddRedRowIndex, height]
    · convert others_missing 2 (by decide) using 1
      norm_num [redRowPoint, oddRedRowIndex, height]
  · apply BentzSixRows.middle_endpoint_forced square fits
    · simpa [redRowPoint, oddRedRowIndex] using inside
    · convert others_missing 2 (by decide) using 1
      norm_num [redRowPoint, oddRedRowIndex, height]
    · convert others_missing 4 (by decide) using 1
      norm_num [redRowPoint, oddRedRowIndex, height]

theorem blue_endpoint_forced
    (selected : Fin 3) (square : PlacedSquare) (fits : square.Fits 5)
    (inside : square.Contains (blueRowPoint (evenBlueRowIndex selected)))
    (others_missing : ∀ row, row ≠ evenBlueRowIndex selected → ¬ square.Contains (blueRowPoint row)) :
    square.Contains ⟨1, height (evenBlueRowIndex selected)⟩ := by
  fin_cases selected
  · apply bottom_endpoint_forced square fits (by norm_num [height, evenBlueRowIndex])
    · simpa [blueRowPoint, evenBlueRowIndex] using inside
    · convert others_missing 1 (by decide) using 1
      norm_num [blueRowPoint, evenBlueRowIndex, height]
  · apply BentzSixRows.middle_endpoint_forced square fits
    · simpa [blueRowPoint, evenBlueRowIndex] using inside
    · convert others_missing 1 (by decide) using 1
      norm_num [blueRowPoint, evenBlueRowIndex, height]
    · convert others_missing 3 (by decide) using 1
      norm_num [blueRowPoint, evenBlueRowIndex, height]
  · apply top_endpoint_forced square fits (by norm_num [height, evenBlueRowIndex])
    · simpa [blueRowPoint, evenBlueRowIndex] using inside
    · convert others_missing 3 (by decide) using 1
      norm_num [blueRowPoint, evenBlueRowIndex, height]

theorem red_endpoint_strict_unavoidable (selected : Fin 2) :
    ∀ square : PlacedSquare, square.StrictFits 5 →
      ∃ index, square.Contains (Function.update redBasePoints (redRowIndex (oddRedRowIndex selected))
        ⟨1, height (oddRedRowIndex selected)⟩ index) := by
  apply strictUnavoidable_update_of_forced
  · intro square strict
    obtain ⟨index, inside⟩ := red_strict_unavoidable (fun _ => 1 / 2)
      (by intro row; constructor <;> norm_num) square (by norm_num only [Nat.cast_ofNat]; exact strict)
    exact ⟨redPointIndex index, by simpa only [redBasePoints, redPoints_at_index] using inside⟩
  · intro square strict inside others_missing
    apply red_endpoint_forced selected square strict.fits
    · simpa only [redBasePoints_at_row] using inside
    · intro row different
      simpa only [redBasePoints_at_row] using
        others_missing (redRowIndex row) (fun same => different (redRowIndex_injective same))

theorem blue_endpoint_strict_unavoidable (selected : Fin 3) :
    ∀ square : PlacedSquare, square.StrictFits 5 →
      ∃ index, square.Contains (Function.update blueBasePoints (blueRowIndex (evenBlueRowIndex selected))
        ⟨1, height (evenBlueRowIndex selected)⟩ index) := by
  apply strictUnavoidable_update_of_forced
  · intro square strict
    obtain ⟨index, inside⟩ := blue_strict_unavoidable (fun _ => 1 / 2)
      (by intro row; constructor <;> norm_num) square (by norm_num only [Nat.cast_ofNat]; exact strict)
    exact ⟨bluePointIndex index, by simpa only [blueBasePoints, bluePoints_at_index] using inside⟩
  · intro square strict inside others_missing
    apply blue_endpoint_forced selected square strict.fits
    · simpa only [blueBasePoints_at_row] using inside
    · intro row different
      simpa only [blueBasePoints_at_row] using
        others_missing (blueRowIndex row) (fun same => different (blueRowIndex_injective same))

theorem red_row_endpoint_same_owner
    {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5)
    (selected : Fin 2) (owner : Fin 22)
    (initially_inside : (packing.squares owner).InteriorContains
      ((redRowPoint (oddRedRowIndex selected)).scale (side / 5))) :
    (packing.squares owner).InteriorContains
      ((Point.mk 1 (height (oddRedRowIndex selected))).scale (side / 5)) := by
  have new_unavoidable := strictUnavoidable_interior_scaled side_positive side_lt_five
    (red_endpoint_strict_unavoidable selected)
  rw [scale_updated_points] at new_unavoidable
  apply packing.unique_point_follows_replacement _ _ _ owner new_unavoidable
  intro index inside
  exact packing.interiorUnavoidable_same_owner_same_point_index _
    (red_interior_unavoidable (fun _ => 1 / 2) (by intro row; constructor <;> norm_num)
      side_positive side_lt_five) owner index (redRowIndex (oddRedRowIndex selected)) inside
    (by
      change (packing.squares owner).InteriorContains
        ((redBasePoints (redRowIndex (oddRedRowIndex selected))).scale (side / 5))
      simpa only [redBasePoints_at_row] using initially_inside)

theorem blue_row_endpoint_same_owner
    {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5)
    (left_unique : BlueLeftUnique packing)
    (selected : Fin 3) (owner : Fin 22)
    (initially_inside : (packing.squares owner).InteriorContains
      ((Point.mk (1 / 2) (height (evenBlueRowIndex selected))).scale (side / 5))) :
    (packing.squares owner).InteriorContains
      ((Point.mk 1 (height (evenBlueRowIndex selected))).scale (side / 5)) := by
  have new_unavoidable := strictUnavoidable_interior_scaled side_positive side_lt_five
    (blue_endpoint_strict_unavoidable selected)
  rw [scale_updated_points] at new_unavoidable
  have unique_point := left_unique (blueRowIndex (evenBlueRowIndex selected)) (by
    rw [blueBasePoints_at_row]
    fin_cases selected <;> norm_num [blueRowPoint, evenBlueRowIndex])
  obtain ⟨actualOwner, actual_inside, unique⟩ := unique_point
  have same_owner : actualOwner = owner := by
    by_contra different
    apply packing.disjoint _ _ different _ ⟨actual_inside, ?_⟩
    convert initially_inside using 1
    rw [scaledBluePoints, blueBasePoints_at_row]
    fin_cases selected <;> simp [blueRowPoint, evenBlueRowIndex]
  subst actualOwner
  exact packing.unique_point_follows_replacement _ _ _ owner new_unavoidable unique

end BentzFiveRows

end SquarePackingArchive
