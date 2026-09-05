import SquarePackingArchive.BentzFiveRowsEndpoint

namespace SquarePackingArchive.BentzFiveRows

theorem blue_half_point_unique
    {side : ℝ} (packing : Packing 22 side) (left_unique : BlueLeftUnique packing)
    (selected : Fin 3) :
    ∃ owner, (packing.squares owner).InteriorContains
      ((Point.mk (1 / 2) (height (evenBlueRowIndex selected))).scale (side / 5)) ∧
      ∀ index, (packing.squares owner).InteriorContains (scaledBluePoints side index) →
        index = blueRowIndex (evenBlueRowIndex selected) := by
  obtain ⟨owner, inside, unique⟩ := left_unique (blueRowIndex (evenBlueRowIndex selected)) (by
    rw [blueBasePoints_at_row]
    fin_cases selected <;> norm_num [blueRowPoint, evenBlueRowIndex])
  refine ⟨owner, ?_, unique⟩
  rw [scaledBluePoints, blueBasePoints_at_row] at inside
  fin_cases selected <;> simpa [blueRowPoint, evenBlueRowIndex] using inside

theorem blue_half_point_misses_right
    {side : ℝ} (packing : Packing 22 side) (left_unique : BlueLeftUnique packing)
    (selected : Fin 3) (owner : Fin 22)
    (half_inside : (packing.squares owner).InteriorContains
      ((Point.mk (1 / 2) (height (evenBlueRowIndex selected))).scale (side / 5))) :
    ¬ (packing.squares owner).InteriorContains
      ((Point.mk (3 / 2) (height (evenBlueRowIndex selected))).scale (side / 5)) := by
  obtain ⟨actualOwner, actual_inside, unique⟩ := blue_half_point_unique packing left_unique selected
  have same_owner : actualOwner = owner := by
    by_contra different
    exact packing.disjoint _ _ different _ ⟨actual_inside, half_inside⟩
  subst actualOwner
  intro right_inside
  have right_as_index : (packing.squares owner).InteriorContains
      (scaledBluePoints side (bluePointIndex (.inr (selected, 1)))) := by
    convert right_inside using 1
    fin_cases selected <;>
      norm_num [scaledBluePoints, blueBasePoints, evenBlueRowIndex, height,
        ShiftedStaggeredLattice.point, blueLattice]
  have equality := unique _ right_as_index
  have coordinate_eq := congrArg (fun index => (blueBasePoints index).x) equality
  rw [blueBasePoints_at_row] at coordinate_eq
  fin_cases selected <;>
    norm_num [blueBasePoints, blueRowPoint, evenBlueRowIndex,
      ShiftedStaggeredLattice.point, blueLattice] at coordinate_eq

theorem five_row_witnesses
    {side : ℝ} (packing : Packing 22 side)
    (side_lower : 4999 / 1000 ≤ side) (side_lt_five : side < 5)
    (left_unique : BlueLeftUnique packing) :
    ∃ owners : Fin 5 ↪ Fin 22, ∃ exception : Fin 3,
      (∀ row, (packing.squares (owners row)).InteriorContains
        ((Point.mk (1 / 2) (height row)).scale (side / 5))) ∧
      (∀ row, (packing.squares (owners row)).InteriorContains
        ((Point.mk 1 (height row)).scale (side / 5))) ∧
      (∀ row, row ≠ evenBlueRowIndex exception →
        (packing.squares (owners row)).InteriorContains
          ((Point.mk (2 / 5) (height row)).scale (side / 5))) ∧
      ¬ (packing.squares (owners (evenBlueRowIndex exception))).InteriorContains
        ((Point.mk (3 / 2) (height (evenBlueRowIndex exception))).scale (side / 5)) := by
  have side_positive : 0 < side := by linarith
  obtain ⟨owners, red_inside⟩ := red_initial_owners packing side_positive side_lt_five
  obtain ⟨exception, row_unique⟩ := at_most_one_exceptional_blue_row packing side_lower side_lt_five
  have blue_half_inside (selected : Fin 3) :
      (packing.squares (owners (evenBlueRowIndex selected))).InteriorContains
        ((Point.mk (1 / 2) (height (evenBlueRowIndex selected))).scale (side / 5)) := by
    obtain ⟨blueOwner, half_inside, _⟩ := blue_half_point_unique packing left_unique selected
    have endpoint := blue_row_endpoint_same_owner packing side_positive side_lt_five
      left_unique selected blueOwner half_inside
    have red_endpoint := red_inside (evenBlueRowIndex selected)
    have endpoint_same : (packing.squares (owners (evenBlueRowIndex selected))).InteriorContains
        ((Point.mk 1 (height (evenBlueRowIndex selected))).scale (side / 5)) := by
      fin_cases selected <;> simpa [redRowPoint, evenBlueRowIndex] using red_endpoint
    have owner_eq : blueOwner = owners (evenBlueRowIndex selected) := by
      by_contra different
      exact packing.disjoint _ _ different _ ⟨endpoint, endpoint_same⟩
    simpa only [owner_eq] using half_inside
  have red_half_inside (selected : Fin 2) :
      (packing.squares (owners (oddRedRowIndex selected))).InteriorContains
        ((Point.mk (1 / 2) (height (oddRedRowIndex selected))).scale (side / 5)) := by
    have inside := red_inside (oddRedRowIndex selected)
    fin_cases selected <;> simpa [redRowPoint, oddRedRowIndex] using inside
  have blue_one_inside (selected : Fin 3) := blue_row_endpoint_same_owner packing
    side_positive side_lt_five left_unique selected _ (blue_half_inside selected)
  have red_one_inside (selected : Fin 2) := red_row_endpoint_same_owner packing
    side_positive side_lt_five selected _ (red_inside (oddRedRowIndex selected))
  have red_left_inside (selected : Fin 2) := red_row_reaches_left packing
    side_positive side_lt_five selected _ (red_inside (oddRedRowIndex selected))
  have blue_left_inside (selected : Fin 3) (different : selected ≠ exception) :=
    blue_unique_row_reaches_left packing side_positive side_lt_five selected
      (row_unique selected different) _ (blue_half_inside selected)
  refine ⟨owners, exception, ?_, ?_, ?_, ?_⟩
  · intro row
    fin_cases row
    · exact blue_half_inside 0
    · exact red_half_inside 0
    · exact blue_half_inside 1
    · exact red_half_inside 1
    · exact blue_half_inside 2
  · intro row
    fin_cases row
    · exact blue_one_inside 0
    · exact red_one_inside 0
    · exact blue_one_inside 1
    · exact red_one_inside 1
    · exact blue_one_inside 2
  · intro row different
    fin_cases row
    · exact blue_left_inside 0 (fun same => different (by rw [← same]; rfl))
    · exact red_left_inside 0
    · exact blue_left_inside 1 (fun same => different (by rw [← same]; rfl))
    · exact red_left_inside 1
    · exact blue_left_inside 2 (fun same => different (by rw [← same]; rfl))
  · exact blue_half_point_misses_right packing left_unique exception _ (blue_half_inside exception)

end SquarePackingArchive.BentzFiveRows
