import SquarePackingArchive.BentzFiveRowsMotion

namespace SquarePackingArchive.BentzFiveRows

noncomputable def blueReflectionIndex (index : Fin 23) : Fin 23 :=
  match (Fintype.equivFin (StaggeredLattice.Index 4 2 3)).symm
      (Fin.cast (by simp [StaggeredLattice.Index]) index) with
  | .inl (row, column) => bluePointIndex (.inl (row, column.rev))
  | .inr (row, column) => bluePointIndex (.inr (row, column.rev))

@[simp] theorem blueReflectionIndex_involutive (index : Fin 23) :
    blueReflectionIndex (blueReflectionIndex index) = index := by
  obtain ⟨source, source_eq⟩ := bluePointIndex_surjective index
  subst index
  rcases source with ⟨row, column⟩ | ⟨row, column⟩ <;>
    simp [blueReflectionIndex, bluePointIndex]

theorem blueBasePoints_reflected (index : Fin 23) :
    blueBasePoints (blueReflectionIndex index) = (blueBasePoints index).reflectX 5 := by
  obtain ⟨source, source_eq⟩ := bluePointIndex_surjective index
  subst index
  rcases source with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    simp [blueReflectionIndex, bluePointIndex, blueBasePoints, bluePoints, ShiftedStaggeredLattice.points]
    fin_cases column <;> norm_num [ShiftedStaggeredLattice.point, blueLattice, Point.reflectX, Fin.rev]

noncomputable def scaledBluePoints (side : ℝ) (index : Fin 23) : Point :=
  (blueBasePoints index).scale (side / 5)

theorem scaledBluePoints_reflected (side : ℝ) (index : Fin 23) :
    scaledBluePoints side (blueReflectionIndex index) = (scaledBluePoints side index).reflectX side := by
  rw [scaledBluePoints, blueBasePoints_reflected]
  unfold scaledBluePoints
  rw [Point.mk.injEq]
  dsimp [Point.scale, Point.reflectX]
  constructor <;> ring

theorem blue_reflected_mem_iff {side : ℝ} (packing : Packing 22 side) (owner : Fin 22) (index : Fin 23) :
    (packing.reflectX.squares owner).InteriorContains (scaledBluePoints side index) ↔
      (packing.squares owner).InteriorContains (scaledBluePoints side (blueReflectionIndex index)) := by
  have result := (packing.squares owner).interiorContains_reflectX_iff side
    (scaledBluePoints side (blueReflectionIndex index))
  rw [← scaledBluePoints_reflected, blueReflectionIndex_involutive] at result
  exact result

theorem blue_reflected_unique_iff {side : ℝ} (packing : Packing 22 side) (index : Fin 23) :
    packing.reflectX.PointUnique (scaledBluePoints side) index ↔
      packing.PointUnique (scaledBluePoints side) (blueReflectionIndex index) := by
  constructor
  · rintro ⟨owner, inside, unique⟩
    refine ⟨owner, (blue_reflected_mem_iff packing owner index).1 inside, ?_⟩
    intro other other_inside
    have reflected_inside := (blue_reflected_mem_iff packing owner (blueReflectionIndex other)).2
      (by simpa only [blueReflectionIndex_involutive] using other_inside)
    have equality := congrArg blueReflectionIndex (unique (blueReflectionIndex other) reflected_inside)
    simpa only [blueReflectionIndex_involutive] using equality
  · rintro ⟨owner, inside, unique⟩
    refine ⟨owner, (blue_reflected_mem_iff packing owner index).2 inside, ?_⟩
    intro other other_inside
    have equality := congrArg blueReflectionIndex (unique (blueReflectionIndex other)
      ((blue_reflected_mem_iff packing owner other).1 other_inside))
    simpa only [blueReflectionIndex_involutive] using equality

theorem blue_left_coordinate_gap (index : Fin 23) (left : (blueBasePoints index).x < 2) :
    (blueBasePoints index).x ≤ 3 / 2 := by
  obtain ⟨source, source_eq⟩ := bluePointIndex_surjective index
  subst index
  rcases source with ⟨row, column⟩ | ⟨row, column⟩
  all_goals
    simp only [blueBasePoints, bluePoints_at_index, ShiftedStaggeredLattice.point, blueLattice] at left ⊢
    fin_cases column <;> norm_num at *

def BlueLeftUnique {side : ℝ} (packing : Packing 22 side) : Prop :=
  ∀ index, (blueBasePoints index).x < 2 → packing.PointUnique (scaledBluePoints side) index

theorem blue_left_unique_or_reflected
    {side : ℝ} (packing : Packing 22 side)
    (side_lower : 4999 / 1000 ≤ side) (side_lt_five : side < 5) :
    BlueLeftUnique packing ∨ BlueLeftUnique packing.reflectX := by
  classical
  by_cases left_unique : BlueLeftUnique packing
  · exact Or.inl left_unique
  have bad_left : ∃ index, (blueBasePoints index).x < 2 ∧
      ¬ packing.PointUnique (scaledBluePoints side) index := by
    by_contra missing
    apply left_unique
    intro index left
    by_contra bad
    exact missing ⟨index, left, bad⟩
  obtain ⟨leftIndex, left_coordinate, left_not_unique⟩ := bad_left
  have left_upper := blue_left_coordinate_gap leftIndex left_coordinate
  have unavoidable : InteriorUnavoidable (scaledBluePoints side) side :=
    blue_interior_unavoidable (fun _ => 1 / 2) (by intro row; constructor <;> norm_num)
      (by linarith) side_lt_five
  have bad_coordinate_upper (index : Fin 23)
      (not_unique : ¬ packing.PointUnique (scaledBluePoints side) index) : (blueBasePoints index).x < 3 := by
    rcases packing.interiorUnavoidable_exception_cluster (scaledBluePoints side) unavoidable with
      ⟨extra, failures_extra⟩ | ⟨owner, failures_inside⟩
    · have same := (failures_extra index not_unique).trans (failures_extra leftIndex left_not_unique).symm
      rw [same]
      linarith
    · have distance := ((packing.squares owner).contained_points_coordinate_distance_lt_ten_sevenths
        (failures_inside index not_unique).contains (failures_inside leftIndex left_not_unique).contains).1
      simp only [scaledBluePoints, Point.scale] at distance
      rw [abs_lt] at distance
      by_contra lower
      have point_separation : 3 / 2 ≤ (blueBasePoints index).x - (blueBasePoints leftIndex).x := by linarith
      have scaled_separation : (4999 / 5000 : ℝ) * (3 / 2) ≤
          (side / 5) * ((blueBasePoints index).x - (blueBasePoints leftIndex).x) :=
        mul_le_mul (by linarith) point_separation (by norm_num) (by linarith)
      nlinarith only [scaled_separation, distance.2]
  refine Or.inr ?_
  intro index left
  apply (blue_reflected_unique_iff packing index).2
  by_contra not_unique
  have upper := bad_coordinate_upper (blueReflectionIndex index) not_unique
  rw [blueBasePoints_reflected] at upper
  dsimp [Point.reflectX] at upper
  linarith

end SquarePackingArchive.BentzFiveRows
