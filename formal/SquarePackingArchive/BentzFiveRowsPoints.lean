import SquarePackingArchive.BentzFiveRows

namespace SquarePackingArchive

lemma PlacedSquare.InteriorContains.contains {square : PlacedSquare} {point : Point}
    (inside : square.InteriorContains point) : square.Contains point := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, equality⟩ := inside
  exact ⟨localX, localY, horizontal_bound.le, vertical_bound.le, equality⟩

lemma PlacedSquare.contained_points_distance_sq_le_two
    (square : PlacedSquare) {first second : Point}
    (first_inside : square.Contains first) (second_inside : square.Contains second) :
    (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2 ≤ 2 := by
  have first_bounds := (square.contains_iff_localCoordinates first).1 first_inside
  have second_bounds := (square.contains_iff_localCoordinates second).1 second_inside
  rw [abs_le, abs_le] at first_bounds second_bounds
  have horizontal_bound : (square.localX first - square.localX second) ^ 2 ≤ 1 := by nlinarith
  have vertical_bound : (square.localY first - square.localY second) ^ 2 ≤ 1 := by nlinarith
  nlinarith only [square.local_coordinate_distance_sq first second, horizontal_bound, vertical_bound]

lemma PlacedSquare.contained_points_coordinate_distance_lt_ten_sevenths
    (square : PlacedSquare) {first second : Point}
    (first_inside : square.Contains first) (second_inside : square.Contains second) :
    |first.x - second.x| < 10 / 7 ∧ |first.y - second.y| < 10 / 7 := by
  have distance := square.contained_points_distance_sq_le_two first_inside second_inside
  constructor <;> rw [abs_lt] <;> constructor <;>
    nlinarith [sq_nonneg (first.x - second.x), sq_nonneg (first.y - second.y)]

namespace BentzFiveRows

noncomputable def redPointIndex (index : StaggeredLattice.Index 4 3 2) : Fin 22 :=
  Fin.cast (by simp [StaggeredLattice.Index]) ((Fintype.equivFin (StaggeredLattice.Index 4 3 2)) index)

noncomputable def bluePointIndex (index : StaggeredLattice.Index 4 2 3) : Fin 23 :=
  Fin.cast (by simp [StaggeredLattice.Index]) ((Fintype.equivFin (StaggeredLattice.Index 4 2 3)) index)

@[simp] theorem redPoints_at_index (offsets : Fin 2 → ℝ) (index : StaggeredLattice.Index 4 3 2) :
    redPoints offsets (redPointIndex index) = (redLattice offsets).point index := by
  simp [redPointIndex, redPoints, ShiftedStaggeredLattice.points]

@[simp] theorem bluePoints_at_index (offsets : Fin 3 → ℝ) (index : StaggeredLattice.Index 4 2 3) :
    bluePoints offsets (bluePointIndex index) = (blueLattice offsets).point index := by
  simp [bluePointIndex, bluePoints, ShiftedStaggeredLattice.points]

noncomputable def redBasePoints : Fin 22 → Point := redPoints (fun _ => 1 / 2)

noncomputable def blueBasePoints : Fin 23 → Point := bluePoints (fun _ => 1 / 2)

noncomputable def redRowIndex (row : Fin 5) : Fin 22 :=
  if even : row.val % 2 = 0 then redPointIndex (.inl (⟨row.val / 2, by omega⟩, 0))
  else redPointIndex (.inr (⟨row.val / 2, by omega⟩, 0))

noncomputable def redRowPoint (row : Fin 5) : Point :=
  ⟨if row.val % 2 = 0 then 1 else 1 / 2, height row⟩

@[simp] theorem redBasePoints_at_row (row : Fin 5) : redBasePoints (redRowIndex row) = redRowPoint row := by
  fin_cases row <;> norm_num [redBasePoints, redRowIndex, redRowPoint, height] <;>
    norm_num [ShiftedStaggeredLattice.point, redLattice, Records.Square23.lattice]

theorem redRowIndex_injective : Function.Injective redRowIndex := by
  intro first second equality
  have height_eq := congrArg (fun index => (redBasePoints index).y) equality
  simp only [redBasePoints_at_row, redRowPoint] at height_eq
  have val_eq : (first : ℝ) = (second : ℝ) := by dsimp [height] at height_eq; linarith
  exact Fin.ext (by exact_mod_cast val_eq)

theorem red_initial_owners {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5) :
    ∃ owners : Fin 5 ↪ Fin 22, ∀ row,
      (packing.squares (owners row)).InteriorContains ((redRowPoint row).scale (side / 5)) := by
  classical
  obtain ⟨assigned, bijective, inside⟩ := packing.interiorUnavoidable_bijective_assignment
    (fun index => (redBasePoints index).scale (side / 5))
    (red_interior_unavoidable (fun _ => 1 / 2) (by intro row; constructor <;> norm_num)
      side_positive side_lt_five)
  let assignment := Equiv.ofBijective assigned bijective
  let owners : Fin 5 ↪ Fin 22 :=
    ⟨fun row => assignment.symm (redRowIndex row), assignment.symm.injective.comp redRowIndex_injective⟩
  refine ⟨owners, ?_⟩
  intro row
  have contained := inside (owners row)
  have assigned_eq : assigned (owners row) = redRowIndex row := assignment.apply_symm_apply _
  rw [assigned_eq, redBasePoints_at_row] at contained
  exact contained

theorem blue_assignment_exceptions {side : ℝ} (packing : Packing 22 side)
    (side_positive : 0 < side) (side_lt_five : side < 5) :
    ∃ extra : Fin 23,
      (∀ index, (∀ owner, ¬ (packing.squares owner).InteriorContains
        ((blueBasePoints index).scale (side / 5))) → index = extra) ∧
      (∀ owner first second, first ≠ second →
        (packing.squares owner).InteriorContains ((blueBasePoints first).scale (side / 5)) →
        (packing.squares owner).InteriorContains ((blueBasePoints second).scale (side / 5)) →
        first = extra ∨ second = extra) :=
  packing.interiorUnavoidable_one_extra_exceptions
    (fun index => (blueBasePoints index).scale (side / 5))
    (blue_interior_unavoidable (fun _ => 1 / 2) (by intro row; constructor <;> norm_num)
      side_positive side_lt_five)

end BentzFiveRows

end SquarePackingArchive
