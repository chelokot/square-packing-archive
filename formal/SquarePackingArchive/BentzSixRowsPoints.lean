import SquarePackingArchive.BentzSixRows

namespace SquarePackingArchive.BentzSixRows

noncomputable def pointIndex (index : StaggeredLattice.Index 5 3 3) : Fin 33 :=
  Fin.cast (by simp [StaggeredLattice.Index]) ((Fintype.equivFin (StaggeredLattice.Index 5 3 3)) index)

@[simp] theorem points_at_pointIndex (heights : Fin 6 → ℝ)
    (index : StaggeredLattice.Index 5 3 3) :
    (lattice heights).points (pointIndex index) = (lattice heights).point index := by
  simp [pointIndex, StaggeredLattice.points]

noncomputable def rowPointIndex (row : Fin 6) : Fin 33 :=
  if row.val % 2 = 0 then
    pointIndex (.inl (⟨row.val / 2, by omega⟩, 0))
  else pointIndex (.inr (⟨row.val / 2, by omega⟩, 0))

noncomputable def rowPoint (heights : Fin 6 → ℝ) (row : Fin 6) : Point :=
  ⟨if row.val % 2 = 0 then 1 else 1 / 2, heights row⟩

def mirrorRow (row : Fin 6) : Fin 6 := ⟨5 - row.val, by omega⟩

@[simp] theorem mirrorRow_mirrorRow (row : Fin 6) : mirrorRow (mirrorRow row) = row := by
  apply Fin.ext
  dsimp [mirrorRow]
  omega

theorem compressedHeights_mirror (selected row : Fin 6) :
    6 - compressedHeights selected row = compressedHeights (mirrorRow selected) (mirrorRow row) := by
  fin_cases selected <;> fin_cases row <;>
    norm_num [compressedHeights, mirrorRow, Matrix.cons_val_two]

theorem compressed_diagonal_mirror (row : Fin 6) :
    6 - compressedHeights (mirrorRow row) (mirrorRow row) = compressedHeights row row := by
  simpa only [mirrorRow_mirrorRow] using compressedHeights_mirror (mirrorRow row) (mirrorRow row)

@[simp] theorem points_at_rowPointIndex (heights : Fin 6 → ℝ) (row : Fin 6) :
    (lattice heights).points (rowPointIndex row) = rowPoint heights row := by
  fin_cases row <;> norm_num [rowPointIndex, rowPoint, points_at_pointIndex] <;>
    norm_num [StaggeredLattice.point, lattice]

theorem rowPointIndex_injective : Function.Injective rowPointIndex := by
  intro first second index_eq
  have point_eq := congrArg (fun index => ((lattice initialHeights).points index).y) index_eq
  simp only [points_at_rowPointIndex, rowPoint] at point_eq
  have val_eq : (first : ℝ) = (second : ℝ) := by
    dsimp [initialHeights] at point_eq
    linarith
  exact Fin.ext (by exact_mod_cast val_eq)

theorem initial_points_interior_unavoidable {side : ℝ}
    (side_positive : 0 < side) (side_lt_six : side < 6) :
    InteriorUnavoidable (fun index => ((lattice initialHeights).points index).scale (side / 6)) side := by
  have result := compressionPoints_interior_unavoidable 0 (position := 0)
    (by norm_num) (by norm_num) side_positive side_lt_six
  simpa only [compressionPoints, interpolate_zero] using result

theorem initial_row_owners {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6) :
    ∃ owners : Fin 6 ↪ Fin 33, ∀ row,
      (packing.squares (owners row)).InteriorContains ((rowPoint initialHeights row).scale (side / 6)) := by
  classical
  obtain ⟨assigned, bijective, inside⟩ := packing.interiorUnavoidable_bijective_assignment
    (fun index => ((lattice initialHeights).points index).scale (side / 6))
    (initial_points_interior_unavoidable side_positive side_lt_six)
  let assignment := Equiv.ofBijective assigned bijective
  let owners : Fin 6 ↪ Fin 33 :=
    ⟨fun row => assignment.symm (rowPointIndex row), assignment.symm.injective.comp rowPointIndex_injective⟩
  refine ⟨owners, ?_⟩
  intro row
  have contained := inside (owners row)
  have assigned_eq : assigned (owners row) = rowPointIndex row := assignment.apply_symm_apply _
  rw [assigned_eq, points_at_rowPointIndex] at contained
  exact contained

theorem compressed_row_same_owner {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (row : Fin 6) (owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      ((rowPoint initialHeights row).scale (side / 6))) :
    (packing.squares owner).InteriorContains
      ((rowPoint (compressedHeights row) row).scale (side / 6)) := by
  have contained := compressed_endpoint_same_owner packing side_positive side_lt_six row
    (rowPointIndex row) owner (by simpa only [points_at_rowPointIndex] using initially_inside)
  simpa only [points_at_rowPointIndex] using contained

theorem reflected_scaled_point_inside
    {count : ℕ} {side horizontal height : ℝ} (packing : Packing count side) (owner : Fin count)
    (inside : (packing.reflectY.squares owner).InteriorContains
      ((Point.mk horizontal height).scale (side / 6))) :
    (packing.squares owner).InteriorContains
      ((Point.mk horizontal (6 - height)).scale (side / 6)) := by
  apply ((packing.squares owner).interiorContains_reflectY_iff side _).1
  convert inside using 1
  congr 1
  rw [Point.mk.injEq]
  dsimp [Point.reflectY, Point.scale]
  constructor <;> ring

end SquarePackingArchive.BentzSixRows
