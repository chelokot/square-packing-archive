import SquarePackingArchive.BentzSixRowsShift
import SquarePackingArchive.BentzLineCuts

namespace SquarePackingArchive.BentzSixRows

theorem six_left_point_owners
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (endpoints : ∀ candidate : Packing 33 side, ∀ selected : Fin 3, ∀ owner : Fin 33,
      (candidate.squares owner).InteriorContains
        ((rowPoint initialHeights (oddRowIndex selected)).scale (side / 6)) →
      (candidate.squares owner).InteriorContains
        ((Point.mk 1 (compressedHeights (oddRowIndex selected) (oddRowIndex selected))).scale (side / 6))) :
    ∃ owners : Fin 6 ↪ Fin 33, ∀ row,
      (packing.squares (owners row)).InteriorContains
        ((Point.mk (2 / 5) (compressedHeights row row)).scale (side / 6)) := by
  obtain ⟨owners, initially_inside⟩ := initial_row_owners packing side_positive side_lt_six
  obtain ⟨reflectedOwners, reflected_initially_inside⟩ :=
    initial_row_owners packing.reflectY side_positive side_lt_six
  have odd_inside (selected : Fin 3) :
      (packing.squares (owners (oddRowIndex selected))).InteriorContains
        ((Point.mk (2 / 5) (compressedHeights (oddRowIndex selected) (oddRowIndex selected))).scale (side / 6)) :=
    odd_row_reaches_left packing side_positive side_lt_six selected _ (initially_inside _)
  have even_inside (selected : Fin 3) :
      (packing.squares (owners (mirrorRow (oddRowIndex selected)))).InteriorContains
        ((Point.mk (2 / 5) (compressedHeights (mirrorRow (oddRowIndex selected))
          (mirrorRow (oddRowIndex selected)))).scale (side / 6)) := by
    let row := oddRowIndex selected
    have reflected_endpoint := endpoints packing.reflectY selected (reflectedOwners row)
      (reflected_initially_inside row)
    have original_endpoint := reflected_scaled_point_inside packing (reflectedOwners row) reflected_endpoint
    have red_endpoint := compressed_row_same_owner packing side_positive side_lt_six (mirrorRow row)
      (owners (mirrorRow row)) (initially_inside (mirrorRow row))
    have row_point_eq : rowPoint (compressedHeights (mirrorRow row)) (mirrorRow row) =
        Point.mk 1 (6 - compressedHeights row row) := by
      rw [compressedHeights_mirror]
      fin_cases selected <;> simp [rowPoint, row, oddRowIndex, mirrorRow]
    rw [row_point_eq] at red_endpoint
    have owner_eq : reflectedOwners row = owners (mirrorRow row) := by
      by_contra different
      exact packing.disjoint _ _ different _ ⟨original_endpoint, red_endpoint⟩
    have reflected_left := odd_row_reaches_left packing.reflectY side_positive side_lt_six selected
      (reflectedOwners row) (reflected_initially_inside row)
    have original_left := reflected_scaled_point_inside packing (reflectedOwners row) reflected_left
    simpa only [owner_eq, compressedHeights_mirror] using original_left
  refine ⟨owners, ?_⟩
  intro row
  fin_cases row
  · exact even_inside 2
  · exact odd_inside 0
  · exact even_inside 1
  · exact odd_inside 1
  · exact even_inside 0
  · exact odd_inside 2

theorem contradiction_of_row_endpoints
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (endpoints : ∀ candidate : Packing 33 side, ∀ selected : Fin 3, ∀ owner : Fin 33,
      (candidate.squares owner).InteriorContains
        ((rowPoint initialHeights (oddRowIndex selected)).scale (side / 6)) →
      (candidate.squares owner).InteriorContains
        ((Point.mk 1 (compressedHeights (oddRowIndex selected) (oddRowIndex selected))).scale (side / 6))) : False := by
  obtain ⟨owners, inside⟩ := six_left_point_owners packing side_positive side_lt_six endpoints
  have side_bound := Bentz.count_le_side_of_left_points packing owners
    (fun row => (Point.mk (2 / 5) (compressedHeights row row)).scale (side / 6))
    (by
      intro row
      obtain ⟨localX, localY, horizontal_bound, vertical_bound, equality⟩ := inside row
      exact ⟨localX, localY, horizontal_bound.le, vertical_bound.le, equality⟩)
    (by intro row; dsimp [Point.scale]; linarith)
  norm_num only [Nat.cast_ofNat] at side_bound
  linarith

end SquarePackingArchive.BentzSixRows
