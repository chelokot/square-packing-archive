import SquarePackingArchive.NagamochiBoundaryOrientation
import SquarePackingArchive.NagamochiCornerTerminalRepayment
import SquarePackingArchive.NagamochiCanonicalComponents

namespace SquarePackingArchive

open MeasureTheory Set

theorem Nagamochi.bottom_terminal_owner_score_repays
    {size coordinate : ℕ} {side factor height : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (owner : Fin (size * size - 2)) (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 1))
    (anchor : ![(coordinate : ℝ), 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal (packing.squares owner) factor coordinate height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    (coordinate ∈ Finset.Icc 2 (size - 2) ∧
      ENNReal.ofReal (1 + 2 * ((1 - height) / 2)) <
        NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor)) ∨
    (coordinate = size - 1 ∧ ENNReal.ofReal (1 + (1 - height) / 2) <
        NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor)) := by
  have coordinate_bounds := Finset.mem_Icc.mp coordinate_mem
  have previous_missing : ![(coordinate : ℝ) - 1, 9 / 10] ∉
      (packing.squares owner).dilatedInteriorRegion factor := by
    intro previous_mem
    apply packing.squareMinusTwo_not_adjacent_bottom_marks (coordinate := coordinate - 1)
      size_lower factor_gt_one factor_at_most scaled_side_le
      (by simp only [Finset.mem_Icc]; omega) owner
    rw [Nat.cast_sub (by omega : 1 ≤ coordinate), Nat.cast_one]
    exact ⟨previous_mem, by simpa using anchor⟩
  by_cases endpoint : coordinate = size - 1
  · apply Or.inr
    refine ⟨endpoint, ?_⟩
    have coordinate_real : (coordinate : ℝ) = (size : ℝ) - 1 := by
      rw [endpoint, Nat.cast_sub (by omega), Nat.cast_one]
    apply right_corner_terminal_score_repays (packing.squares owner) (packing.fits owner)
      size_lower factor_gt_one factor_at_most scaled_side_le (by rwa [← coordinate_real])
      ?_ (by simpa [endpoint] using terminal) height_mem
    norm_num [coordinate_real, sub_sub] at previous_missing
    exact previous_missing
  · have interior_mem : coordinate ∈ Finset.Icc 2 (size - 2) := by
      simp only [Finset.mem_Icc]
      omega
    have next_missing : ![(coordinate : ℝ) + 1, 9 / 10] ∉
        (packing.squares owner).dilatedInteriorRegion factor := by
      intro next_mem
      exact packing.squareMinusTwo_not_adjacent_bottom_marks size_lower factor_gt_one factor_at_most
        scaled_side_le (by simp only [Finset.mem_Icc] at interior_mem ⊢; omega) owner ⟨anchor, next_mem⟩
    have result := terminal_two_height_score_repays (packing.squares owner) (packing.fits owner)
      size_lower factor_gt_one factor_at_most scaled_side_le interior_mem anchor previous_missing next_missing
      terminal terminal height_mem height_mem
    exact Or.inl ⟨interior_mem, by convert result using 1; congr 1; ring⟩

lemma NagamochiResource.CornerPoint.originalCoordinate_interior
    (corner : NagamochiResource.CornerPoint) {size coordinate : ℕ}
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2)) :
    ∃ physicalCoordinate ∈ Finset.Icc 2 (size - 2),
      (physicalCoordinate : ℝ) = corner.originalCoordinate size coordinate := by
  have bounds := Finset.mem_Icc.mp coordinate_mem
  unfold originalCoordinate
  split
  · refine ⟨size - coordinate, ?_, Nat.cast_sub (by omega)⟩
    simp only [Finset.mem_Icc]
    omega
  · exact ⟨coordinate, coordinate_mem, rfl⟩

theorem Nagamochi.bad_corner_owner_has_repaid_terminal
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (corner : NagamochiResource.CornerPoint) (origin : Fin (size * size - 2))
    (corner_mem : NagamochiResource.cornerPoint size corner ∈
      (packing.squares origin).dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) ≤ 1) :
    ∃ coordinate ∈ Finset.Icc 2 (size - 1), ∃ owner height,
      height ∈ Icc (9 / 10 : ℝ) 1 ∧
      Nagamochi.BoundaryChainTerminal
        (corner.canonicalSquare (packing.squares owner) (size / factor)) factor coordinate height ∧
      ENNReal.ofReal ((1 + height) / 2) <
        NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) ∧
      ((coordinate ∈ Finset.Icc 2 (size - 2) ∧
        (∃ physicalCoordinate ∈ Finset.Icc 2 (size - 2),
          NagamochiResource.edgePoint size physicalCoordinate corner.edge ∈
            (packing.squares owner).dilatedInteriorRegion factor) ∧
        ENNReal.ofReal (1 + 2 * ((1 - height) / 2)) <
          NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor)) ∨
       (coordinate = size - 1 ∧
        NagamochiResource.cornerPoint size corner.oppositeEndpoint ∈
          (packing.squares owner).dilatedInteriorRegion factor ∧
        ENNReal.ofReal (1 + (1 - height) / 2) <
          NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor))) := by
  obtain ⟨coordinate, coordinate_mem, owner, height, height_mem, anchor, terminal, origin_budget⟩ :=
    bad_corner_owner_reaches_weighted_terminal packing size_lower factor_gt_one factor_at_most
      scaled_side_le corner origin corner_mem bad
  have positive : 0 < factor := by linarith
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ positive]
    nlinarith
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  let enlarged := packing.enlarge side_bound
  let canonical := corner.canonicalPacking enlarged
  have canonical_square : canonical.squares owner =
      corner.canonicalSquare (packing.squares owner) (size / factor) := by simp [canonical, enlarged]
  have canonical_anchor : ![(coordinate : ℝ), 9 / 10] ∈
      (canonical.squares owner).dilatedInteriorRegion factor := by
    rw [canonical_square, corner.canonicalSquare_mem_iff _ positive, identity,
      corner.originalPoint_baseline]
    exact anchor
  have score_eq : NagamochiResource.measure size ((canonical.squares owner).dilatedInteriorRegion factor) =
      NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor) :=
    corner.canonicalPacking_score enlarged positive owner
  have repaid := bottom_terminal_owner_score_repays canonical size_lower factor_gt_one factor_at_most
    identity.le owner coordinate_mem canonical_anchor (by rwa [canonical_square]) height_mem
  rw [score_eq] at repaid
  refine ⟨coordinate, coordinate_mem, owner, height, height_mem, terminal, origin_budget, ?_⟩
  rcases repaid with ⟨interior_mem, budget⟩ | ⟨endpoint, budget⟩
  · apply Or.inl
    obtain ⟨physicalCoordinate, physical_mem, physical_eq⟩ := corner.originalCoordinate_interior interior_mem
    refine ⟨interior_mem, ⟨physicalCoordinate, physical_mem, ?_⟩, budget⟩
    have point_eq : NagamochiResource.edgePoint size physicalCoordinate corner.edge =
        corner.edge.pointAt size (corner.originalCoordinate size coordinate) := by
      rw [← physical_eq]
      cases corner.edge <;> rfl
    rwa [point_eq]
  · apply Or.inr
    refine ⟨endpoint, ?_, budget⟩
    rw [← corner.originalPoint_baseline] at anchor
    rw [endpoint, Nat.cast_sub (by omega), Nat.cast_one,
      corner.originalPoint_opposite_anchor] at anchor
    exact anchor

theorem Nagamochi.right_terminal_owner_physical_marked_points
    {size : ℕ} {side factor height : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (corner : NagamochiResource.CornerPoint) (owner : Fin (size * size - 2))
    (corner_mem : NagamochiResource.cornerPoint size corner.oppositeEndpoint ∈
      (packing.squares owner).dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal
      (corner.canonicalSquare (packing.squares owner) (size / factor)) factor ((size - 1 : ℕ) : ℝ) height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    (∀ kind, NagamochiResource.cornerPoint size kind ∈
      (packing.squares owner).dilatedInteriorRegion factor ↔ kind = corner.oppositeEndpoint) ∧
    ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉
        (packing.squares owner).dilatedInteriorRegion factor := by
  have positive : 0 < factor := by linarith
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ positive]
    nlinarith
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  let enlarged := packing.enlarge side_bound
  let canonical := corner.canonicalPacking enlarged
  have square_eq : canonical.squares owner =
      corner.canonicalSquare (packing.squares owner) (size / factor) := by simp [canonical, enlarged]
  have canonical_corner : ![(size : ℝ) - 1, 9 / 10] ∈
      (canonical.squares owner).dilatedInteriorRegion factor := by
    rw [square_eq, corner.canonicalSquare_mem_iff _ positive, identity,
      corner.originalPoint_opposite_anchor]
    exact corner_mem
  have previous_missing : ![(size : ℝ) - 2, 9 / 10] ∉
      (canonical.squares owner).dilatedInteriorRegion factor := by
    intro previous_mem
    exact canonical.squareMinusTwo_not_adjacent_right_bottom_corner_and_edge size_lower
      factor_gt_one factor_at_most identity.le owner ⟨canonical_corner, previous_mem⟩
  rw [square_eq] at canonical_corner previous_missing
  exact canonical_right_terminal_physical_marked_points corner (packing.squares owner)
    (enlarged.fits owner) size_lower factor_gt_one factor_at_most canonical_corner previous_missing
    terminal height_mem

end SquarePackingArchive
