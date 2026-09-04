import SquarePackingArchive.NagamochiBoundaryTransfer
import SquarePackingArchive.NagamochiAssignmentCapacity
import SquarePackingArchive.NagamochiCompensation

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem bad_corner_owner_has_capacity_transfer
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (corner : NagamochiResource.CornerPoint) (origin : Fin (size * size - 2))
    (corner_mem : NagamochiResource.cornerPoint size corner ∈
      (packing.squares origin).dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) ≤ 1) :
    ∃ owner credit, 0 ≤ credit ∧
      1 < packing.originalScore size factor origin + credit ∧
      TerminalSupport packing size factor corner owner ∧
      1 + (packing.terminalCapacity size factor owner : ℝ) * credit <
        packing.originalScore size factor owner := by
  obtain ⟨coordinate, coordinate_mem, owner, height, height_mem, terminal, origin_budget, repaid⟩ :=
    bad_corner_owner_has_repaid_terminal packing size_lower factor_gt_one factor_at_most scaled_side_le
      corner origin corner_mem bad
  have credit_nonnegative : 0 ≤ (1 - height) / 2 := by linarith [height_mem.2]
  have origin_real := packing.originalScore_gt_of_measure_bound (by omega) origin
    (by linarith [height_mem.1] : 0 ≤ (1 + height) / 2) origin_budget
  refine ⟨owner, (1 - height) / 2, credit_nonnegative, by linarith, ?_, ?_⟩
  · rcases repaid with ⟨_, edge_support, _⟩ | ⟨endpoint, corner_support, _⟩
    · exact Or.inl edge_support
    · obtain ⟨unique_corner, no_edges⟩ := right_terminal_owner_physical_marked_points packing size_lower
        factor_gt_one factor_at_most scaled_side_le corner owner corner_support
        (by simpa [endpoint] using terminal) height_mem
      refine Or.inr ⟨corner_support, ?_, no_edges⟩
      exact ⟨corner.oppositeEndpoint, corner_support, fun kind contained => (unique_corner kind).1 contained⟩
  · rcases repaid with ⟨_, ⟨physicalCoordinate, physical_mem, physical_point⟩, owner_budget⟩ |
        ⟨endpoint, corner_support, owner_budget⟩
    · rw [packing.terminalCapacity_eq_two_of_edge_point physical_mem physical_point]
      exact packing.originalScore_gt_of_measure_bound (by omega) owner
        (by norm_num; linarith) owner_budget
    · obtain ⟨_, no_edges⟩ := right_terminal_owner_physical_marked_points packing size_lower
        factor_gt_one factor_at_most scaled_side_le corner owner corner_support
        (by simpa [endpoint] using terminal) height_mem
      rw [packing.terminalCapacity_eq_one_of_no_edge_points no_edges]
      norm_num only [Nat.cast_one, one_mul]
      exact packing.originalScore_gt_of_measure_bound (by omega) owner (by linarith) owner_budget

end SquarePackingArchive.Nagamochi
