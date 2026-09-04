import SquarePackingArchive.NagamochiBoundaryAccounting

namespace SquarePackingArchive

open MeasureTheory Set

def Nagamochi.TerminalSupport
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (size : ℕ) (factor : ℝ) (sourceCorner : NagamochiResource.CornerPoint)
    (owner : Fin squareCount) : Prop :=
  (∃ coordinate ∈ Finset.Icc 2 (size - 2),
    NagamochiResource.edgePoint size coordinate sourceCorner.edge ∈
      (packing.squares owner).dilatedInteriorRegion factor) ∨
  (NagamochiResource.cornerPoint size sourceCorner.oppositeEndpoint ∈
      (packing.squares owner).dilatedInteriorRegion factor ∧
    (∃! kind, NagamochiResource.cornerPoint size kind ∈
      (packing.squares owner).dilatedInteriorRegion factor) ∧
    ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉
        (packing.squares owner).dilatedInteriorRegion factor)

noncomputable def Packing.terminalCapacity
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (size : ℕ) (factor : ℝ) (owner : Fin squareCount) : ℕ := by
  classical
  exact if ∃ coordinate ∈ Finset.Icc 2 (size - 2), ∃ kind,
    NagamochiResource.edgePoint size coordinate kind ∈
      (packing.squares owner).dilatedInteriorRegion factor then 2 else 1

theorem Packing.terminalCapacity_eq_two_of_edge_point
    {squareCount size coordinate : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    {owner : Fin squareCount} {kind : NagamochiResource.EdgePoint}
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (point_mem : NagamochiResource.edgePoint size coordinate kind ∈
      (packing.squares owner).dilatedInteriorRegion factor) :
    packing.terminalCapacity size factor owner = 2 := by
  classical
  exact if_pos ⟨coordinate, coordinate_mem, kind, point_mem⟩

theorem Packing.terminalCapacity_eq_one_of_no_edge_points
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    {owner : Fin squareCount}
    (no_edges : ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉
        (packing.squares owner).dilatedInteriorRegion factor) :
    packing.terminalCapacity size factor owner = 1 := by
  classical
  apply if_neg
  rintro ⟨coordinate, coordinate_mem, kind, point_mem⟩
  exact no_edges coordinate coordinate_mem kind point_mem

theorem Packing.terminalAssignment_fiber_card_le_capacity
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    {Origin : Type*} (origins : Finset Origin)
    (sourceCorner : origins → NagamochiResource.CornerPoint)
    (source_injective : Function.Injective sourceCorner)
    (assigned : origins → Fin squareCount)
    (support : ∀ origin, Nagamochi.TerminalSupport packing size factor
      (sourceCorner origin) (assigned origin))
    (target : Fin squareCount) :
    (Finset.univ.filter (fun origin : origins => assigned origin = target)).card ≤
      packing.terminalCapacity size factor target := by
  classical
  let fiber := Finset.univ.filter (fun origin : origins => assigned origin = target)
  change fiber.card ≤ packing.terminalCapacity size factor target
  let fiberCorner : fiber → NagamochiResource.CornerPoint := fun origin => sourceCorner origin.val
  have fiber_injective : Function.Injective fiberCorner := by
    intro first second equality
    apply Subtype.ext
    exact source_injective equality
  have fiber_support (origin : fiber) : Nagamochi.TerminalSupport packing size factor
      (fiberCorner origin) target := by
    have assigned_eq := (Finset.mem_filter.mp origin.property).2
    simpa only [assigned_eq] using support origin.val
  by_cases has_edge : ∃ coordinate ∈ Finset.Icc 2 (size - 2), ∃ kind,
      NagamochiResource.edgePoint size coordinate kind ∈ (packing.squares target).dilatedInteriorRegion factor
  · have capacity_eq : packing.terminalCapacity size factor target = 2 := if_pos has_edge
    rw [capacity_eq]
    apply NagamochiResource.card_le_two_of_same_square_edge_assignments fiber fiberCorner fiber_injective
      (packing.squares target) size_lower factor_positive factor_at_most
    intro origin
    rcases fiber_support origin with edge_support | ⟨_, _, no_edges⟩
    · exact edge_support
    · obtain ⟨coordinate, coordinate_mem, kind, point_mem⟩ := has_edge
      exact False.elim (no_edges coordinate coordinate_mem kind point_mem)
  · have capacity_eq : packing.terminalCapacity size factor target = 1 := if_neg has_edge
    rw [capacity_eq]
    by_cases empty : fiber = ∅
    · simp only [empty, Finset.card_empty, zero_le]
    obtain ⟨first, first_mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have first_support := fiber_support ⟨first, first_mem⟩
    have unique_corner : ∃! kind, NagamochiResource.cornerPoint size kind ∈
        (packing.squares target).dilatedInteriorRegion factor := by
      rcases first_support with ⟨coordinate, coordinate_mem, point_mem⟩ | ⟨_, unique, _⟩
      · exact False.elim (has_edge ⟨coordinate, coordinate_mem, _, point_mem⟩)
      · exact unique
    apply NagamochiResource.card_le_one_of_unique_terminal_corner fiber fiberCorner fiber_injective
      NagamochiResource.CornerPoint.oppositeEndpoint
      NagamochiResource.CornerPoint.oppositeEndpoint_injective unique_corner
    intro origin
    rcases fiber_support origin with ⟨coordinate, coordinate_mem, point_mem⟩ | ⟨point_mem, _, _⟩
    · exact False.elim (has_edge ⟨coordinate, coordinate_mem, _, point_mem⟩)
    · exact point_mem

end SquarePackingArchive
