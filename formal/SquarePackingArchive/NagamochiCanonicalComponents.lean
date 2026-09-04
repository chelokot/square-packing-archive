import SquarePackingArchive.NagamochiBoundaryOrientation
import SquarePackingArchive.NagamochiTerminalCornerOwnership
import SquarePackingArchive.NagamochiGlobalBadSquare

namespace SquarePackingArchive

open MeasureTheory Set

lemma Nagamochi.edgePoints_preimage_reflectX (size : ℕ) {region : Set Plane}
    (measurable : MeasurableSet region) :
    NagamochiResource.edgePoints size (Plane.reflectX size ⁻¹' region) =
      NagamochiResource.edgePoints size region := by
  rw [preimage_reflectX_eq,
    edgePoints_preimage_swap size
      ((measurable.preimage measurable_swapPlane).preimage (measurable_reflectYPlane size)),
    edgePoints_preimage_reflectY size (measurable.preimage measurable_swapPlane),
    edgePoints_preimage_swap size measurable]

lemma Nagamochi.marked_components_reflectX (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.cornerPoints size ((square.reflectX (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size ((square.reflectX (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have region_eq : (square.reflectX (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectX size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [identity] using square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectX size)
  rw [region_eq]
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  exact ⟨cornerPoints_preimage_reflectX size measurable, edgePoints_preimage_reflectX size measurable⟩

lemma NagamochiResource.EdgePoint.bottomSquare_marked_components
    (edge : NagamochiResource.EdgePoint) (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.cornerPoints size ((edge.bottomSquare square (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size ((edge.bottomSquare square (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by
  cases edge with
  | bottom => exact ⟨rfl, rfl⟩
  | top => exact (Nagamochi.original_components_reflectY square size factor_positive).2
  | left => exact (Nagamochi.original_components_swap square size factor_positive).2
  | right =>
      have reflected := Nagamochi.marked_components_reflectX square size factor_positive
      have swapped := (Nagamochi.original_components_swap (square.reflectX (size / factor)) size factor_positive).2
      exact ⟨swapped.1.trans reflected.1, swapped.2.trans reflected.2⟩

lemma NagamochiResource.CornerPoint.canonicalSquare_marked_components
    (corner : NagamochiResource.CornerPoint) (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.cornerPoints size ((corner.canonicalSquare square (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size ((corner.canonicalSquare square (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by
  have bottom := corner.edge.bottomSquare_marked_components square size factor_positive
  unfold canonicalSquare
  split
  · have reflected := Nagamochi.marked_components_reflectX
      (corner.edge.bottomSquare square (size / factor)) size factor_positive
    exact ⟨reflected.1.trans bottom.1, reflected.2.trans bottom.2⟩
  · exact bottom

lemma NagamochiResource.CornerPoint.canonicalPacking_marked_components
    (corner : NagamochiResource.CornerPoint) {squareCount size : ℕ} {factor : ℝ}
    (packing : Packing squareCount ((size : ℝ) / factor))
    (factor_positive : 0 < factor) (owner : Fin squareCount) :
    NagamochiResource.cornerPoints size ((corner.canonicalPacking packing).squares owner |>.dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size ((packing.squares owner).dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size ((corner.canonicalPacking packing).squares owner |>.dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size ((packing.squares owner).dilatedInteriorRegion factor) := by
  simpa using corner.canonicalSquare_marked_components (packing.squares owner) size factor_positive

lemma NagamochiResource.CornerPoint.canonicalSquare_fits
    (corner : NagamochiResource.CornerPoint) (square : PlacedSquare) {side : ℝ}
    (fits : square.Fits side) : (corner.canonicalSquare square side).Fits side := by
  cases corner <;>
    simpa [canonicalSquare, edge, reversed, EdgePoint.bottomSquare] using fits

theorem Nagamochi.canonical_right_terminal_physical_marked_points
    (corner : NagamochiResource.CornerPoint) (square : PlacedSquare) {size : ℕ} {factor height : ℝ}
    (fits : square.Fits (size / factor)) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈
      (corner.canonicalSquare square (size / factor)).dilatedInteriorRegion factor)
    (previous_point_missing : ![(size : ℝ) - 2, (9 / 10 : ℝ)] ∉
      (corner.canonicalSquare square (size / factor)).dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal (corner.canonicalSquare square (size / factor))
      factor ((size - 1 : ℕ) : ℝ) height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    (∀ kind, NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor ↔
      kind = corner.oppositeEndpoint) ∧
    ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉ square.dilatedInteriorRegion factor := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have canonical_fits := corner.canonicalSquare_fits square fits
  have canonical_corners := right_corner_terminal_has_exactly_one_marked_corner _ canonical_fits size_lower
    factor_gt_one factor_at_most identity.le corner_mem terminal height_mem
  have canonical_edges := right_corner_terminal_has_no_edge_points _ canonical_fits size_lower factor_gt_one
    factor_at_most identity.le corner_mem previous_point_missing terminal height_mem.2
  have canonical_masses := marked_masses_of_unique_corner_and_no_edges
    ((corner.canonicalSquare square (size / factor)).measurableSet_dilatedInteriorRegion positive.ne')
    ⟨.rightBottom, canonical_corners⟩ canonical_edges
  have components := corner.canonicalSquare_marked_components square size positive
  rw [components.1, components.2] at canonical_masses
  have physical_shape := unique_corner_and_no_edges_of_marked_masses
    (square.measurableSet_dilatedInteriorRegion positive.ne') canonical_masses.1 canonical_masses.2
  have opposite_mem : NagamochiResource.cornerPoint size corner.oppositeEndpoint ∈
      square.dilatedInteriorRegion factor := by
    have transported := (corner.canonicalSquare_mem_iff square positive _).1 corner_mem
    simpa [identity] using transported
  refine ⟨?_, physical_shape.2⟩
  obtain ⟨selected, _, unique⟩ := physical_shape.1
  have opposite_selected := unique corner.oppositeEndpoint opposite_mem
  intro kind
  constructor
  · intro point_mem
    exact (unique kind point_mem).trans opposite_selected.symm
  · rintro rfl
    exact opposite_mem

end SquarePackingArchive
