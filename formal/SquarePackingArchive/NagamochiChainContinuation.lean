import SquarePackingArchive.NagamochiChainStep
import SquarePackingArchive.NagamochiBoundaryChain

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem chain_step_left_of_upper_facet_and_high_leftmost_vertex
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (leftmost_vertex_above_grid : 9 / 10 ≤ factor * square.center.y +
      factor * (square.frame.cosine - square.frame.sine) / 2) :
    ∃ height ∈ Icc (9 / 10 : ℝ) exitHeight,
      ![horizontal - 1, height] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := by linarith
  let canonical := (square.reflectX side).firstQuadrant
  have canonical_eq : canonical = (square.reflectX side).rotateThreeQuarter := by
    dsimp [canonical, PlacedSquare.firstQuadrant]
    rw [if_neg (show ¬0 ≤ (square.reflectX side).frame.cosine by
      change ¬0 ≤ -square.frame.cosine
      linarith)]
    rw [if_pos (show 0 ≤ (square.reflectX side).frame.sine from sine_positive.le)]
  have canonical_cosine : canonical.frame.cosine = square.frame.sine := by
    rw [canonical_eq]
    simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_sine : canonical.frame.sine = square.frame.cosine := by
    rw [canonical_eq]
    simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_center : canonical.center = ⟨side - square.center.x, square.center.y⟩ := by
    simp [canonical, PlacedSquare.reflectX, Point.reflectX]
  have canonical_fits : canonical.Fits side := by
    simpa [canonical] using fits
  have region_eq : canonical.dilatedInteriorRegion factor =
      (square.reflectX side).dilatedInteriorRegion factor :=
    (square.reflectX side).firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have canonical_anchor : ![factor * side - horizontal, (9 / 10 : ℝ)] ∈
      canonical.dilatedInteriorRegion factor := by
    rw [region_eq]
    exact (square.mem_reflectX_dilatedInteriorRegion_iff factor_positive
      ![horizontal, (9 / 10 : ℝ)]).2 grid_point_mem
  have canonical_facet : factor / 2 ≤ canonical.dilatedLocalY factor
      ⟨factor * side - horizontal, exitHeight⟩ := by
    dsimp [PlacedSquare.dilatedLocalY]
    rw [canonical_cosine, canonical_sine, canonical_center]
    dsimp [PlacedSquare.dilatedLocalX] at upper_facet
    nlinarith
  have canonical_vertex : 9 / 10 ≤ factor * canonical.center.y +
      factor * (canonical.frame.sine - canonical.frame.cosine) / 2 := by
    rw [canonical_cosine, canonical_sine, canonical_center]
    exact leftmost_vertex_above_grid
  obtain ⟨height, height_mem, crossing⟩ := chain_step_of_upper_facet_and_high_rightmost_vertex
    canonical canonical_fits factor_gt_one (by rwa [canonical_cosine]) (by rwa [canonical_sine])
    canonical_anchor canonical_facet exit_at_most canonical_vertex
  refine ⟨height, height_mem, ?_⟩
  apply (square.mem_reflectX_dilatedInteriorRegion_iff factor_positive
    ![horizontal - 1, height]).1
  rw [region_eq] at crossing
  convert crossing using 1
  simp [Plane.reflectX]
  ring

theorem chain_owner_continues_or_stops
    (square : PlacedSquare) {previousRegion : Set Plane} {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (previous_convex : Convex ℝ previousRegion)
    (regions_disjoint : Disjoint previousRegion (square.dilatedInteriorRegion factor))
    (previous_anchor : ![horizontal - 1, (9 / 10 : ℝ)] ∈ previousRegion)
    (previous_crossing : ![horizontal, exitHeight] ∈ previousRegion)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (exit_height_mem : exitHeight ∈ Icc (9 / 10 : ℝ) 1) :
    (∃ height ∈ Icc (9 / 10 : ℝ) exitHeight,
      ![horizontal + 1, height] ∈ square.dilatedInteriorRegion factor) ∨
    (factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩ ∧
      factor * square.center.y + factor * (square.frame.sine - square.frame.cosine) / 2 < 9 / 10) ∨
    (factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, exitHeight⟩ ∧
      factor * square.center.y + factor * (square.frame.cosine - square.frame.sine) / 2 < 9 / 10) := by
  have factor_positive : 0 < factor := by linarith
  by_cases upper_vertical : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩
  · by_cases low_vertex : factor * square.center.y +
        factor * (square.frame.sine - square.frame.cosine) / 2 < 9 / 10
    · exact Or.inr (Or.inl ⟨upper_vertical, low_vertex⟩)
    · exact Or.inl (chain_step_of_upper_facet_and_high_rightmost_vertex square fits factor_gt_one
        cosine_positive sine_positive grid_point_mem upper_vertical exit_height_mem.2 (le_of_not_gt low_vertex))
  · have upper_horizontal : factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, exitHeight⟩ := by
      by_contra! upper_horizontal
      have anchor_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive grid_point_mem
      rw [abs_lt, abs_lt] at anchor_bounds
      have crossing_mem : ![horizontal, exitHeight] ∈ square.dilatedInteriorRegion factor := by
        apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
        · rw [abs_lt]
          refine ⟨?_, upper_horizontal⟩
          have lower_at_grid := anchor_bounds.1.1
          dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at lower_at_grid ⊢
          nlinarith [exit_height_mem.1]
        · rw [abs_lt]
          refine ⟨?_, lt_of_not_ge upper_vertical⟩
          have lower_at_grid := anchor_bounds.2.1
          dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at lower_at_grid ⊢
          nlinarith [exit_height_mem.1]
      exact Set.disjoint_left.mp regions_disjoint previous_crossing crossing_mem
    by_cases low_vertex : factor * square.center.y +
        factor * (square.frame.cosine - square.frame.sine) / 2 < 9 / 10
    · exact Or.inr (Or.inr ⟨upper_horizontal, low_vertex⟩)
    · obtain ⟨height, height_mem, crossing⟩ := chain_step_left_of_upper_facet_and_high_leftmost_vertex
        square fits factor_gt_one cosine_positive sine_positive grid_point_mem upper_horizontal
        exit_height_mem.2 (le_of_not_gt low_vertex)
      exact False.elim (disjoint_convex_regions_cannot_cross_above_baseline previous_convex
        (square.convex_dilatedInteriorRegion factor) regions_disjoint previous_anchor previous_crossing
        grid_point_mem crossing exit_height_mem.1 height_mem.1)

end SquarePackingArchive.Nagamochi
