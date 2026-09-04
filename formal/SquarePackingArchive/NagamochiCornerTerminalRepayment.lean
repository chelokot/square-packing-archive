import SquarePackingArchive.NagamochiCornerTerminalResource
import SquarePackingArchive.NagamochiTerminalRepayment

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem boundaryChainTerminal_point_missing
    (square : PlacedSquare) {factor horizontal height : ℝ}
    (factor_positive : 0 < factor)
    (terminal : BoundaryChainTerminal square factor horizontal height) :
    ![horizontal, height] ∉ square.dilatedInteriorRegion factor := by
  intro point_mem
  have normalized_mem := (square.firstQuadrant_dilatedInteriorRegion_eq factor_positive).symm ▸ point_mem
  have bounds := inverse_bounds_of_dilatedInteriorRegion_mem square.firstQuadrant factor_positive normalized_mem
  rw [abs_lt, abs_lt] at bounds
  rcases terminal.2.2 with ⟨facet, _⟩ | ⟨facet, _⟩
  · exact (not_lt_of_ge facet) bounds.2.2
  · exact (not_lt_of_ge facet) bounds.1.2

theorem right_corner_terminal_score_of_upperX_facet
    (square : PlacedSquare) {size : ℕ} {factor height : ℝ}
    (fits : square.Fits (size / factor)) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(size : ℝ) - 2, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalX factor ⟨(size : ℝ) - 1, height⟩)
    (height_at_most : height ≤ 1)
    (leftmost_vertex_below : factor * square.center.y +
      factor * (square.frame.cosine - square.frame.sine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 + (1 - height) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have scaled_side : factor * ((size : ℝ) / factor) = size := by field_simp
  let canonical := (square.reflectX (size / factor)).rotateThreeQuarter
  have canonical_cosine : canonical.frame.cosine = square.frame.sine := by
    simp [canonical, PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_sine : canonical.frame.sine = square.frame.cosine := by
    simp [canonical, PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_center : canonical.center = ⟨(size : ℝ) / factor - square.center.x, square.center.y⟩ := rfl
  have canonical_fits : canonical.Fits (size / factor) := by
    intro point point_mem
    apply ((square.reflectX_fits_iff _).2 fits)
    simpa [canonical, PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf] using point_mem
  have region_eq : canonical.dilatedInteriorRegion factor =
      (square.reflectX (size / factor)).dilatedInteriorRegion factor :=
    (square.reflectX (size / factor)).rotateThreeQuarter_dilatedInteriorRegion_eq factor_positive
  have canonical_corner : ![(1 : ℝ), (9 / 10 : ℝ)] ∈ canonical.dilatedInteriorRegion factor := by
    rw [region_eq]
    simpa [scaled_side, Plane.reflectX] using
      (square.mem_reflectX_dilatedInteriorRegion_iff (coordinateSum := size / factor) factor_positive
        ![(size : ℝ) - 1, (9 / 10 : ℝ)]).2 corner_mem
  have canonical_next_missing : ![(2 : ℝ), (9 / 10 : ℝ)] ∉ canonical.dilatedInteriorRegion factor := by
    intro point_mem
    apply previous_point_missing
    apply (square.mem_reflectX_dilatedInteriorRegion_iff (coordinateSum := size / factor) factor_positive
      ![(size : ℝ) - 2, (9 / 10 : ℝ)]).1
    rw [region_eq] at point_mem
    simpa [Plane.reflectX, scaled_side] using point_mem
  have canonical_facet : factor / 2 ≤ canonical.dilatedLocalY factor ⟨1, height⟩ := by
    dsimp [PlacedSquare.dilatedLocalY]
    rw [canonical_cosine, canonical_sine, canonical_center]
    dsimp [PlacedSquare.dilatedLocalX] at upper_facet
    nlinarith
  have canonical_vertex : factor * canonical.center.y +
      factor * (canonical.frame.sine - canonical.frame.cosine) / 2 ≤ 9 / 10 := by
    rw [canonical_cosine, canonical_sine, canonical_center]
    exact leftmost_vertex_below
  have result := corner_terminal_score_repays_incoming_height canonical canonical_fits size_lower
    factor_gt_one factor_at_most (by rwa [canonical_cosine]) (by rwa [canonical_sine])
    canonical_corner canonical_next_missing canonical_facet height_at_most canonical_vertex
  have reflected_region_eq : (square.reflectX (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectX size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [scaled_side] using square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectX size)
  rw [region_eq, reflected_region_eq, resourceMeasure_preimage_reflectX size
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')] at result
  exact result

theorem right_corner_terminal_score_repays
    (square : PlacedSquare) {size : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (scaled_side_le : factor * side ≤ size)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(size : ℝ) - 2, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal square factor ((size - 1 : ℕ) : ℝ) height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    ENNReal.ofReal (1 + (1 - height) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have last_coordinate : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [last_coordinate] at terminal
  obtain ⟨cosine_positive, sine_positive, stopped⟩ := terminal
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_fits := (square.firstQuadrant_fits_iff _).2 fits
  rcases stopped with ⟨facet, _⟩ | ⟨facet, low_vertex⟩
  · have rightmost := rightmost_vertex_beyond_successor_of_upper_facet square.firstQuadrant normalized_fits
      factor_gt_one cosine_positive.le sine_positive facet height_mem.2
    have right_bound := (square.firstQuadrant.center_bounds normalized_fits).2.1
    simp only [frameExtent, abs_of_nonneg cosine_positive.le, abs_of_nonneg sine_positive.le] at right_bound
    have scaled_right := mul_le_mul_of_nonneg_left right_bound factor_positive.le
    exfalso
    nlinarith
  · have side_le : side ≤ (size : ℝ) / factor := by
      apply (le_div_iff₀ factor_positive).mpr
      simpa only [mul_comm] using scaled_side_le
    have enlarged_fits : square.firstQuadrant.Fits (size / factor) := by
      intro point point_mem
      have bounds := normalized_fits point_mem
      exact ⟨bounds.1, bounds.2.1.trans side_le, bounds.2.2.1, bounds.2.2.2.trans side_le⟩
    have normalized_low : factor * square.firstQuadrant.center.y +
        factor * (square.firstQuadrant.frame.cosine - square.firstQuadrant.frame.sine) / 2 ≤ 9 / 10 := by
      simpa using low_vertex.le
    have result := right_corner_terminal_score_of_upperX_facet square.firstQuadrant enlarged_fits size_lower
      factor_gt_one factor_at_most cosine_positive sine_positive (region_eq.symm ▸ corner_mem)
      (region_eq.symm ▸ previous_point_missing) facet height_mem.2 normalized_low
    rwa [region_eq] at result

theorem left_corner_terminal_score_repays
    (square : PlacedSquare) {size : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (corner_mem : ![(1 : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(2 : ℝ), (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal square factor 1 height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    ENNReal.ofReal (1 + (1 - height) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  obtain ⟨cosine_positive, sine_positive, stopped⟩ := terminal
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_fits := (square.firstQuadrant_fits_iff _).2 fits
  rcases stopped with ⟨facet, low_vertex⟩ | ⟨facet, _⟩
  · have normalized_low : factor * square.firstQuadrant.center.y +
        factor * (square.firstQuadrant.frame.sine - square.firstQuadrant.frame.cosine) / 2 ≤ 9 / 10 := by
      simpa using low_vertex.le
    have result := corner_terminal_score_repays_incoming_height square.firstQuadrant normalized_fits size_lower
      factor_gt_one factor_at_most cosine_positive sine_positive (region_eq.symm ▸ corner_mem)
      (region_eq.symm ▸ next_point_missing) facet height_mem.2 normalized_low
    rwa [region_eq] at result
  · have impossible_facet := unit_corner_localX_lt_half_factor square.firstQuadrant normalized_fits
      factor_gt_one cosine_positive.le sine_positive.le
    dsimp [PlacedSquare.dilatedLocalX] at facet impossible_facet
    exfalso
    nlinarith [height_mem.2]

end SquarePackingArchive.Nagamochi
