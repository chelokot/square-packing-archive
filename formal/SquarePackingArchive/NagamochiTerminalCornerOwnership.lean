import SquarePackingArchive.NagamochiCornerOwnership
import SquarePackingArchive.NagamochiCornerTerminalRepayment

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma corner_kind_near_right_bottom_corner
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    {kind : NagamochiResource.CornerPoint}
    (point_mem : NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor) :
    kind = .rightBottom ∨ kind = .bottomRight := by
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_lower
  have distance := dilated_square_coordinate_distance_lt_two square factor_positive factor_at_most
    point_mem corner_mem
  cases kind <;> norm_num [NagamochiResource.cornerPoint, abs_lt] at distance ⊢ <;> linarith

theorem right_corner_has_exactly_one_marked_corner_of_missing_segment
    (square : PlacedSquare) {size : ℕ} {factor height : ℝ}
    (fits : square.Fits (size / factor)) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1)
    (incoming_missing : ![(size : ℝ) - 1, height] ∉ square.dilatedInteriorRegion factor) :
    ∀ kind, NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor ↔
      kind = .rightBottom := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have partner_missing : NagamochiResource.cornerPoint size .bottomRight ∉
      square.dilatedInteriorRegion factor := by
    intro partner_mem
    have reflected_corner := (square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) positive _).2 corner_mem
    have reflected_partner := (square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) positive _).2 partner_mem
    have segments := corner_segments_mem_of_adjacent_marked_points (square.reflectX (size / factor))
      ((square.reflectX_fits_iff _).2 fits) factor_gt_one
      (by simpa [Plane.reflectX, identity] using reflected_corner)
      (by simpa [Plane.reflectX, identity, NagamochiResource.cornerPoint] using reflected_partner)
    apply incoming_missing
    apply (square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) positive ![(size : ℝ) - 1, height]).1
    simpa [Plane.reflectX, identity] using (segments height height_mem).1
  intro kind
  constructor
  · intro point_mem
    rcases corner_kind_near_right_bottom_corner square size_lower positive factor_at_most
      corner_mem point_mem with own | partner
    · exact own
    · subst kind
      exact False.elim (partner_missing point_mem)
  · rintro rfl
    simpa [NagamochiResource.cornerPoint] using corner_mem

theorem right_corner_terminal_has_exactly_one_marked_corner
    (square : PlacedSquare) {size : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (scaled_side_le : factor * side ≤ size)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal square factor ((size - 1 : ℕ) : ℝ) height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    ∀ kind, NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor ↔
      kind = .rightBottom := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ positive]
    nlinarith
  have enlarged_fits : square.Fits (size / factor) := by
    intro point point_mem
    have bounds := fits point_mem
    exact ⟨bounds.1, bounds.2.1.trans side_bound, bounds.2.2.1, bounds.2.2.2.trans side_bound⟩
  have incoming_missing := boundaryChainTerminal_point_missing square positive terminal
  have coordinate_eq : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [coordinate_eq] at incoming_missing
  exact right_corner_has_exactly_one_marked_corner_of_missing_segment square enlarged_fits size_lower
    factor_gt_one factor_at_most corner_mem height_mem incoming_missing

lemma right_corner_terminal_points_above_are_left
    (square : PlacedSquare) {size : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (scaled_side_le : factor * side ≤ size)
    (terminal : BoundaryChainTerminal square factor ((size - 1 : ℕ) : ℝ) height)
    (height_at_most : height ≤ 1) :
    ∀ point ∈ square.dilatedInteriorRegion factor, 1 ≤ point 1 → point 0 < (size : ℝ) - 1 := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have coordinate_eq : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [coordinate_eq] at terminal
  obtain ⟨cosine_positive, sine_positive, stopped⟩ := terminal
  have normalized_fits := (square.firstQuadrant_fits_iff _).2 fits
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq positive
  rcases stopped with ⟨facet, _⟩ | ⟨facet, _⟩
  · have rightmost := rightmost_vertex_beyond_successor_of_upper_facet square.firstQuadrant normalized_fits
      factor_gt_one cosine_positive.le sine_positive facet height_at_most
    have right_bound := (square.firstQuadrant.center_bounds normalized_fits).2.1
    simp only [frameExtent, abs_of_pos cosine_positive, abs_of_pos sine_positive] at right_bound
    have scaled_right := mul_le_mul_of_nonneg_left right_bound positive.le
    exfalso
    nlinarith
  · intro point point_mem point_above
    have normalized_mem := region_eq.symm ▸ point_mem
    have bound := (abs_lt.mp (inverse_bounds_of_dilatedInteriorRegion_mem square.firstQuadrant
      positive normalized_mem).1).2
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at facet bound
    have vertical_increase := mul_nonneg sine_positive.le (show 0 ≤ point 1 - height by linarith)
    nlinarith

theorem right_corner_terminal_has_no_edge_points
    (square : PlacedSquare) {size : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (scaled_side_le : factor * side ≤ size)
    (corner_mem : ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(size : ℝ) - 2, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal square factor ((size - 1 : ℕ) : ℝ) height)
    (height_at_most : height ≤ 1) :
    ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉ square.dilatedInteriorRegion factor := by
  intro coordinate coordinate_mem kind point_mem
  have coordinate_lower : 2 ≤ coordinate := (Finset.mem_Icc.mp coordinate_mem).1
  have coordinate_upper : coordinate ≤ size - 2 := (Finset.mem_Icc.mp coordinate_mem).2
  have coordinate_real_lower : (2 : ℝ) ≤ coordinate := by exact_mod_cast coordinate_lower
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_lower
  have distance := dilated_square_coordinate_distance_lt_two square (zero_lt_one.trans factor_gt_one)
    factor_at_most point_mem corner_mem
  cases kind with
  | bottom =>
      by_cases is_previous : coordinate = size - 2
      · apply previous_point_missing
        simpa [NagamochiResource.edgePoint, is_previous, Nat.cast_sub (by omega : 2 ≤ size)] using point_mem
      · have farther : coordinate ≤ size - 3 := by omega
        have farther_real : (coordinate : ℝ) ≤ (size : ℝ) - 3 := by
          have cast_bound : (coordinate : ℝ) ≤ ((size - 3 : ℕ) : ℝ) := by exact_mod_cast farther
          simpa [Nat.cast_sub (by omega : 3 ≤ size)] using cast_bound
        norm_num [NagamochiResource.edgePoint, abs_lt] at distance
        linarith
  | top =>
      norm_num [NagamochiResource.edgePoint, abs_lt] at distance
      linarith
  | left =>
      norm_num [NagamochiResource.edgePoint, abs_lt] at distance
      linarith
  | right =>
      have left_bound := right_corner_terminal_points_above_are_left square fits size_lower
        factor_gt_one scaled_side_le terminal height_at_most _ point_mem
        (by simpa [NagamochiResource.edgePoint] using (show (1 : ℝ) ≤ coordinate by linarith))
      norm_num [NagamochiResource.edgePoint] at left_bound

end SquarePackingArchive.Nagamochi
