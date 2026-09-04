import SquarePackingArchive.NagamochiBoundaryPropagation
import SquarePackingArchive.NagamochiChainStep

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem bottom_bad_square_score_gt_exit_budget_positive_frame
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ENNReal.ofReal ((1 + bottomLeftExitHeight square factor) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners square
    fits size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  have inner_corner_missing := bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below first_missing second_missing corner_mem bad
  have bottom_budget := area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits (by omega) factor_gt_one factor_at_most inside_container center_horizontal
    center_below first_missing second_missing
  have left_chord := bottom_left_exit_chord (size := size) square fits (by omega) factor_gt_one
    cosine_positive sine_positive corner_mem inner_corner_missing
  have left_bound := NagamochiResource.boundaryLine_lower_bound_of_chord measurable left_chord
  have weighted_left := mul_le_mul (a := (1 / 2 : ENNReal)) le_rfl left_bound bot_le bot_le
  have pair_subset : ({NagamochiResource.BoundarySide.bottom, .left} : Finset _) ⊆
      NagamochiResource.boundarySides := by
    intro boundary _
    exact NagamochiResource.mem_boundarySides boundary
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := square.dilatedInteriorRegion factor) pair_subset
  rw [Finset.sum_pair (by decide : NagamochiResource.BoundarySide.bottom ≠ .left), mul_add] at pair_bound
  have continuous_bound : (NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor)) +
        (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) := by
    rw [add_assoc]
    exact add_le_add le_rfl ((add_le_add le_rfl weighted_left).trans pair_bound)
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem (size := size) .leftBottom measurable corner_mem
  have first_strict := (ENNReal.add_lt_add_iff_right (by finiteness :
    (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) ≠ ⊤)).2 bottom_budget
  have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (9 / 20 : ENNReal) ≠ ⊤)).2 first_strict
  have exit_bounds := bottom_left_exit_height_bounds square fits factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have length_nonnegative : 0 ≤ bottomLeftExitHeight square factor - 9 / 10 := by linarith [exit_bounds.1]
  have budget_nonnegative : 0 ≤ (1 + bottomLeftExitHeight square factor) / 2 := by linarith [exit_bounds.1]
  have budget_identity : (1 / 2 : ENNReal) +
      (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) + 9 / 20 =
      ENNReal.ofReal ((1 + bottomLeftExitHeight square factor) / 2) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal length_nonnegative,
      ENNReal.toReal_ofReal budget_nonnegative]
    norm_num
    ring
  rw [budget_identity] at strict
  exact (strict.trans_le (add_le_add continuous_bound corner_bound)).trans_le
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size _)

theorem bottom_bad_square_rightmost_vertex_above_grid
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    9 / 10 ≤ factor * square.center.y + factor * (square.frame.sine - square.frame.cosine) / 2 := by
  by_contra! vertex_below
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners square
    fits size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  have inner_corner_missing := bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below first_missing second_missing corner_mem bad
  have no_edge_points := bottom_bad_square_has_no_edge_points square fits (by omega) factor_gt_one
    factor_at_most inside_container center_horizontal center_below first_missing second_missing bad
  have next_point_missing : ![(2 : ℝ), 9 / 10] ∉ square.dilatedInteriorRegion factor := by
    exact no_edge_points 2 (by simp only [Finset.mem_Icc]; omega) .bottom
  have vertex_right := rightmost_vertex_beyond_two_of_bottom_corner_and_missing_inner_corner square
    fits factor_gt_one cosine_positive.le sine_positive corner_mem inner_corner_missing
  let vertex := square.dilatedPoint factor (factor / 2) (-(factor / 2))
  have vertex_mem : vertex.toPlane ∈ closure (square.dilatedInteriorRegion factor) :=
    square.dilatedPoint_mem_closure factor_positive
      (by rw [abs_of_nonneg (by positivity)])
      (by rw [abs_neg, abs_of_nonneg (by positivity)])
  have vertex_x : 2 < vertex.x := by
    dsimp [vertex, PlacedSquare.dilatedPoint, Frame.place]
    linarith
  have vertex_y : vertex.y < 9 / 10 := by
    dsimp [vertex, PlacedSquare.dilatedPoint, Frame.place]
    linarith
  let ratio := 1 / (vertex.x - 1)
  have ratio_positive : 0 < ratio := div_pos (by norm_num) (by linarith)
  have ratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_one (by linarith : 0 < vertex.x - 1)]
    linarith
  let lowerHeight := (1 - ratio) * (9 / 10) + ratio * vertex.y
  have lower_below : lowerHeight < 9 / 10 := by
    dsimp [lowerHeight]
    nlinarith [mul_pos ratio_positive (sub_pos.mpr vertex_y)]
  have lower_mem : ![(2 : ℝ), lowerHeight] ∈ square.dilatedInteriorRegion factor := by
    have segment_mem := lineMap_mem_openSegment ℝ ![(1 : ℝ), 9 / 10] vertex.toPlane
      ⟨ratio_positive, ratio_lt_one⟩
    have open_region := square.isOpen_dilatedInteriorRegion factor_positive.ne'
    have point_mem := (square.convex_dilatedInteriorRegion factor).openSegment_interior_closure_subset_interior
      (by simpa [open_region.interior_eq] using corner_mem) vertex_mem segment_mem
    rw [open_region.interior_eq] at point_mem
    convert point_mem using 1
    funext coordinate
    fin_cases coordinate
    · simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [Point.toPlane]
      have ratio_cancel : ratio * (vertex.x - 1) = 1 := by
        dsimp [ratio]
        exact div_mul_cancel₀ _ (by linarith)
      nlinarith
    · simp [AffineMap.lineMap_apply_module, Point.toPlane, lowerHeight]
  obtain ⟨height, height_mem, point_mem⟩ := bottom_bad_square_crosses_next_boundary_band_positive_frame
    square fits size_at_least_four factor_gt_one factor_at_most cosine_positive sine_positive
    inside_container center_horizontal center_below corner_mem bad
  apply next_point_missing
  by_cases height_eq : height = 9 / 10
  · simpa only [height_eq] using point_mem
  · have height_gt : 9 / 10 < height := lt_of_le_of_ne height_mem.1 (Ne.symm height_eq)
    exact vertical_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
      (lower_below.trans height_gt) lower_mem point_mem (9 / 10) ⟨lower_below, height_gt⟩

theorem bottom_bad_square_starts_weighted_chain_positive_frame
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ∃ height ∈ Icc (9 / 10 : ℝ) 1,
      ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor ∧
      ENNReal.ofReal ((1 + height) / 2) < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have vertex_above := bottom_bad_square_rightmost_vertex_above_grid square fits size_at_least_four
    factor_gt_one factor_at_most cosine_positive sine_positive inside_container center_horizontal center_below corner_mem bad
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners square
    fits size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  have inner_corner_missing := bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below first_missing second_missing corner_mem bad
  have exit_bounds := bottom_left_exit_height_bounds square fits factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨1, bottomLeftExitHeight square factor⟩ := by
    apply le_of_eq
    dsimp [PlacedSquare.dilatedLocalY, bottomLeftExitHeight]
    field_simp
    ring
  obtain ⟨height, height_mem, point_mem⟩ := chain_step_of_upper_facet_and_high_rightmost_vertex square
    fits factor_gt_one cosine_positive sine_positive corner_mem upper_facet exit_bounds.2 vertex_above
  have score_bound := bottom_bad_square_score_gt_exit_budget_positive_frame square fits size_at_least_four
    factor_gt_one factor_at_most cosine_positive sine_positive inside_container center_horizontal center_below corner_mem bad
  refine ⟨height, ⟨height_mem.1, height_mem.2.trans exit_bounds.2⟩, ?_, ?_⟩
  · norm_num at point_mem
    exact point_mem
  · exact (ENNReal.ofReal_le_ofReal (by linarith [height_mem.2])).trans_lt score_bound

lemma unit_corner_mem_of_axis_frame
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (axis_frame : square.frame.cosine = 0 ∨ square.frame.sine = 0) :
    ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have corner_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive corner_mem
  rw [abs_lt, abs_lt] at corner_bounds
  have horizontal_upper := unit_corner_localX_lt_half_factor square fits factor_gt_one
    cosine_nonnegative sine_nonnegative
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    refine ⟨?_, horizontal_upper⟩
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at corner_bounds ⊢
    linarith [corner_bounds.1.1]
  · rw [abs_lt]
    constructor
    · dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at corner_bounds ⊢
      linarith [corner_bounds.2.1]
    · rcases axis_frame with cosine_zero | sine_zero
      · simpa [PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_zero] using corner_bounds.2.2
      · have cosine_one : square.frame.cosine = 1 := by nlinarith [square.frame.unit]
        have center_bound := (square.center_bounds fits).2.2.1
        norm_num [frameExtent, cosine_one, sine_zero] at center_bound
        have scaled_center := mul_le_mul_of_nonneg_left center_bound factor_positive.le
        simp [PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_one, sine_zero]
        nlinarith

theorem positive_frame_of_bad_bottom_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    0 < square.frame.cosine ∧ 0 < square.frame.sine := by
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners square
    fits size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  have inner_corner_missing := bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below first_missing second_missing corner_mem bad
  have not_axis : ¬ (square.frame.cosine = 0 ∨ square.frame.sine = 0) := by
    intro axis_frame
    exact inner_corner_missing (unit_corner_mem_of_axis_frame square fits factor_gt_one
      cosine_nonnegative sine_nonnegative corner_mem axis_frame)
  constructor
  · exact lt_of_le_of_ne cosine_nonnegative (fun equality => not_axis (Or.inl equality.symm))
  · exact lt_of_le_of_ne sine_nonnegative (fun equality => not_axis (Or.inr equality.symm))

theorem bottom_bad_square_starts_weighted_chain
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ∃ height ∈ Icc (9 / 10 : ℝ) 1,
      ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor ∧
      ENNReal.ofReal ((1 + height) / 2) < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq (zero_lt_one.trans factor_gt_one)
  have normalized_fits := (square.firstQuadrant_fits_iff side).2 fits
  have normalized_horizontal : factor * square.firstQuadrant.center.x ∈ Icc 1 ((size : ℝ) - 1) := by
    simpa using center_horizontal
  have normalized_below : factor * square.firstQuadrant.center.y ≤ 1 := by simpa using center_below
  have positive := positive_frame_of_bad_bottom_corner square.firstQuadrant normalized_fits
    size_at_least_four factor_gt_one factor_at_most square.firstQuadrant_cosine_nonnegative
    square.firstQuadrant_sine_nonnegative (region_eq.symm ▸ inside_container) normalized_horizontal
    normalized_below (region_eq.symm ▸ corner_mem) (region_eq.symm ▸ bad)
  have result := bottom_bad_square_starts_weighted_chain_positive_frame square.firstQuadrant
    normalized_fits size_at_least_four factor_gt_one factor_at_most positive.1 positive.2
    (region_eq.symm ▸ inside_container) normalized_horizontal normalized_below
    (region_eq.symm ▸ corner_mem) (region_eq.symm ▸ bad)
  rwa [region_eq] at result

end SquarePackingArchive.Nagamochi
