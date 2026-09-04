import SquarePackingArchive.NagamochiBadSquare
import SquarePackingArchive.NagamochiChainPotential

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma upper_facet_vertex_below_exit
    (square : PlacedSquare) {factor horizontal baseline exitHeight : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (anchor_mem : ![horizontal, baseline] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩) :
    baseline < exitHeight ∧
      factor * square.center.y + factor * (square.frame.cosine - square.frame.sine) / 2 < exitHeight := by
  have anchor_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive anchor_mem
  rw [abs_lt, abs_lt] at anchor_bounds
  have exit_above : baseline < exitHeight := by
    have upper_at_anchor := anchor_bounds.2.2
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_at_anchor upper_facet
    nlinarith
  refine ⟨exit_above, ?_⟩
  have horizontal_lower : -(factor / 2) < square.dilatedLocalX factor ⟨horizontal, exitHeight⟩ := by
    have anchor_lower := anchor_bounds.1.1
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at anchor_lower ⊢
    nlinarith
  have horizontal_scaled := mul_lt_mul_of_pos_left horizontal_lower sine_positive
  have vertical_scaled := mul_le_mul_of_nonneg_left upper_facet cosine_positive.le
  dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY] at horizontal_scaled vertical_scaled
  nlinarith [square.frame.unit,
    congrArg (fun value : ℝ => (exitHeight - factor * square.center.y) * value) square.frame.unit]

theorem terminal_height_bound_of_fits
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    1 < (square.frame.cosine + square.frame.sine) /
      (1 + square.frame.cosine + square.frame.sine) + exitHeight / 2 := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have point_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive grid_point_mem
  rw [abs_lt, abs_lt] at point_bounds
  have bottom_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_pos cosine_positive, abs_of_pos sine_positive] at bottom_bound
  have scaled_bottom := mul_le_mul_of_nonneg_left bottom_bound factor_positive.le
  have sine_at_most : square.frame.sine ≤ 9 / 10 := by
    nlinarith [mul_pos (sub_pos.mpr factor_gt_one) sine_positive]
  have exit_above_grid : 9 / 10 < exitHeight := by
    have upper_at_grid := point_bounds.2.2
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_at_grid upper_facet
    nlinarith
  have horizontal_lower := mul_lt_mul_of_pos_left point_bounds.1.1 sine_positive
  have vertical_upper := mul_le_mul_of_nonneg_left upper_facet cosine_positive.le
  have cosine_factor := mul_lt_mul_of_pos_right factor_gt_one cosine_positive
  have lower_local_bound : square.frame.cosine - (9 / 10) * square.frame.sine ^ 2 <
      square.frame.cosine ^ 2 * exitHeight := by
    dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint]
      at horizontal_lower vertical_upper
    nlinarith [square.frame.unit,
      congrArg (fun value : ℝ => factor * square.center.y * value) square.frame.unit]
  exact terminal_height_potential_repaid cosine_positive sine_positive square.frame.unit
    sine_at_most exit_above_grid lower_local_bound

lemma upperCap_subset_inner_of_upper_facet
    (square : PlacedSquare) {size : ℕ} {factor horizontal exitHeight : ℝ}
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (horizontal_lower : 1 ≤ horizontal) (horizontal_upper : horizontal + 2 ≤ (size : ℝ) - 1)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1) :
    square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1} ⊆
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
  rintro point ⟨point_mem, point_above⟩
  change 1 ≤ point 1 at point_above
  have point_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive point_mem
  have upper_at_point := (abs_lt.mp point_bounds.2).2
  have point_right : horizontal < point 0 := by
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_at_point upper_facet
    have vertical_increase := mul_nonneg cosine_positive.le
      (show 0 ≤ point 1 - exitHeight by linarith)
    nlinarith
  have distances := dilated_square_coordinate_distance_lt_two square factor_positive factor_at_most
    point_mem grid_point_mem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at distances
  rw [abs_lt, abs_lt] at distances
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_lower
  constructor
  · intro coordinate
    fin_cases coordinate <;> dsimp <;> linarith
  · intro coordinate
    fin_cases coordinate <;> dsimp <;> linarith

theorem terminal_upperCap_budget_of_fits
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 - exitHeight / 2) <
      volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) +
        (1 / 2 : ENNReal) * volume {coordinate : ℝ |
          ![coordinate, 1] ∈ square.dilatedInteriorRegion factor} := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have height_bound := terminal_height_bound_of_fits square fits factor_gt_one cosine_positive
    sine_positive grid_point_mem upper_facet vertex_below_grid
  have other_vertex := (upper_facet_vertex_below_exit square factor_positive cosine_positive
    sine_positive grid_point_mem upper_facet).2
  have cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine := by
    dsimp [horizontalUpperCapHeight]
    linarith
  have cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine := by
    dsimp [horizontalUpperCapHeight]
    linarith
  have strict_scalar : 1 - exitHeight / 2 < (square.frame.cosine + square.frame.sine) /
      (1 + square.frame.cosine + square.frame.sine) := by linarith
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 strict_scalar |>.trans_le
    (upperCap_angle_bound_of_fits square fits factor_gt_one cosine_positive sine_positive
      cap_le_cosine cap_le_sine)

theorem terminal_continuous_budget_of_fits
    (square : PlacedSquare) {size : ℕ} {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (horizontal_lower : 1 ≤ horizontal) (horizontal_upper : horizontal + 2 ≤ (size : ℝ) - 1)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 - exitHeight / 2) <
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom
          (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have cap_inside := upperCap_subset_inner_of_upper_facet square size_lower factor_positive
    factor_at_most cosine_positive sine_positive horizontal_lower horizontal_upper
    grid_point_mem upper_facet exit_at_most
  have area_bound : volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) := by
    rw [NagamochiResource.innerArea, Measure.restrict_apply region_measurable]
    exact measure_mono fun point point_mem => ⟨point_mem.1, cap_inside point_mem⟩
  have section_bound : volume {coordinate : ℝ |
      ![coordinate, 1] ∈ square.dilatedInteriorRegion factor} ≤
        NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
    rw [NagamochiResource.boundaryLine, horizontalSegmentMeasure_apply region_measurable]
    apply measure_mono
    intro coordinate coordinate_mem
    have bounds := cap_inside ⟨coordinate_mem, by norm_num⟩
    refine ⟨⟨?_, ?_⟩, coordinate_mem⟩
    · have lower := bounds.1 0
      norm_num at lower
      linarith
    · have upper := bounds.2 0
      norm_num at upper
      linarith
  exact (terminal_upperCap_budget_of_fits square fits factor_gt_one cosine_positive sine_positive
    grid_point_mem upper_facet exit_at_most vertex_below_grid).trans_le
      (add_le_add area_bound (mul_le_mul le_rfl section_bound bot_le bot_le))

end SquarePackingArchive.Nagamochi
