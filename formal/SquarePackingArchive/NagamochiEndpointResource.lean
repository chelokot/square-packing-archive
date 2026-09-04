import SquarePackingArchive.NagamochiTerminalEndpoint
import SquarePackingArchive.NagamochiChainGeometry

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem endpoint_upperCap_subset_inner
    (square : PlacedSquare) {size : ℕ} {factor horizontal exitHeight : ℝ}
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (horizontal_lower : 1 ≤ horizontal) (horizontal_upper : horizontal + 1 ≤ (size : ℝ) - 1)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1} ⊆
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
  have next_upper := next_grid_point_upper_facet_of_missing square factor_positive
    cosine_positive sine_positive grid_point_mem next_point_missing vertex_below_grid
  rintro point ⟨point_mem, point_above⟩
  change 1 ≤ point 1 at point_above
  have point_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive point_mem
  rw [abs_lt, abs_lt] at point_bounds
  have point_right : horizontal < point 0 := by
    have upper_at_point := point_bounds.2.2
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_at_point upper_facet
    have vertical_increase := mul_nonneg cosine_positive.le
      (show 0 ≤ point 1 - exitHeight by linarith)
    nlinarith
  have point_left : point 0 < horizontal + 1 := by
    have upper_at_point := point_bounds.1.2
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at upper_at_point next_upper
    have vertical_increase := mul_nonneg sine_positive.le
      (show 0 ≤ point 1 - 9 / 10 by linarith)
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

theorem endpoint_upperCap_continuous_le
    (square : PlacedSquare) {size : ℕ} {factor horizontal exitHeight : ℝ}
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (horizontal_lower : 1 ≤ horizontal) (horizontal_upper : horizontal + 1 ≤ (size : ℝ) - 1)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) +
        (1 / 2 : ENNReal) * volume {coordinate : ℝ |
          ![coordinate, 1] ∈ square.dilatedInteriorRegion factor} ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom
          (square.dilatedInteriorRegion factor) := by
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have cap_inside := endpoint_upperCap_subset_inner square size_lower factor_positive factor_at_most
    cosine_positive sine_positive horizontal_lower horizontal_upper grid_point_mem next_point_missing
    upper_facet exit_at_most vertex_below_grid
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
  exact add_le_add area_bound (mul_le_mul le_rfl section_bound bot_le bot_le)

theorem endpoint_two_height_continuous_budget_of_fits
    (square : PlacedSquare) {size : ℕ} {side factor horizontal firstHeight secondHeight : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (horizontal_lower : 1 ≤ horizontal) (horizontal_upper : horizontal + 1 ≤ (size : ℝ) - 1)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, firstHeight⟩)
    (second_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, secondHeight⟩)
    (first_at_most : firstHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 / 2 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom
          (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have scalar_bound := endpoint_two_height_potentials_repaid_of_fits square fits factor_gt_one
    cosine_positive sine_positive grid_point_mem next_point_missing first_upper_facet second_upper_facet
    vertex_below_grid
  have other_vertex := (upper_facet_vertex_below_exit square factor_positive cosine_positive
    sine_positive grid_point_mem first_upper_facet).2
  have cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine := by
    dsimp [horizontalUpperCapHeight]
    linarith
  have cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine := by
    dsimp [horizontalUpperCapHeight]
    linarith
  have strict_bound : ENNReal.ofReal (1 / 2 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      ENNReal.ofReal ((square.frame.cosine + square.frame.sine) /
        (1 + square.frame.cosine + square.frame.sine)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    linarith
  exact strict_bound.trans_le ((upperCap_angle_bound_of_fits square fits factor_gt_one
    cosine_positive sine_positive cap_le_cosine cap_le_sine).trans
      (endpoint_upperCap_continuous_le square size_lower factor_positive factor_at_most
        cosine_positive sine_positive horizontal_lower horizontal_upper grid_point_mem next_point_missing
        first_upper_facet first_at_most vertex_below_grid))

theorem endpoint_two_height_score_budget_of_fits
    (square : PlacedSquare) {size coordinate : ℕ} {side factor firstHeight secondHeight : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (grid_point_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨coordinate, firstHeight⟩)
    (second_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨coordinate, secondHeight⟩)
    (first_at_most : firstHeight ≤ 1) (second_at_most : secondHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have coordinate_bounds := Finset.mem_Icc.mp coordinate_mem
  have coordinate_lower : (2 : ℝ) ≤ coordinate := by exact_mod_cast coordinate_bounds.1
  have coordinate_upper : (coordinate : ℝ) + 1 ≤ (size : ℝ) - 1 := by
    have cast_bound : (coordinate : ℝ) ≤ ((size - 2 : ℕ) : ℝ) := by exact_mod_cast coordinate_bounds.2
    rw [Nat.cast_sub (by omega : 2 ≤ size), Nat.cast_ofNat] at cast_bound
    linarith
  have region_measurable := square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne'
  have continuous_bound := endpoint_two_height_continuous_budget_of_fits square fits size_lower
    factor_gt_one factor_at_most cosine_positive sine_positive (by linarith) coordinate_upper
    grid_point_mem next_point_missing first_upper_facet second_upper_facet first_at_most vertex_below_grid
  have marked_bound := NagamochiResource.edgePoints_lower_bound_of_mem .bottom coordinate_mem
    region_measurable grid_point_mem
  have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 / 2 : ENNReal) ≠ ⊤)).2 continuous_bound
  have encoded : ENNReal.ofReal (1 / 2 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) +
      (1 / 2 : ENNReal) = ENNReal.ofReal (1 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) := by
    rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by norm_num [ENNReal.ofReal_div_of_pos],
      ← ENNReal.ofReal_add (by linarith) (by norm_num)]
    congr 1
    ring
  rw [encoded] at strict
  have line_bound := NagamochiResource.boundaryLine_le_boundaryLines size .bottom
    (square.dilatedInteriorRegion factor)
  have resource_bound :
      (NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom
          (square.dilatedInteriorRegion factor)) + NagamochiResource.edgePoints size
            (square.dilatedInteriorRegion factor) ≤
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
    simp only [NagamochiResource.measure, Measure.add_apply]
    exact add_le_add ((add_le_add le_rfl line_bound).trans (le_add_of_nonneg_right bot_le)) le_rfl
  exact (strict.trans_le (add_le_add le_rfl marked_bound)).trans_le resource_bound

end SquarePackingArchive.Nagamochi
