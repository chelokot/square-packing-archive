import SquarePackingArchive.NagamochiBoundaryPropagation

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma rightmost_vertex_beyond_successor_of_upper_facet
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1) :
    horizontal + 1 < factor * square.center.x +
      factor * (square.frame.cosine + square.frame.sine) / 2 := by
  have factor_positive : 0 < factor := by linarith
  have bottom_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative,
    abs_of_pos sine_positive] at bottom_bound
  have scaled_bottom := mul_le_mul_of_nonneg_left bottom_bound
    (mul_nonneg factor_positive.le cosine_nonnegative)
  have cosine_at_most : square.frame.cosine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.sine]
  have sine_at_most : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.cosine]
  have product_nonnegative := mul_nonneg (sub_nonneg.mpr cosine_at_most) (sub_nonneg.mpr sine_at_most)
  have strict_factor := mul_lt_mul_of_pos_right factor_gt_one
    (by positivity : 0 < 1 + square.frame.cosine * square.frame.sine)
  have height_bound := mul_le_mul_of_nonneg_left exit_at_most cosine_nonnegative
  apply (mul_lt_mul_iff_left₀ sine_positive).mp
  dsimp [PlacedSquare.dilatedLocalY] at upper_facet
  nlinarith [square.frame.unit]

theorem chain_step_of_upper_facet_and_high_rightmost_vertex
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (exit_at_most : exitHeight ≤ 1)
    (rightmost_vertex_above_grid : 9 / 10 ≤ factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2) :
    ∃ height ∈ Icc (9 / 10 : ℝ) exitHeight,
      ![horizontal + 1, height] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := by linarith
  have anchor_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive grid_point_mem
  rw [abs_lt, abs_lt] at anchor_bounds
  have exit_above_grid : 9 / 10 < exitHeight := by
    have upper_at_grid := anchor_bounds.2.2
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_at_grid upper_facet
    nlinarith
  have rightmost := rightmost_vertex_beyond_successor_of_upper_facet square fits factor_gt_one
    cosine_positive.le sine_positive upper_facet exit_at_most
  by_cases vertex_below_exit : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ exitHeight
  · have vertex_mem := square.dilatedPoint_mem_closure factor_positive
      (by rw [abs_of_pos (by positivity)] : |factor / 2| ≤ factor / 2)
      (by rw [abs_neg, abs_of_pos (by positivity)] : |-(factor / 2)| ≤ factor / 2)
    apply vertical_band_crossing_of_open_convex_closure
      (square.convex_dilatedInteriorRegion factor)
      (square.isOpen_dilatedInteriorRegion factor_positive.ne')
      grid_point_mem vertex_mem (by simp)
    · convert rightmost using 1
      dsimp [PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
      ring
    · exact ⟨le_rfl, exit_above_grid.le⟩
    · convert (show factor * square.center.y +
          factor * (square.frame.sine - square.frame.cosine) / 2 ∈ Icc (9 / 10 : ℝ) exitHeight
          from ⟨rightmost_vertex_above_grid, vertex_below_exit⟩) using 1
      simp [PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
      ring
  · let localX := (exitHeight - factor * square.center.y + factor * square.frame.cosine / 2) /
      square.frame.sine
    have bottom_below_grid : factor * square.center.y -
        factor * (square.frame.cosine + square.frame.sine) / 2 < 9 / 10 := by
      have horizontal_lower := mul_lt_mul_of_pos_left anchor_bounds.1.1 sine_positive
      have vertical_lower := mul_lt_mul_of_pos_left anchor_bounds.2.1 cosine_positive
      dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint]
        at horizontal_lower vertical_lower
      nlinarith [square.frame.unit,
        congrArg (fun value : ℝ => ((9 / 10 : ℝ) - factor * square.center.y) * value) square.frame.unit]
    have local_lower : -(factor / 2) ≤ localX := by
      dsimp [localX]
      rw [le_div_iff₀ sine_positive]
      linarith
    have local_upper : localX ≤ factor / 2 := by
      dsimp [localX]
      rw [div_le_iff₀ sine_positive]
      linarith
    let edgePoint := square.dilatedPoint factor localX (-(factor / 2))
    have edge_mem : edgePoint.toPlane ∈ closure (square.dilatedInteriorRegion factor) :=
      square.dilatedPoint_mem_closure factor_positive (abs_le.mpr ⟨local_lower, local_upper⟩)
        (by rw [abs_neg, abs_of_pos (by positivity)])
    have edge_height : edgePoint.y = exitHeight := by
      dsimp [edgePoint, localX, PlacedSquare.dilatedPoint, Frame.place]
      field_simp
      ring
    have edge_identity : square.frame.sine * edgePoint.x =
        square.dilatedLocalY factor ⟨horizontal, exitHeight⟩ +
          square.frame.sine * horizontal + factor / 2 := by
      calc
        square.frame.sine * edgePoint.x =
            square.dilatedLocalY factor ⟨horizontal, exitHeight⟩ +
              square.frame.sine * horizontal +
                factor * (square.frame.cosine ^ 2 + square.frame.sine ^ 2) / 2 := by
          dsimp [edgePoint, localX, PlacedSquare.dilatedPoint, Frame.place, PlacedSquare.dilatedLocalY]
          field_simp
          ring
        _ = _ := by rw [square.frame.unit]; ring
    have edge_beyond : horizontal + 1 < edgePoint.x := by
      have sine_at_most : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.cosine]
      apply (mul_lt_mul_iff_left₀ sine_positive).mp
      nlinarith
    apply vertical_band_crossing_of_open_convex_closure
      (square.convex_dilatedInteriorRegion factor)
      (square.isOpen_dilatedInteriorRegion factor_positive.ne')
      grid_point_mem edge_mem (by simp) edge_beyond
    · exact ⟨le_rfl, exit_above_grid.le⟩
    · change edgePoint.y ∈ Icc (9 / 10 : ℝ) exitHeight
      rw [edge_height]
      exact ⟨exit_above_grid.le, le_rfl⟩

end SquarePackingArchive.Nagamochi
