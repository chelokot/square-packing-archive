import SquarePackingArchive.NagamochiBoundaryPropagation
import SquarePackingArchive.NagamochiChainPotential

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma upper_facet_of_missing_above_anchor
    (square : PlacedSquare) {factor horizontal baseline height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (anchor_mem : ![horizontal, baseline] ∈ square.dilatedInteriorRegion factor)
    (height_above : baseline ≤ height)
    (point_missing : ![horizontal, height] ∉ square.dilatedInteriorRegion factor) :
    factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, height⟩ ∨
      factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, height⟩ := by
  have anchor_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive anchor_mem
  rw [abs_lt, abs_lt] at anchor_bounds
  by_contra! upper_bounds
  apply point_missing
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    refine ⟨?_, upper_bounds.1⟩
    have anchor_lower := anchor_bounds.1.1
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at anchor_lower ⊢
    nlinarith
  · rw [abs_lt]
    refine ⟨?_, upper_bounds.2⟩
    have anchor_lower := anchor_bounds.2.1
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at anchor_lower ⊢
    nlinarith

lemma common_upper_facet_of_two_missing_above_anchor
    (square : PlacedSquare) {factor horizontal baseline firstHeight secondHeight : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (anchor_mem : ![horizontal, baseline] ∈ square.dilatedInteriorRegion factor)
    (first_above : baseline ≤ firstHeight) (second_above : baseline ≤ secondHeight)
    (first_missing : ![horizontal, firstHeight] ∉ square.dilatedInteriorRegion factor)
    (second_missing : ![horizontal, secondHeight] ∉ square.dilatedInteriorRegion factor) :
    (factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, firstHeight⟩ ∧
      factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal, secondHeight⟩) ∨
    (factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, firstHeight⟩ ∧
      factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, secondHeight⟩) := by
  rcases le_total firstHeight secondHeight with ordered | ordered
  · rcases upper_facet_of_missing_above_anchor square factor_positive cosine_nonnegative
      sine_nonnegative anchor_mem first_above first_missing with horizontal_facet | vertical_facet
    · left
      refine ⟨horizontal_facet, ?_⟩
      dsimp [PlacedSquare.dilatedLocalX] at horizontal_facet ⊢
      nlinarith
    · right
      refine ⟨vertical_facet, ?_⟩
      dsimp [PlacedSquare.dilatedLocalY] at vertical_facet ⊢
      nlinarith
  · rcases upper_facet_of_missing_above_anchor square factor_positive cosine_nonnegative
      sine_nonnegative anchor_mem second_above second_missing with horizontal_facet | vertical_facet
    · left
      refine ⟨?_, horizontal_facet⟩
      dsimp [PlacedSquare.dilatedLocalX] at horizontal_facet ⊢
      nlinarith
    · right
      refine ⟨?_, vertical_facet⟩
      dsimp [PlacedSquare.dilatedLocalY] at vertical_facet ⊢
      nlinarith

lemma next_grid_point_upper_facet_of_missing
    (square : PlacedSquare) {factor horizontal : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    factor / 2 ≤ square.dilatedLocalX factor ⟨horizontal + 1, 9 / 10⟩ := by
  have point_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive grid_point_mem
  rw [abs_lt, abs_lt] at point_bounds
  by_contra! horizontal_upper
  apply next_point_missing
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    refine ⟨?_, horizontal_upper⟩
    have lower_bound := point_bounds.1.1
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at lower_bound ⊢
    linarith
  · rw [abs_lt]
    constructor
    · have horizontal_scaled := mul_lt_mul_of_pos_left horizontal_upper sine_positive
      have vertical_identity := congrArg (fun value : ℝ =>
        (9 / 10 - factor * square.center.y) * value) square.frame.unit
      apply (mul_lt_mul_iff_right₀ cosine_positive).mp
      dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint] at horizontal_scaled ⊢
      nlinarith
    · have upper_bound := point_bounds.2.2
      dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_bound ⊢
      linarith

theorem endpoint_exit_deficit_bound_of_fits
    (square : PlacedSquare) {side factor horizontal exitHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, exitHeight⟩)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    1 - exitHeight <
      ((1 - square.frame.cosine) * (1 - square.frame.sine) - square.frame.sine ^ 2 / 10) /
        square.frame.cosine ^ 2 := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have next_upper := next_grid_point_upper_facet_of_missing square factor_positive
    cosine_positive sine_positive grid_point_mem next_point_missing vertex_below_grid
  have next_scaled := mul_le_mul_of_nonneg_left next_upper sine_positive.le
  have exit_scaled := mul_le_mul_of_nonneg_left upper_facet cosine_positive.le
  have bottom_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_pos cosine_positive, abs_of_pos sine_positive] at bottom_bound
  have scaled_bottom := mul_le_mul_of_nonneg_left bottom_bound factor_positive.le
  have factor_sum := mul_lt_mul_of_pos_right factor_gt_one (add_pos cosine_positive sine_positive)
  dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY] at next_scaled exit_scaled
  apply (lt_div_iff₀ (sq_pos_of_pos cosine_positive)).mpr
  nlinarith [square.frame.unit]

theorem endpoint_two_height_potentials_repaid_of_fits
    (square : PlacedSquare) {side factor horizontal firstHeight secondHeight : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (grid_point_mem : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![horizontal + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, firstHeight⟩)
    (second_upper_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨horizontal, secondHeight⟩)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    (1 - firstHeight) / 2 + (1 - secondHeight) / 2 <
      (square.frame.cosine + square.frame.sine) /
        (1 + square.frame.cosine + square.frame.sine) - 1 / 2 := by
  have first_deficit := endpoint_exit_deficit_bound_of_fits square fits factor_gt_one
    cosine_positive sine_positive grid_point_mem next_point_missing first_upper_facet vertex_below_grid
  have second_deficit := endpoint_exit_deficit_bound_of_fits square fits factor_gt_one
    cosine_positive sine_positive grid_point_mem next_point_missing second_upper_facet vertex_below_grid
  have scalar_bound := no_crossing_exit_deficit_lt_half_cap_surplus
    cosine_positive sine_positive square.frame.unit
  have identity : (square.frame.cosine + square.frame.sine - 1) /
      (2 * (square.frame.cosine + square.frame.sine + 1)) =
      (square.frame.cosine + square.frame.sine) /
        (1 + square.frame.cosine + square.frame.sine) - 1 / 2 := by
    have first_nonzero : square.frame.cosine + square.frame.sine + 1 ≠ 0 := by positivity
    have second_nonzero : 1 + square.frame.cosine + square.frame.sine ≠ 0 := by positivity
    field_simp
    ring
  rw [identity] at scalar_bound
  linarith

end SquarePackingArchive.Nagamochi
