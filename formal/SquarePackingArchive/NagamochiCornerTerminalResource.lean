import SquarePackingArchive.NagamochiEndpointResource
import SquarePackingArchive.NagamochiBoundaryPropagation

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem corner_terminal_score_repays_incoming_height
    (square : PlacedSquare) {size : ℕ} {side factor incomingHeight : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(2 : ℝ), 9 / 10] ∉ square.dilatedInteriorRegion factor)
    (incoming_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨1, incomingHeight⟩)
    (incoming_at_most : incomingHeight ≤ 1)
    (rightmost_vertex_below : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 + (1 - incomingHeight) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor := by
    intro point_mem
    have local_bound := (inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive point_mem).2
    rw [abs_lt] at local_bound
    dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at local_bound incoming_facet
    nlinarith
  have exit_bounds := bottom_left_exit_height_bounds square fits factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have exit_facet : factor / 2 ≤ square.dilatedLocalY factor ⟨1, bottomLeftExitHeight square factor⟩ := by
    apply le_of_eq
    dsimp [PlacedSquare.dilatedLocalY, bottomLeftExitHeight]
    field_simp
    ring
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have terminal_budget := endpoint_two_height_continuous_budget_of_fits square fits size_at_least_four
    factor_gt_one factor_at_most cosine_positive sine_positive (by norm_num : (1 : ℝ) ≤ 1)
    (by linarith : (1 : ℝ) + 1 ≤ (size : ℝ) - 1) corner_mem
    (by norm_num; exact next_point_missing) incoming_facet exit_facet incoming_at_most rightmost_vertex_below
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
    (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) ≠ ⊤)).2 terminal_budget
  have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (9 / 20 : ENNReal) ≠ ⊤)).2 first_strict
  have length_nonnegative : 0 ≤ bottomLeftExitHeight square factor - 9 / 10 := by linarith [exit_bounds.1]
  have terminal_nonnegative : 0 ≤ 1 / 2 + (1 - incomingHeight) / 2 +
      (1 - bottomLeftExitHeight square factor) / 2 := by linarith [exit_bounds.2]
  have final_nonnegative : 0 ≤ 1 + (1 - incomingHeight) / 2 := by linarith
  have budget_identity : ENNReal.ofReal
      (1 / 2 + (1 - incomingHeight) / 2 + (1 - bottomLeftExitHeight square factor) / 2) +
      (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) + 9 / 20 =
      ENNReal.ofReal (1 + (1 - incomingHeight) / 2) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal length_nonnegative,
      ENNReal.toReal_ofReal terminal_nonnegative, ENNReal.toReal_ofReal final_nonnegative]
    norm_num
    ring
  rw [budget_identity] at strict
  exact (strict.trans_le (add_le_add continuous_bound corner_bound)).trans_le
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size _)

end SquarePackingArchive.Nagamochi
