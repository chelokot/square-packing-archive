import SquarePackingArchive.NagamochiAdjacentMarks
import SquarePackingArchive.NagamochiGlobalBadSquare

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem bottom_strip_of_bad_left_bottom_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1) ∧ factor * square.center.y ≤ 1 := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have distance := dilated_square_point_center_coordinate_distance_lt_one square
    positive factor_at_most corner_mem
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at distance
  rw [abs_lt, abs_lt] at distance
  have horizontal_upper : factor * square.center.x ≤ (size : ℝ) - 1 := by linarith
  have vertical_upper : factor * square.center.y ≤ (size : ℝ) - 1 := by linarith
  have horizontal_lower : 1 ≤ factor * square.center.x := by
    by_contra! center_left
    by_cases center_below : factor * square.center.y ≤ 1
    · exact (not_lt_of_ge bad) (score_gt_one_of_case5 square (by omega) factor_gt_one
        inside_container (Or.inl center_left.le) (Or.inl center_below))
    · have swapped_corner : NagamochiResource.cornerPoint size .bottomLeft ∈
          square.swap.dilatedInteriorRegion factor := by
        have contained := (square.mem_swap_dilatedInteriorRegion_iff positive _).2 corner_mem
        simpa [NagamochiResource.cornerPoint, Plane.swap] using contained
      have swapped_score := score_gt_one_of_bottom_strip_bottomLeft_corner square.swap
        ((square.swap_fits_iff side).2 fits) size_at_least_four factor_gt_one factor_at_most
        (square.swap_dilatedInteriorRegion_subset_containerRegion positive inside_container)
        (by simpa [PlacedSquare.swap, Point.swap] using
          (show factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1) from ⟨by linarith, vertical_upper⟩))
        (by simpa [PlacedSquare.swap, Point.swap] using center_left.le) swapped_corner
      rw [(original_components_swap square size positive).1] at swapped_score
      exact (not_lt_of_ge bad) swapped_score
  refine ⟨⟨horizontal_lower, horizontal_upper⟩, ?_⟩
  by_contra! center_above
  apply (not_lt_of_ge bad) (score_gt_one_of_center_inner square factor_gt_one factor_at_most inside_container ?_)
  simp only [Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, Point.toPlane,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact ⟨⟨horizontal_lower, center_above.le⟩, ⟨horizontal_upper, vertical_upper⟩⟩

end SquarePackingArchive.Nagamochi
