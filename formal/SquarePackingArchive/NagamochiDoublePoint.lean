import SquarePackingArchive.NagamochiAugmentedResource
import SquarePackingArchive.NagamochiBadSquare

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma edgePoints_ge_one_of_two_bottom_points
    {size coordinate : ℕ} {region : Set Plane}
    (region_measurable : MeasurableSet region)
    (coordinate_lower : 2 ≤ coordinate) (coordinate_upper : coordinate + 1 ≤ size - 2)
    (first_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ region)
    (second_mem : ![((coordinate + 1 : ℕ) : ℝ), (9 / 10 : ℝ)] ∈ region) :
    1 ≤ NagamochiResource.edgePoints size region := by
  have first_bound := NagamochiResource.edgePointCluster_lower_bound_of_mem
    (size := size) (coordinate := coordinate) .bottom region_measurable
    (by simpa [NagamochiResource.edgePoint] using first_mem)
  have second_bound := NagamochiResource.edgePointCluster_lower_bound_of_mem
    (size := size) (coordinate := coordinate + 1) .bottom region_measurable
    (by simpa [NagamochiResource.edgePoint] using second_mem)
  have pair_subset : ({coordinate, coordinate + 1} : Finset ℕ) ⊆ Finset.Icc 2 (size - 2) := by
    intro selected selected_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at selected_mem
    simp only [Finset.mem_Icc]
    rcases selected_mem with rfl | rfl <;> omega
  have pair_bound := Finset.sum_le_sum_of_subset
    (f := fun selected => NagamochiResource.edgePointCluster size selected region) pair_subset
  rw [Finset.sum_pair (by omega : coordinate ≠ coordinate + 1)] at pair_bound
  have halves : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  have marked_bound := add_le_add first_bound second_bound
  rw [halves] at marked_bound
  exact (marked_bound.trans pair_bound).trans_eq (by
    simp only [NagamochiResource.edgePoints, Measure.finsetSum_apply])

lemma region_bounds_of_two_bottom_points
    (square : PlacedSquare) {size coordinate : ℕ} {factor : ℝ}
    (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (coordinate_lower : 2 ≤ coordinate) (coordinate_upper : coordinate + 1 ≤ size - 2)
    (first_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (second_mem : ![((coordinate + 1 : ℕ) : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor) :
    ∀ point ∈ square.dilatedInteriorRegion factor,
      1 < point 0 ∧ point 0 < (size : ℝ) - 1 ∧ point 1 < (size : ℝ) - 1 := by
  have size_lower : 5 ≤ size := by omega
  have size_real : (5 : ℝ) ≤ size := by exact_mod_cast size_lower
  have coordinate_real_lower : (2 : ℝ) ≤ coordinate := by exact_mod_cast coordinate_lower
  have coordinate_real_upper : (coordinate : ℝ) + 1 ≤ (size : ℝ) - 2 := by
    have cast_bound : ((coordinate + 1 : ℕ) : ℝ) ≤ ((size - 2 : ℕ) : ℝ) := by
      exact_mod_cast coordinate_upper
    simpa [Nat.cast_sub (by omega : 2 ≤ size)] using cast_bound
  intro point point_mem
  have first_distance := dilated_square_coordinate_distance_lt_two square factor_positive
    factor_at_most point_mem first_mem
  have second_distance := dilated_square_coordinate_distance_lt_two square factor_positive
    factor_at_most point_mem second_mem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_add, Nat.cast_one,
    abs_lt] at first_distance second_distance
  exact ⟨by linarith [second_distance.1.1],
    by linarith [first_distance.1.2], by linarith [first_distance.2.2]⟩

theorem score_gt_three_halves_of_two_bottom_points
    (square : PlacedSquare) {size coordinate : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (coordinate_lower : 2 ≤ coordinate) (coordinate_upper : coordinate + 1 ≤ size - 2)
    (first_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (second_mem : ![((coordinate + 1 : ℕ) : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor) :
    (3 / 2 : ENNReal) < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_lower : 5 ≤ size := by omega
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have bounds := region_bounds_of_two_bottom_points square factor_positive factor_at_most
    coordinate_lower coordinate_upper first_mem second_mem
  have center_bounds := bounds _ (square.dilatedCenter_mem_dilatedInteriorRegion factor_positive)
  have center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1) := by
    simp only [Point.toPlane, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at center_bounds
    exact ⟨center_bounds.1.le, center_bounds.2.1.le⟩
  have continuous_bound : (1 / 2 : ENNReal) <
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) := by
    by_cases center_below : factor * square.center.y ≤ 1
    · have first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉
          square.dilatedInteriorRegion factor := by
        intro contained
        have lower := (bounds _ contained).1
        norm_num [NagamochiResource.cornerPoint] at lower
      have second_missing : NagamochiResource.cornerPoint size .bottomRight ∉
          square.dilatedInteriorRegion factor := by
        intro contained
        have upper := (bounds _ contained).2.1
        norm_num [NagamochiResource.cornerPoint] at upper
      exact continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners square fits
        (by omega) factor_gt_one factor_at_most inside_container center_horizontal center_below
        first_missing second_missing
    · have half_area := half_innerArea_of_single_inner_boundary_crossing (size := size) square .bottom
        factor_positive (by
          simp only [InnerBoundarySide.inwardThreshold, InnerBoundarySide.inwardNormal,
            ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, Point.toPlane,
            Matrix.cons_val_one]
          exact (lt_of_not_ge center_below).le)
        (by
          intro point point_mem other other_ne
          have point_bounds := bounds point point_mem
          cases other <;>
            simp only [InnerBoundarySide.inwardThreshold, InnerBoundarySide.inwardNormal,
              ContinuousLinearMap.proj_apply, neg_apply] <;>
            first | exact False.elim (other_ne rfl) | linarith [point_bounds.1,
              point_bounds.2.1, point_bounds.2.2])
      have area_gt_one : 1 < ENNReal.ofReal (factor ^ 2) := by
        rw [ENNReal.one_lt_ofReal]
        nlinarith
      have strict := ENNReal.mul_lt_mul_right (a := (1 / 2 : ENNReal))
        (by norm_num) (by finiteness) area_gt_one
      simp only [mul_one] at strict
      exact (strict.trans_le half_area).trans_le (le_add_of_nonneg_right bot_le)
  have marked_bound := edgePoints_ge_one_of_two_bottom_points region_measurable
    coordinate_lower coordinate_upper first_mem second_mem
  have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 : ENNReal) ≠ ⊤)).2
    continuous_bound
  have constant_eq : (1 / 2 : ENNReal) + 1 = 3 / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  rw [constant_eq] at strict
  have combined := strict.trans_le (add_le_add le_rfl marked_bound)
  exact combined.trans_le (by
    simp only [NagamochiResource.measure, Measure.add_apply]
    exact add_le_add (le_add_of_nonneg_right bot_le) le_rfl)

theorem augmentedScore_gt_three_halves_of_two_bottom_points
    (square : PlacedSquare) {size coordinate : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (coordinate_lower : 2 ≤ coordinate) (coordinate_upper : coordinate + 1 ≤ size - 2)
    (first_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (second_mem : ![((coordinate + 1 : ℕ) : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor) :
    (3 / 2 : ENNReal) < NagamochiAugmentedResource.measure size (square.dilatedInteriorRegion factor) :=
  (score_gt_three_halves_of_two_bottom_points square fits factor_gt_one factor_at_most
    inside_container coordinate_lower coordinate_upper first_mem second_mem).trans_le
    (NagamochiAugmentedResource.original_le size _)

end SquarePackingArchive.Nagamochi
