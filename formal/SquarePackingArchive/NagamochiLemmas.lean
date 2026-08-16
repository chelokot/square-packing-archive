import SquarePackingArchive.NagamochiResource

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma score_gt_one_of_dilatedInteriorRegion_subset_innerArea
    {size : ℕ} {factor : ℝ} {square : PlacedSquare}
    (factor_gt_one : 1 < factor)
    (inside_inner_area :
      square.dilatedInteriorRegion factor ⊆
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_measurable :=
    square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have inner_area_score :
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) =
        volume (square.dilatedInteriorRegion factor) := by
    rw [NagamochiResource.innerArea, Measure.restrict_apply region_measurable]
    rw [inter_eq_left.mpr inside_inner_area]
  have region_volume_gt_one :
      1 < volume (square.dilatedInteriorRegion factor) := by
    rw [square.volume_dilatedInteriorRegion factor_positive.le]
    rw [ENNReal.one_lt_ofReal]
    nlinarith
  calc
    1 < NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor) := by
      rw [inner_area_score]
      exact region_volume_gt_one
    _ ≤ NagamochiResource.measure size
        (square.dilatedInteriorRegion factor) := by
      simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
      calc
        _ ≤ NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
            NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) :=
          le_add_of_nonneg_right bot_le
        _ ≤ _ + NagamochiResource.cornerPoints size
            (square.dilatedInteriorRegion factor) := le_add_of_nonneg_right bot_le
        _ ≤ _ + NagamochiResource.edgePoints size
            (square.dilatedInteriorRegion factor) := le_add_of_nonneg_right bot_le

lemma adjacentCut_triangleArea_lt_half_chord
    {side firstLeg secondLeg : ℝ}
    (side_at_least_one : 1 ≤ side)
    (side_at_most : side ≤ 101 / 100)
    (firstLeg_positive : 0 < firstLeg)
    (firstLeg_at_most : firstLeg ≤ side)
    (secondLeg_positive : 0 < secondLeg)
    (secondLeg_at_most : secondLeg ≤ side) :
    firstLeg * secondLeg / 2 <
      Real.sqrt (firstLeg ^ 2 + secondLeg ^ 2) / 2 := by
  have side_positive : 0 < side := lt_of_lt_of_le zero_lt_one side_at_least_one
  have product_positive : 0 < firstLeg * secondLeg :=
    mul_pos firstLeg_positive secondLeg_positive
  have product_at_most_side_sq : firstLeg * secondLeg ≤ side ^ 2 := by
    nlinarith
  have side_sq_lt_two : side ^ 2 < 2 := by
    nlinarith
  have product_lt_two : firstLeg * secondLeg < 2 :=
    product_at_most_side_sq.trans_lt side_sq_lt_two
  have squared_product_lt_sum :
      (firstLeg * secondLeg) ^ 2 < firstLeg ^ 2 + secondLeg ^ 2 := by
    nlinarith [sq_nonneg (firstLeg - secondLeg)]
  have sum_nonnegative : 0 ≤ firstLeg ^ 2 + secondLeg ^ 2 :=
    add_nonneg (sq_nonneg firstLeg) (sq_nonneg secondLeg)
  have square_root_nonnegative :
      0 ≤ Real.sqrt (firstLeg ^ 2 + secondLeg ^ 2) := Real.sqrt_nonneg _
  have square_root_sq :
      (Real.sqrt (firstLeg ^ 2 + secondLeg ^ 2)) ^ 2 =
        firstLeg ^ 2 + secondLeg ^ 2 := Real.sq_sqrt sum_nonnegative
  have product_lt_square_root :
      firstLeg * secondLeg < Real.sqrt (firstLeg ^ 2 + secondLeg ^ 2) := by
    nlinarith
  linarith

end SquarePackingArchive.Nagamochi
