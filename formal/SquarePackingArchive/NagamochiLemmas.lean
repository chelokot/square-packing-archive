import SquarePackingArchive.NagamochiResource

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

noncomputable def centeredAdjacentChordLength (offset tangentHalfAngle : ℝ) : ℝ :=
  -offset * (1 + tangentHalfAngle ^ 2) ^ 2 /
      (2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)) +
    (1 + tangentHalfAngle ^ 2) *
      (1 + 2 * tangentHalfAngle - tangentHalfAngle ^ 2) /
        (4 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2))

lemma centeredAdjacentChordLength_gt_one
    {offset tangentHalfAngle : ℝ}
    (offset_nonnegative : 0 ≤ offset)
    (offset_lt : offset < (Real.sqrt 2 - 1) / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    1 < centeredAdjacentChordLength offset tangentHalfAngle := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt_two_gt_one : 1 < Real.sqrt 2 := by nlinarith
  have sqrt_two_lt_two : Real.sqrt 2 < 2 := by nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have tangent_sq_lt_one : tangentHalfAngle ^ 2 < 1 := by nlinarith
  have denominator_positive :
      0 < 4 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2) := by positivity
  let numerator :=
    -2 * offset * (1 + tangentHalfAngle ^ 2) ^ 2 +
      (1 + tangentHalfAngle ^ 2) *
        (1 + 2 * tangentHalfAngle - tangentHalfAngle ^ 2) -
          4 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)
  let maximumOffsetNumerator :=
    -2 * ((Real.sqrt 2 - 1) / 2) * (1 + tangentHalfAngle ^ 2) ^ 2 +
      (1 + tangentHalfAngle ^ 2) *
        (1 + 2 * tangentHalfAngle - tangentHalfAngle ^ 2) -
          4 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)
  let positiveFactor :=
    -Real.sqrt 2 * tangentHalfAngle ^ 2 +
      (2 + 2 * Real.sqrt 2) * tangentHalfAngle + 2 + Real.sqrt 2
  have tangent_sq_le_one : tangentHalfAngle ^ 2 ≤ 1 := tangent_sq_lt_one.le
  have positive_factor_positive : 0 < positiveFactor := by
    dsimp [positiveFactor]
    have square_term_le :
        Real.sqrt 2 * tangentHalfAngle ^ 2 ≤ Real.sqrt 2 := by
      exact mul_le_of_le_one_right sqrt_two_nonnegative tangent_sq_le_one
    have linear_term_nonnegative :
        0 ≤ (2 + 2 * Real.sqrt 2) * tangentHalfAngle := by positivity
    linarith
  have maximum_factorization :
      maximumOffsetNumerator =
        (tangentHalfAngle + 1 - Real.sqrt 2) ^ 2 * positiveFactor := by
    dsimp [maximumOffsetNumerator, positiveFactor]
    nlinarith
  have maximum_numerator_nonnegative : 0 ≤ maximumOffsetNumerator := by
    rw [maximum_factorization]
    positivity
  have numerator_gt_maximum : maximumOffsetNumerator < numerator := by
    dsimp [maximumOffsetNumerator, numerator]
    have coefficient_positive : 0 < (1 + tangentHalfAngle ^ 2) ^ 2 := by positivity
    nlinarith
  have numerator_positive : 0 < numerator :=
    maximum_numerator_nonnegative.trans_lt numerator_gt_maximum
  have chord_difference :
      centeredAdjacentChordLength offset tangentHalfAngle - 1 =
        numerator /
          (4 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)) := by
    dsimp [centeredAdjacentChordLength, numerator]
    field_simp [ne_of_gt tangent_positive, ne_of_gt (sub_pos.mpr tangent_sq_lt_one)]
    ring
  rw [← sub_pos] at ⊢
  rw [chord_difference]
  positivity

noncomputable def cornerAdjacentChordLength (height tangentHalfAngle : ℝ) : ℝ :=
  -(height - 1) * (1 + tangentHalfAngle ^ 2) ^ 2 /
      (2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)) +
    2 * tangentHalfAngle *
      (1 - tangentHalfAngle + tangentHalfAngle ^ 2 - tangentHalfAngle ^ 3) /
        (2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2))

lemma cornerAdjacentChordLength_gt_one
    {height tangentHalfAngle : ℝ}
    (height_gt_half : 1 / 2 < height)
    (height_lt : height < Real.sqrt 2 - 1 / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    1 < cornerAdjacentChordLength height tangentHalfAngle := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt_two_gt_one : 1 < Real.sqrt 2 := by nlinarith
  have sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by nlinarith
  have tangent_nonnegative : 0 ≤ tangentHalfAngle := tangent_positive.le
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have tangent_sq_lt_one : tangentHalfAngle ^ 2 < 1 := by nlinarith
  have denominator_positive :
      0 < 2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2) := by positivity
  let numerator :=
    -(height - 1) * (1 + tangentHalfAngle ^ 2) ^ 2 +
      2 * tangentHalfAngle *
        (1 - tangentHalfAngle + tangentHalfAngle ^ 2 - tangentHalfAngle ^ 3) -
          2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)
  let maximumHeightNumerator :=
    -((Real.sqrt 2 - 1 / 2) - 1) * (1 + tangentHalfAngle ^ 2) ^ 2 +
      2 * tangentHalfAngle *
        (1 - tangentHalfAngle + tangentHalfAngle ^ 2 - tangentHalfAngle ^ 3) -
          2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)
  let positiveFactor :=
    -(1 + 2 * Real.sqrt 2) * tangentHalfAngle ^ 2 +
      (2 * Real.sqrt 2 + 2) * tangentHalfAngle + 1
  have tangent_sq_at_most :
      tangentHalfAngle ^ 2 ≤ (Real.sqrt 2 - 1) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr tangent_at_most)
      (add_nonneg tangent_nonnegative (sub_nonneg.mpr sqrt_two_gt_one.le))]
  have negative_term_lt_one :
      (1 + 2 * Real.sqrt 2) * tangentHalfAngle ^ 2 < 1 := by
    have coefficient_positive : 0 < 1 + 2 * Real.sqrt 2 := by positivity
    have scaled_bound := mul_le_mul_of_nonneg_left tangent_sq_at_most coefficient_positive.le
    have endpoint_lt_one :
        (1 + 2 * Real.sqrt 2) * (Real.sqrt 2 - 1) ^ 2 < 1 := by
      nlinarith
    exact scaled_bound.trans_lt endpoint_lt_one
  have positive_factor_positive : 0 < positiveFactor := by
    dsimp [positiveFactor]
    have linear_term_nonnegative :
        0 ≤ (2 * Real.sqrt 2 + 2) * tangentHalfAngle := by positivity
    linarith
  have maximum_factorization :
      maximumHeightNumerator =
        (tangentHalfAngle + 1 - Real.sqrt 2) ^ 2 * positiveFactor / 2 := by
    dsimp [maximumHeightNumerator, positiveFactor]
    nlinarith
  have maximum_numerator_nonnegative : 0 ≤ maximumHeightNumerator := by
    rw [maximum_factorization]
    positivity
  have numerator_gt_maximum : maximumHeightNumerator < numerator := by
    dsimp [maximumHeightNumerator, numerator]
    have coefficient_positive : 0 < (1 + tangentHalfAngle ^ 2) ^ 2 := by positivity
    nlinarith
  have numerator_positive : 0 < numerator :=
    maximum_numerator_nonnegative.trans_lt numerator_gt_maximum
  have chord_difference :
      cornerAdjacentChordLength height tangentHalfAngle - 1 =
        numerator /
          (2 * tangentHalfAngle * (1 - tangentHalfAngle ^ 2)) := by
    dsimp [cornerAdjacentChordLength, numerator]
    field_simp [ne_of_gt tangent_positive, ne_of_gt (sub_pos.mpr tangent_sq_lt_one)]
  rw [← sub_pos] at ⊢
  rw [chord_difference]
  positivity

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
