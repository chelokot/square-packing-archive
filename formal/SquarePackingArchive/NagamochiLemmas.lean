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

noncomputable def cornerCutAreaCoefficient (tangentHalfAngle : ℝ) : ℝ :=
  tangentHalfAngle * (1 - tangentHalfAngle ^ 2) /
    (1 + tangentHalfAngle ^ 2) ^ 2

noncomputable def unitCornerCutArea (tangentHalfAngle : ℝ) : ℝ :=
  (tangentHalfAngle - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle)

noncomputable def unitCornerCutChord (tangentHalfAngle : ℝ) : ℝ :=
  1 - unitCornerCutArea tangentHalfAngle

lemma cornerCut_area_add_half_chord_gt_half
    {tangentHalfAngle chordGrowth : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1)
    (chord_growth_nonnegative : 0 ≤ chordGrowth) :
    let chord := unitCornerCutChord tangentHalfAngle + chordGrowth
    let area := chord ^ 2 * cornerCutAreaCoefficient tangentHalfAngle
    1 / 2 < area + chord / 2 := by
  have one_add_tangent_positive : 0 < 1 + tangentHalfAngle := by linarith
  have one_minus_tangent_sq_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
    nlinarith
  have coefficient_positive : 0 < cornerCutAreaCoefficient tangentHalfAngle := by
    dsimp [cornerCutAreaCoefficient]
    positivity
  have unit_area_positive : 0 < unitCornerCutArea tangentHalfAngle := by
    dsimp [unitCornerCutArea]
    exact div_pos (by nlinarith) one_add_tangent_positive
  have unit_area_lt_one : unitCornerCutArea tangentHalfAngle < 1 := by
    rw [unitCornerCutArea, div_lt_one one_add_tangent_positive]
    nlinarith
  have unit_chord_positive : 0 < unitCornerCutChord tangentHalfAngle := by
    dsimp [unitCornerCutChord]
    linarith
  have unit_area_identity :
      unitCornerCutChord tangentHalfAngle ^ 2 *
          cornerCutAreaCoefficient tangentHalfAngle =
        unitCornerCutArea tangentHalfAngle := by
    dsimp [unitCornerCutChord, unitCornerCutArea, cornerCutAreaCoefficient]
    field_simp [ne_of_gt one_add_tangent_positive]
    ring
  let chord := unitCornerCutChord tangentHalfAngle + chordGrowth
  let area := chord ^ 2 * cornerCutAreaCoefficient tangentHalfAngle
  have chord_at_least_unit : unitCornerCutChord tangentHalfAngle ≤ chord := by
    dsimp [chord]
    linarith
  have chord_nonnegative : 0 ≤ chord :=
    unit_chord_positive.le.trans chord_at_least_unit
  have chord_sq_at_least :
      unitCornerCutChord tangentHalfAngle ^ 2 ≤ chord ^ 2 := by
    nlinarith
  have area_at_least_unit : unitCornerCutArea tangentHalfAngle ≤ area := by
    dsimp [area]
    rw [← unit_area_identity]
    exact mul_le_mul_of_nonneg_right chord_sq_at_least coefficient_positive.le
  dsimp only
  calc
    1 / 2 < unitCornerCutArea tangentHalfAngle +
        unitCornerCutChord tangentHalfAngle / 2 := by
      dsimp [unitCornerCutChord]
      linarith
    _ ≤ area + chord / 2 := by
      gcongr

lemma pinnedCutPolynomial_positive
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    0 <
      (1 - tangentHalfAngle) ^ 2 * (1 - tangentHalfAngle ^ 2) -
        2 *
          (tangentHalfAngle * (1 - tangentHalfAngle) ^ 2 -
            tangentHalfAngle / 5) := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_fifth_lt_one : Real.sqrt (1 / 5) < 1 := by nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have polynomial_identity :
      (1 - tangentHalfAngle) ^ 2 * (1 - tangentHalfAngle ^ 2) -
          2 *
            (tangentHalfAngle * (1 - tangentHalfAngle) ^ 2 -
              tangentHalfAngle / 5) =
        (1 - tangentHalfAngle) ^ 2 *
            (2 - (1 + tangentHalfAngle) ^ 2) +
          (2 / 5) * tangentHalfAngle := by ring
  rw [polynomial_identity]
  by_cases tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1
  · have square_at_most_two : (1 + tangentHalfAngle) ^ 2 ≤ 2 := by
      nlinarith
    have first_term_nonnegative :
        0 ≤ (1 - tangentHalfAngle) ^ 2 *
          (2 - (1 + tangentHalfAngle) ^ 2) := by positivity
    have second_term_positive : 0 < (2 / 5) * tangentHalfAngle := by positivity
    linarith
  · have root_bound : 41 / 100 < Real.sqrt 2 - 1 := by nlinarith
    have tangent_gt_lower : 41 / 100 < tangentHalfAngle := by
      exact root_bound.trans_le (le_of_not_ge tangent_at_most)
    have sqrt_fifth_gt : 11 / 25 < Real.sqrt (1 / 5) := by nlinarith
    have tangent_lt_upper : tangentHalfAngle < 14 / 25 := by linarith
    let firstFactor := (1 - tangentHalfAngle) ^ 2
    let secondFactor := 2 - (1 + tangentHalfAngle) ^ 2
    have first_factor_nonnegative : 0 ≤ firstFactor := by
      dsimp [firstFactor]
      positivity
    have first_factor_at_most : firstFactor ≤ (59 / 100) ^ 2 := by
      dsimp [firstFactor]
      nlinarith
    have second_factor_lower :
        2 - (39 / 25) ^ 2 < secondFactor := by
      dsimp [secondFactor]
      nlinarith
    by_cases second_factor_nonnegative : 0 ≤ secondFactor
    · have first_term_nonnegative : 0 ≤ firstFactor * secondFactor := by positivity
      have second_term_positive : 0 < (2 / 5) * tangentHalfAngle := by positivity
      linarith
    · have second_factor_negative : secondFactor < 0 := lt_of_not_ge second_factor_nonnegative
      have product_at_least_scaled :
          (59 / 100) ^ 2 * secondFactor ≤ firstFactor * secondFactor := by
        exact mul_le_mul_of_nonpos_right first_factor_at_most second_factor_negative.le
      have lower_constant_nonnegative : 0 ≤ (59 / 100 : ℝ) ^ 2 := by positivity
      have scaled_gt_constant :
          (59 / 100) ^ 2 * (2 - (39 / 25) ^ 2) <
            (59 / 100) ^ 2 * secondFactor := by
        exact mul_lt_mul_of_pos_left second_factor_lower (by positivity)
      have product_lower :
          (59 / 100) ^ 2 * (2 - (39 / 25) ^ 2) <
            firstFactor * secondFactor :=
        scaled_gt_constant.trans_le product_at_least_scaled
      have linear_lower :
          (2 / 5) * (41 / 100) < (2 / 5) * tangentHalfAngle := by
        nlinarith
      have constant_sum_positive :
          0 <
            (59 / 100 : ℝ) ^ 2 * (2 - (39 / 25) ^ 2) +
              (2 / 5) * (41 / 100) := by norm_num
      change 0 < firstFactor * secondFactor + (2 / 5) * tangentHalfAngle
      linarith

noncomputable def pinnedCutArea (tangentHalfAngle : ℝ) : ℝ :=
  tangentHalfAngle * (1 - tangentHalfAngle) / (1 + tangentHalfAngle)

noncomputable def pinnedCutChord (tangentHalfAngle : ℝ) : ℝ :=
  (1 + tangentHalfAngle ^ 2) / (1 + tangentHalfAngle)

noncomputable def pinnedCutMissingLength (tangentHalfAngle : ℝ) : ℝ :=
  2 * tangentHalfAngle *
      (tangentHalfAngle * (1 - tangentHalfAngle) ^ 2 - tangentHalfAngle / 5) /
    (1 - tangentHalfAngle ^ 2) ^ 2

lemma pinnedCut_score_gt_one
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    1 <
      pinnedCutArea tangentHalfAngle + pinnedCutChord tangentHalfAngle / 2 +
        1 / 2 - pinnedCutMissingLength tangentHalfAngle / 2 := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_fifth_positive : 0 < Real.sqrt (1 / 5) := by nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have one_add_tangent_positive : 0 < 1 + tangentHalfAngle := by linarith
  have one_minus_tangent_sq_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
    nlinarith
  have area_add_chord :
      pinnedCutArea tangentHalfAngle + pinnedCutChord tangentHalfAngle = 1 := by
    dsimp [pinnedCutArea, pinnedCutChord]
    field_simp [ne_of_gt one_add_tangent_positive]
    ring
  have area_gt_missing :
      pinnedCutMissingLength tangentHalfAngle < pinnedCutArea tangentHalfAngle := by
    have polynomial_positive := pinnedCutPolynomial_positive tangent_positive tangent_lt
    dsimp [pinnedCutMissingLength, pinnedCutArea]
    rw [div_lt_div_iff₀ (sq_pos_of_pos one_minus_tangent_sq_positive)
      one_add_tangent_positive]
    field_simp [ne_of_gt one_add_tangent_positive]
    nlinarith
  linarith

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

lemma score_gt_one_of_two_boundaryLine_chords
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    {firstSide secondSide : NagamochiResource.BoundarySide}
    (factor_gt_one : 1 < factor)
    (different_sides : firstSide ≠ secondSide)
    (first_chord :
      ENNReal.ofReal factor ≤
        NagamochiResource.boundaryLine size firstSide region)
    (second_chord :
      ENNReal.ofReal factor ≤
        NagamochiResource.boundaryLine size secondSide region) :
    1 < NagamochiResource.measure size region := by
  have factor_score_gt_one : 1 < ENNReal.ofReal factor := by
    rw [ENNReal.one_lt_ofReal]
    exact factor_gt_one
  have pair_subset :
      ({firstSide, secondSide} : Finset NagamochiResource.BoundarySide) ⊆
        NagamochiResource.boundarySides := by
    intro side side_mem
    exact NagamochiResource.mem_boundarySides side
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := region) pair_subset
  have half_times_two : (2 : ENNReal)⁻¹ * 2 = 1 := by
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    1 < ENNReal.ofReal factor := factor_score_gt_one
    _ = (1 / 2 : ENNReal) *
        (ENNReal.ofReal factor + ENNReal.ofReal factor) := by
      rw [show (1 / 2 : ENNReal) = 2⁻¹ by norm_num]
      calc
        ENNReal.ofReal factor = 1 * ENNReal.ofReal factor := by rw [one_mul]
        _ = (2⁻¹ * 2) * ENNReal.ofReal factor := by rw [half_times_two]
        _ = 2⁻¹ *
            (ENNReal.ofReal factor + ENNReal.ofReal factor) := by ring
    _ ≤ (1 / 2 : ENNReal) *
        (NagamochiResource.boundaryLine size firstSide region +
          NagamochiResource.boundaryLine size secondSide region) := by
      exact mul_le_mul le_rfl (add_le_add first_chord second_chord) bot_le bot_le
    _ = (1 / 2 : ENNReal) *
        (∑ side ∈ ({firstSide, secondSide} :
          Finset NagamochiResource.BoundarySide),
            NagamochiResource.boundaryLine size side region) := by
      rw [Finset.sum_pair different_sides]
    _ ≤ NagamochiResource.boundaryLines size region := pair_bound
    _ ≤ NagamochiResource.measure size region :=
      NagamochiResource.boundaryLines_le_measure size region

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
