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

lemma Frame.exists_tangentHalfAngle_of_sine_le_cosine
    (frame : Frame)
    (cosine_positive : 0 < frame.cosine)
    (sine_positive : 0 < frame.sine)
    (sine_le_cosine : frame.sine ≤ frame.cosine) :
    ∃ tangentHalfAngle : ℝ,
      0 < tangentHalfAngle ∧
        tangentHalfAngle ≤ Real.sqrt 2 - 1 ∧
          frame.cosine =
            (1 - tangentHalfAngle ^ 2) /
              (1 + tangentHalfAngle ^ 2) ∧
          frame.sine =
            2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2) := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_two_gt_one : 1 < Real.sqrt 2 := by nlinarith
  have sine_sq_le_cosine_sq : frame.sine ^ 2 ≤ frame.cosine ^ 2 := by
    nlinarith
  have twice_sine_sq_le_one : 2 * frame.sine ^ 2 ≤ 1 := by
    nlinarith [frame.unit]
  have sqrt_two_mul_sine_le_one : Real.sqrt 2 * frame.sine ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt 2 * frame.sine - 1)]
  have tangent_bound_numerator :
      frame.sine ≤
        (Real.sqrt 2 - 1) * (1 + frame.cosine) := by
    have base_bound :
        frame.sine ≤
          (Real.sqrt 2 - 1) * (1 + frame.sine) := by
      nlinarith
    have coefficient_nonnegative : 0 ≤ Real.sqrt 2 - 1 := by linarith
    have scaled_order :
        (Real.sqrt 2 - 1) * (1 + frame.sine) ≤
          (Real.sqrt 2 - 1) * (1 + frame.cosine) := by
      exact mul_le_mul_of_nonneg_left (by linarith) coefficient_nonnegative
    exact base_bound.trans scaled_order
  let tangentHalfAngle := frame.sine / (1 + frame.cosine)
  have denominator_positive : 0 < 1 + frame.cosine := by linarith
  have tangent_positive : 0 < tangentHalfAngle := by
    dsimp [tangentHalfAngle]
    positivity
  have tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1 := by
    dsimp [tangentHalfAngle]
    exact (div_le_iff₀ denominator_positive).2 tangent_bound_numerator
  refine ⟨tangentHalfAngle, tangent_positive, tangent_at_most, ?_, ?_⟩
  · dsimp [tangentHalfAngle]
    field_simp [denominator_positive.ne']
    nlinarith [frame.unit]
  · dsimp [tangentHalfAngle]
    field_simp [denominator_positive.ne']
    nlinarith [frame.unit]

lemma horizontalAdjacentChord_length_gt_one
    (square : PlacedSquare) {factor height offset tangentHalfAngle : ℝ}
    (factor_at_least_one : 1 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cosine_eq :
      square.frame.cosine =
        (1 - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle ^ 2))
    (sine_eq :
      square.frame.sine =
        2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2))
    (vertical_offset : height - factor * square.center.y = -offset)
    (offset_nonnegative : 0 ≤ offset)
    (offset_lt : offset < (Real.sqrt 2 - 1) / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    1 <
      square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt_two_lt_two : Real.sqrt 2 < 2 := by nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have tangent_sq_lt_one : tangentHalfAngle ^ 2 < 1 := by nlinarith
  have one_add_tangent_sq_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have denominator_positive :
      0 < 2 * square.frame.sine * square.frame.cosine := by positivity
  have cosine_add_sine_positive :
      0 < square.frame.cosine + square.frame.sine := by linarith
  have base_expression_eq :
      (square.frame.cosine + square.frame.sine - 2 * offset) /
          (2 * square.frame.sine * square.frame.cosine) =
        centeredAdjacentChordLength offset tangentHalfAngle := by
    rw [cosine_eq, sine_eq]
    dsimp [centeredAdjacentChordLength]
    field_simp [tangent_positive.ne', ne_of_gt one_add_tangent_sq_positive,
      ne_of_gt (sub_pos.mpr tangent_sq_lt_one)]
    ring
  have base_gt_one :
      1 <
        (square.frame.cosine + square.frame.sine - 2 * offset) /
          (2 * square.frame.sine * square.frame.cosine) := by
    rw [base_expression_eq]
    exact centeredAdjacentChordLength_gt_one offset_nonnegative offset_lt
      tangent_positive tangent_at_most
  rw [square.horizontalAdjacentChord_length
    cosine_positive.ne' sine_positive.ne', vertical_offset]
  have base_le_scaled :
      (square.frame.cosine + square.frame.sine - 2 * offset) /
          (2 * square.frame.sine * square.frame.cosine) ≤
        (factor * (square.frame.cosine + square.frame.sine) + 2 * -offset) /
          (2 * square.frame.sine * square.frame.cosine) := by
    apply div_le_div_of_nonneg_right
    · nlinarith
    · exact denominator_positive.le
  exact base_gt_one.trans_le base_le_scaled

lemma horizontalAdjacentChord_length_gt_one_of_center_at_most_line
    (square : PlacedSquare) {factor height : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_at_most_line : factor * square.center.y ≤ height) :
    1 <
      square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height := by
  have cosine_at_most_one : square.frame.cosine ≤ 1 := by
    nlinarith [square.frame.unit]
  have sine_at_most_one : square.frame.sine ≤ 1 := by
    nlinarith [square.frame.unit]
  have first_product_nonnegative :
      0 ≤ square.frame.cosine * (1 - square.frame.sine) := by
    positivity
  have second_product_nonnegative :
      0 ≤ square.frame.sine * (1 - square.frame.cosine) := by
    positivity
  have twice_product_at_most_sum :
      2 * square.frame.sine * square.frame.cosine ≤
        square.frame.cosine + square.frame.sine := by
    nlinarith
  have component_sum_positive :
      0 < square.frame.cosine + square.frame.sine := by linarith
  have scaled_sum_gt_denominator :
      2 * square.frame.sine * square.frame.cosine <
        factor * (square.frame.cosine + square.frame.sine) := by
    nlinarith
  rw [square.horizontalAdjacentChord_length
    cosine_positive.ne' sine_positive.ne']
  rw [lt_div_iff₀ (by positivity :
    0 < 2 * square.frame.sine * square.frame.cosine)]
  nlinarith

lemma horizontalAdjacentChord_length_gt_one_any_positive_frame
    (square : PlacedSquare) {factor height offset : ℝ}
    (factor_at_least_one : 1 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (vertical_offset : height - factor * square.center.y = -offset)
    (offset_nonnegative : 0 ≤ offset)
    (offset_lt : offset < (Real.sqrt 2 - 1) / 2) :
    1 <
      square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height := by
  by_cases sine_le_cosine : square.frame.sine ≤ square.frame.cosine
  · obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
        cosine_eq, sine_eq⟩ :=
      Frame.exists_tangentHalfAngle_of_sine_le_cosine square.frame
        cosine_positive sine_positive sine_le_cosine
    exact horizontalAdjacentChord_length_gt_one square factor_at_least_one
      cosine_positive sine_positive cosine_eq sine_eq vertical_offset
      offset_nonnegative offset_lt tangent_positive tangent_at_most
  · have cosine_le_sine : square.frame.cosine ≤ square.frame.sine :=
      le_of_not_ge sine_le_cosine
    let swappedFrameSquare : PlacedSquare :=
      { center := square.center, frame := square.frame.swap }
    have swapped_cosine_positive :
        0 < swappedFrameSquare.frame.cosine := by
      simpa [swappedFrameSquare, Frame.swap] using sine_positive
    have swapped_sine_positive :
        0 < swappedFrameSquare.frame.sine := by
      simpa [swappedFrameSquare, Frame.swap] using cosine_positive
    have swapped_sine_le_cosine :
        swappedFrameSquare.frame.sine ≤
          swappedFrameSquare.frame.cosine := by
      simpa [swappedFrameSquare, Frame.swap] using cosine_le_sine
    obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
        cosine_eq, sine_eq⟩ :=
      Frame.exists_tangentHalfAngle_of_sine_le_cosine
        swappedFrameSquare.frame swapped_cosine_positive
        swapped_sine_positive swapped_sine_le_cosine
    have swapped_vertical_offset :
        height - factor * swappedFrameSquare.center.y = -offset := by
      simpa [swappedFrameSquare] using vertical_offset
    have swapped_length_gt_one := horizontalAdjacentChord_length_gt_one
      swappedFrameSquare factor_at_least_one swapped_cosine_positive
      swapped_sine_positive cosine_eq sine_eq swapped_vertical_offset
      offset_nonnegative offset_lt tangent_positive tangent_at_most
    have chord_lengths_eq :
        square.horizontalAdjacentChordEnd factor height -
            square.horizontalAdjacentChordStart factor height =
          swappedFrameSquare.horizontalAdjacentChordEnd factor height -
            swappedFrameSquare.horizontalAdjacentChordStart factor height := by
      rw [square.horizontalAdjacentChord_length cosine_positive.ne'
        sine_positive.ne']
      rw [swappedFrameSquare.horizontalAdjacentChord_length
        swapped_cosine_positive.ne' swapped_sine_positive.ne']
      simp only [swappedFrameSquare, Frame.swap]
      ring
    rw [chord_lengths_eq]
    exact swapped_length_gt_one

lemma bottomBoundaryChord_of_horizontalAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor 1 ≤
        square.horizontalAdjacentChordStart factor 1)
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor 1 ≤
        square.horizontalAdjacentOtherUpper factor 1)
    (chord_inside_segment :
      Ioo (square.horizontalAdjacentChordStart factor 1)
          (square.horizontalAdjacentChordEnd factor 1) ⊆
        Icc (9 / 10) ((size : ℝ) - 9 / 10)) :
    NagamochiResource.HasBoundaryChord size .bottom
      (square.dilatedInteriorRegion factor)
      (square.horizontalAdjacentChordEnd factor 1 -
        square.horizontalAdjacentChordStart factor 1) := by
  exact ⟨square.horizontalAdjacentChordStart factor 1,
    square.horizontalAdjacentChordEnd factor 1, le_rfl, chord_inside_segment,
    square.horizontalAdjacentChord_inside_dilatedInteriorRegion
      factor_positive cosine_positive sine_positive
      other_lower_at_most end_at_most_other_upper⟩

lemma topBoundaryChord_of_horizontalAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor ((size : ℝ) - 1) ≤
        square.horizontalAdjacentChordStart factor ((size : ℝ) - 1))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor ((size : ℝ) - 1) ≤
        square.horizontalAdjacentOtherUpper factor ((size : ℝ) - 1))
    (chord_inside_segment :
      Ioo (square.horizontalAdjacentChordStart factor ((size : ℝ) - 1))
          (square.horizontalAdjacentChordEnd factor ((size : ℝ) - 1)) ⊆
        Icc (9 / 10) ((size : ℝ) - 9 / 10)) :
    NagamochiResource.HasBoundaryChord size .top
      (square.dilatedInteriorRegion factor)
      (square.horizontalAdjacentChordEnd factor ((size : ℝ) - 1) -
        square.horizontalAdjacentChordStart factor ((size : ℝ) - 1)) := by
  exact ⟨square.horizontalAdjacentChordStart factor ((size : ℝ) - 1),
    square.horizontalAdjacentChordEnd factor ((size : ℝ) - 1),
    le_rfl, chord_inside_segment,
    square.horizontalAdjacentChord_inside_dilatedInteriorRegion
      factor_positive cosine_positive sine_positive
      other_lower_at_most end_at_most_other_upper⟩

def HasHorizontalOppositeChordWithin
    (size : ℕ) (square : PlacedSquare) (factor height : ℝ) : Prop :=
  (square.horizontalAdjacentOtherLower factor height ≤
      square.horizontalAdjacentChordStart factor height ∧
    square.horizontalAdjacentOtherUpper factor height ≤
      square.horizontalAdjacentChordEnd factor height ∧
    Ioo (square.horizontalAdjacentChordStart factor height)
        (square.horizontalAdjacentOtherUpper factor height) ⊆
      Icc (9 / 10) ((size : ℝ) - 9 / 10)) ∨
  (square.horizontalAdjacentChordStart factor height ≤
      square.horizontalAdjacentOtherLower factor height ∧
    square.horizontalAdjacentChordEnd factor height ≤
      square.horizontalAdjacentOtherUpper factor height ∧
    Ioo (square.horizontalAdjacentOtherLower factor height)
        (square.horizontalAdjacentChordEnd factor height) ⊆
      Icc (9 / 10) ((size : ℝ) - 9 / 10))

lemma bottomBoundaryChord_of_horizontalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite : HasHorizontalOppositeChordWithin size square factor 1) :
    NagamochiResource.HasBoundaryChord size .bottom
      (square.dilatedInteriorRegion factor) factor := by
  rcases opposite with
    ⟨y_lower_at_most_x_lower, x_upper_at_most_y_upper, chord_inside_segment⟩ |
      ⟨x_lower_at_most_y_lower, y_upper_at_most_x_upper, chord_inside_segment⟩
  · exact ⟨square.horizontalAdjacentChordStart factor 1,
      square.horizontalAdjacentOtherUpper factor 1,
      square.horizontalCosineChord_length_at_least_factor
        factor_positive.le cosine_positive,
      chord_inside_segment,
      square.horizontalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        y_lower_at_most_x_lower x_upper_at_most_y_upper⟩
  · exact ⟨square.horizontalAdjacentOtherLower factor 1,
      square.horizontalAdjacentChordEnd factor 1,
      square.horizontalSineChord_length_at_least_factor
        factor_positive.le sine_positive,
      chord_inside_segment,
      square.horizontalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        x_lower_at_most_y_lower y_upper_at_most_x_upper⟩

lemma topBoundaryChord_of_horizontalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite :
      HasHorizontalOppositeChordWithin size square factor ((size : ℝ) - 1)) :
    NagamochiResource.HasBoundaryChord size .top
      (square.dilatedInteriorRegion factor) factor := by
  rcases opposite with
    ⟨y_lower_at_most_x_lower, x_upper_at_most_y_upper, chord_inside_segment⟩ |
      ⟨x_lower_at_most_y_lower, y_upper_at_most_x_upper, chord_inside_segment⟩
  · exact ⟨square.horizontalAdjacentChordStart factor ((size : ℝ) - 1),
      square.horizontalAdjacentOtherUpper factor ((size : ℝ) - 1),
      square.horizontalCosineChord_length_at_least_factor
        factor_positive.le cosine_positive,
      chord_inside_segment,
      square.horizontalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        y_lower_at_most_x_lower x_upper_at_most_y_upper⟩
  · exact ⟨square.horizontalAdjacentOtherLower factor ((size : ℝ) - 1),
      square.horizontalAdjacentChordEnd factor ((size : ℝ) - 1),
      square.horizontalSineChord_length_at_least_factor
        factor_positive.le sine_positive,
      chord_inside_segment,
      square.horizontalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        x_lower_at_most_y_lower y_upper_at_most_x_upper⟩

def HasVerticalOppositeChordWithin
    (size : ℕ) (square : PlacedSquare) (factor width : ℝ) : Prop :=
  (square.verticalAdjacentOtherLower factor width ≤
      square.verticalAdjacentChordStart factor width ∧
    square.verticalAdjacentOtherUpper factor width ≤
      square.verticalAdjacentChordEnd factor width ∧
    Ioo (square.verticalAdjacentChordStart factor width)
        (square.verticalAdjacentOtherUpper factor width) ⊆
      Icc (9 / 10) ((size : ℝ) - 9 / 10)) ∨
  (square.verticalAdjacentChordStart factor width ≤
      square.verticalAdjacentOtherLower factor width ∧
    square.verticalAdjacentChordEnd factor width ≤
      square.verticalAdjacentOtherUpper factor width ∧
    Ioo (square.verticalAdjacentOtherLower factor width)
        (square.verticalAdjacentChordEnd factor width) ⊆
      Icc (9 / 10) ((size : ℝ) - 9 / 10))

lemma leftBoundaryChord_of_verticalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite : HasVerticalOppositeChordWithin size square factor 1) :
    NagamochiResource.HasBoundaryChord size .left
      (square.dilatedInteriorRegion factor) factor := by
  rcases opposite with
    ⟨second_lower_at_most_first_lower, first_upper_at_most_second_upper,
      chord_inside_segment⟩ |
      ⟨first_lower_at_most_second_lower, second_upper_at_most_first_upper,
        chord_inside_segment⟩
  · exact ⟨square.verticalAdjacentChordStart factor 1,
      square.verticalAdjacentOtherUpper factor 1,
      square.verticalSineChord_length_at_least_factor
        factor_positive.le sine_positive,
      chord_inside_segment,
      square.verticalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        second_lower_at_most_first_lower first_upper_at_most_second_upper⟩
  · exact ⟨square.verticalAdjacentOtherLower factor 1,
      square.verticalAdjacentChordEnd factor 1,
      square.verticalCosineChord_length_at_least_factor
        factor_positive.le cosine_positive,
      chord_inside_segment,
      square.verticalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        first_lower_at_most_second_lower second_upper_at_most_first_upper⟩

lemma rightBoundaryChord_of_verticalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite :
      HasVerticalOppositeChordWithin size square factor ((size : ℝ) - 1)) :
    NagamochiResource.HasBoundaryChord size .right
      (square.dilatedInteriorRegion factor) factor := by
  rcases opposite with
    ⟨second_lower_at_most_first_lower, first_upper_at_most_second_upper,
      chord_inside_segment⟩ |
      ⟨first_lower_at_most_second_lower, second_upper_at_most_first_upper,
        chord_inside_segment⟩
  · exact ⟨square.verticalAdjacentChordStart factor ((size : ℝ) - 1),
      square.verticalAdjacentOtherUpper factor ((size : ℝ) - 1),
      square.verticalSineChord_length_at_least_factor
        factor_positive.le sine_positive,
      chord_inside_segment,
      square.verticalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        second_lower_at_most_first_lower first_upper_at_most_second_upper⟩
  · exact ⟨square.verticalAdjacentOtherLower factor ((size : ℝ) - 1),
      square.verticalAdjacentChordEnd factor ((size : ℝ) - 1),
      square.verticalCosineChord_length_at_least_factor
        factor_positive.le cosine_positive,
      chord_inside_segment,
      square.verticalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        first_lower_at_most_second_lower second_upper_at_most_first_upper⟩

def HasOppositeBoundaryChord
    (size : ℕ) (square : PlacedSquare) (factor : ℝ) :
    NagamochiResource.BoundarySide → Prop
  | .bottom => HasHorizontalOppositeChordWithin size square factor 1
  | .top =>
      HasHorizontalOppositeChordWithin size square factor ((size : ℝ) - 1)
  | .left => HasVerticalOppositeChordWithin size square factor 1
  | .right =>
      HasVerticalOppositeChordWithin size square factor ((size : ℝ) - 1)

lemma boundaryChord_of_opposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (side : NagamochiResource.BoundarySide)
    (opposite : HasOppositeBoundaryChord size square factor side) :
    NagamochiResource.HasBoundaryChord size side
      (square.dilatedInteriorRegion factor) factor := by
  cases side with
  | bottom =>
      exact bottomBoundaryChord_of_horizontalOpposite square factor_positive
        cosine_positive sine_positive opposite
  | top =>
      exact topBoundaryChord_of_horizontalOpposite square factor_positive
        cosine_positive sine_positive opposite
  | left =>
      exact leftBoundaryChord_of_verticalOpposite square factor_positive
        cosine_positive sine_positive opposite
  | right =>
      exact rightBoundaryChord_of_verticalOpposite square factor_positive
        cosine_positive sine_positive opposite

lemma boundaryChord_of_pointAt_mem
    {size : ℕ} {region : Set Plane}
    {intervalStart intervalEnd minimumLength : ℝ}
    (side : NagamochiResource.BoundarySide)
    (region_convex : Convex ℝ region)
    (intervalStart_lt_intervalEnd : intervalStart < intervalEnd)
    (minimum_length : minimumLength ≤ intervalEnd - intervalStart)
    (inside_boundary_segment :
      Ioo intervalStart intervalEnd ⊆
        Icc (9 / 10) ((size : ℝ) - 9 / 10))
    (start_mem : side.pointAt size intervalStart ∈ region)
    (end_mem : side.pointAt size intervalEnd ∈ region) :
    NagamochiResource.HasBoundaryChord size side region minimumLength := by
  cases side with
  | bottom =>
      exact ⟨intervalStart, intervalEnd, minimum_length,
        inside_boundary_segment,
        horizontal_openSegment_subset_of_convex region_convex
          intervalStart_lt_intervalEnd
          (by simpa [NagamochiResource.BoundarySide.pointAt] using start_mem)
          (by simpa [NagamochiResource.BoundarySide.pointAt] using end_mem)⟩
  | top =>
      exact ⟨intervalStart, intervalEnd, minimum_length,
        inside_boundary_segment,
        horizontal_openSegment_subset_of_convex region_convex
          intervalStart_lt_intervalEnd
          (by simpa [NagamochiResource.BoundarySide.pointAt] using start_mem)
          (by simpa [NagamochiResource.BoundarySide.pointAt] using end_mem)⟩
  | left =>
      exact ⟨intervalStart, intervalEnd, minimum_length,
        inside_boundary_segment,
        vertical_openSegment_subset_of_convex region_convex
          intervalStart_lt_intervalEnd
          (by simpa [NagamochiResource.BoundarySide.pointAt] using start_mem)
          (by simpa [NagamochiResource.BoundarySide.pointAt] using end_mem)⟩
  | right =>
      exact ⟨intervalStart, intervalEnd, minimum_length,
        inside_boundary_segment,
        vertical_openSegment_subset_of_convex region_convex
          intervalStart_lt_intervalEnd
          (by simpa [NagamochiResource.BoundarySide.pointAt] using start_mem)
          (by simpa [NagamochiResource.BoundarySide.pointAt] using end_mem)⟩

lemma firstBoundaryChord_of_corner_and_unit_point
    {size : ℕ} {region : Set Plane}
    (size_at_least_three : 3 ≤ size)
    (side : NagamochiResource.BoundarySide)
    (region_convex : Convex ℝ region)
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region)
    (unit_point_mem : side.pointAt size 1 ∈ region) :
    NagamochiResource.HasBoundaryChord size side region (1 / 10) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have corner_point_at_mem : side.pointAt size (9 / 10) ∈ region := by
    simpa using corner_point_mem
  exact boundaryChord_of_pointAt_mem side region_convex (by norm_num)
    (by norm_num)
    (fun _ point_mem => ⟨point_mem.1.le, by linarith [point_mem.2]⟩)
    corner_point_at_mem unit_point_mem

lemma secondBoundaryChord_of_unit_and_corner_point
    {size : ℕ} {region : Set Plane}
    (size_at_least_three : 3 ≤ size)
    (side : NagamochiResource.BoundarySide)
    (region_convex : Convex ℝ region)
    (unit_point_mem : side.pointAt size ((size : ℝ) - 1) ∈ region)
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region) :
    NagamochiResource.HasBoundaryChord size side region (1 / 10) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have corner_point_at_mem :
      side.pointAt size ((size : ℝ) - 9 / 10) ∈ region := by
    simpa using corner_point_mem
  exact boundaryChord_of_pointAt_mem side region_convex (by norm_num)
    (by norm_num)
    (fun _ point_mem => ⟨by linarith [point_mem.1], point_mem.2.le⟩)
    unit_point_mem corner_point_at_mem

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

lemma horizontalOtherAdjacentChord_length_gt_one_of_bottom_contained
    (square : PlacedSquare) {factor height tangentHalfAngle : ℝ}
    (factor_at_least_one : 1 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cosine_eq :
      square.frame.cosine =
        (1 - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle ^ 2))
    (sine_eq :
      square.frame.sine =
        2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2))
    (bottom_contained :
      factor * (square.frame.cosine + square.frame.sine) / 2 ≤
        factor * square.center.y)
    (height_gt_half : 1 / 2 < height)
    (height_lt : height < Real.sqrt 2 - 1 / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    1 <
      square.horizontalAdjacentOtherUpper factor height -
        square.horizontalAdjacentOtherLower factor height := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_two_lt_two : Real.sqrt 2 < 2 := by nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have tangent_sq_lt_one : tangentHalfAngle ^ 2 < 1 := by nlinarith
  have one_add_tangent_sq_positive : 0 < 1 + tangentHalfAngle ^ 2 := by
    positivity
  have cosine_add_sine_positive :
      0 < square.frame.cosine + square.frame.sine := by linarith
  have base_expression_eq :
      (square.frame.cosine + square.frame.sine - height) /
          (square.frame.sine * square.frame.cosine) =
        cornerAdjacentChordLength height tangentHalfAngle := by
    rw [cosine_eq, sine_eq]
    dsimp [cornerAdjacentChordLength]
    field_simp [tangent_positive.ne', ne_of_gt one_add_tangent_sq_positive,
      ne_of_gt (sub_pos.mpr tangent_sq_lt_one)]
    ring
  have base_gt_one :
      1 <
        (square.frame.cosine + square.frame.sine - height) /
          (square.frame.sine * square.frame.cosine) := by
    rw [base_expression_eq]
    exact cornerAdjacentChordLength_gt_one height_gt_half height_lt
      tangent_positive tangent_at_most
  rw [square.horizontalOtherAdjacentChord_length
    cosine_positive.ne' sine_positive.ne']
  have base_common_denominator :
      (square.frame.cosine + square.frame.sine - height) /
          (square.frame.sine * square.frame.cosine) =
        (2 * (square.frame.cosine + square.frame.sine - height)) /
          (2 * square.frame.sine * square.frame.cosine) := by
    field_simp [cosine_positive.ne', sine_positive.ne']
  rw [base_common_denominator] at base_gt_one
  have base_le_actual :
      (2 * (square.frame.cosine + square.frame.sine - height)) /
          (2 * square.frame.sine * square.frame.cosine) ≤
        (factor * (square.frame.cosine + square.frame.sine) -
          2 * (height - factor * square.center.y)) /
            (2 * square.frame.sine * square.frame.cosine) := by
    apply div_le_div_of_nonneg_right
    · nlinarith
    · positivity
  exact base_gt_one.trans_le base_le_actual

lemma horizontalOtherAdjacentChord_length_gt_one
    (square : PlacedSquare) {factor height tangentHalfAngle : ℝ}
    (factor_at_least_one : 1 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cosine_eq :
      square.frame.cosine =
        (1 - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle ^ 2))
    (sine_eq :
      square.frame.sine =
        2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2))
    (bottom_touch :
      factor * square.center.y =
        factor * (square.frame.cosine + square.frame.sine) / 2)
    (height_gt_half : 1 / 2 < height)
    (height_lt : height < Real.sqrt 2 - 1 / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    1 <
      square.horizontalAdjacentOtherUpper factor height -
        square.horizontalAdjacentOtherLower factor height := by
  exact horizontalOtherAdjacentChord_length_gt_one_of_bottom_contained square
    factor_at_least_one cosine_positive sine_positive cosine_eq sine_eq
    bottom_touch.ge height_gt_half height_lt tangent_positive tangent_at_most

lemma horizontalOtherAdjacentChord_length_gt_one_any_positive_frame
    (square : PlacedSquare) {factor height : ℝ}
    (factor_at_least_one : 1 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (bottom_contained :
      factor * (square.frame.cosine + square.frame.sine) / 2 ≤
        factor * square.center.y)
    (height_gt_half : 1 / 2 < height)
    (height_lt : height < Real.sqrt 2 - 1 / 2) :
    1 <
      square.horizontalAdjacentOtherUpper factor height -
        square.horizontalAdjacentOtherLower factor height := by
  by_cases sine_le_cosine : square.frame.sine ≤ square.frame.cosine
  · obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
        cosine_eq, sine_eq⟩ :=
      Frame.exists_tangentHalfAngle_of_sine_le_cosine square.frame
        cosine_positive sine_positive sine_le_cosine
    exact horizontalOtherAdjacentChord_length_gt_one_of_bottom_contained square
      factor_at_least_one cosine_positive sine_positive cosine_eq sine_eq
      bottom_contained height_gt_half height_lt tangent_positive tangent_at_most
  · have cosine_le_sine : square.frame.cosine ≤ square.frame.sine :=
      le_of_not_ge sine_le_cosine
    let swappedFrameSquare : PlacedSquare :=
      { center := square.center, frame := square.frame.swap }
    have swapped_cosine_positive :
        0 < swappedFrameSquare.frame.cosine := by
      simpa [swappedFrameSquare, Frame.swap] using sine_positive
    have swapped_sine_positive :
        0 < swappedFrameSquare.frame.sine := by
      simpa [swappedFrameSquare, Frame.swap] using cosine_positive
    have swapped_sine_le_cosine :
        swappedFrameSquare.frame.sine ≤
          swappedFrameSquare.frame.cosine := by
      simpa [swappedFrameSquare, Frame.swap] using cosine_le_sine
    have swapped_bottom_contained :
        factor * (swappedFrameSquare.frame.cosine +
            swappedFrameSquare.frame.sine) / 2 ≤
          factor * swappedFrameSquare.center.y := by
      simpa [swappedFrameSquare, Frame.swap, add_comm] using bottom_contained
    obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
        cosine_eq, sine_eq⟩ :=
      Frame.exists_tangentHalfAngle_of_sine_le_cosine
        swappedFrameSquare.frame swapped_cosine_positive
        swapped_sine_positive swapped_sine_le_cosine
    have swapped_length_gt_one :=
      horizontalOtherAdjacentChord_length_gt_one_of_bottom_contained
        swappedFrameSquare factor_at_least_one swapped_cosine_positive
        swapped_sine_positive cosine_eq sine_eq swapped_bottom_contained
        height_gt_half height_lt tangent_positive tangent_at_most
    have chord_lengths_eq :
        square.horizontalAdjacentOtherUpper factor height -
            square.horizontalAdjacentOtherLower factor height =
          swappedFrameSquare.horizontalAdjacentOtherUpper factor height -
            swappedFrameSquare.horizontalAdjacentOtherLower factor height := by
      rw [square.horizontalOtherAdjacentChord_length cosine_positive.ne'
        sine_positive.ne']
      rw [swappedFrameSquare.horizontalOtherAdjacentChord_length
        swapped_cosine_positive.ne' swapped_sine_positive.ne']
      simp only [swappedFrameSquare, Frame.swap]
      ring
    rw [chord_lengths_eq]
    exact swapped_length_gt_one

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

noncomputable def pinnedBoundaryCornerScore (tangentHalfAngle : ℝ) : ℝ :=
  pinnedCutChord tangentHalfAngle / 2 + 1 / 2 -
    pinnedCutMissingLength tangentHalfAngle / 2

lemma pinnedCut_score_gt_one
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    1 <
      pinnedCutArea tangentHalfAngle +
        pinnedBoundaryCornerScore tangentHalfAngle := by
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
  dsimp [pinnedBoundaryCornerScore]
  linarith

lemma score_gt_one_of_real_grouped_bounds
    {size : ℕ} {region : Set Plane}
    {innerScore boundaryCornerScore edgeScore : ℝ}
    (inner_nonnegative : 0 ≤ innerScore)
    (boundary_corner_nonnegative : 0 ≤ boundaryCornerScore)
    (edge_nonnegative : 0 ≤ edgeScore)
    (score_gt_one : 1 < innerScore + boundaryCornerScore + edgeScore)
    (inner_bound :
      ENNReal.ofReal innerScore ≤ NagamochiResource.innerArea size region)
    (boundary_corner_bound :
      ENNReal.ofReal boundaryCornerScore ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region)
    (edge_bound :
      ENNReal.ofReal edgeScore ≤ NagamochiResource.edgePoints size region) :
    1 < NagamochiResource.measure size region := by
  have encoded_score_gt_one :
      1 < ENNReal.ofReal (innerScore + boundaryCornerScore + edgeScore) := by
    rw [ENNReal.one_lt_ofReal]
    exact score_gt_one
  have encoded_score_eq :
      ENNReal.ofReal (innerScore + boundaryCornerScore + edgeScore) =
        ENNReal.ofReal innerScore + ENNReal.ofReal boundaryCornerScore +
          ENNReal.ofReal edgeScore := by
    rw [ENNReal.ofReal_add (add_nonneg inner_nonnegative boundary_corner_nonnegative)
      edge_nonnegative]
    rw [ENNReal.ofReal_add inner_nonnegative boundary_corner_nonnegative]
  calc
    1 < ENNReal.ofReal (innerScore + boundaryCornerScore + edgeScore) :=
      encoded_score_gt_one
    _ = ENNReal.ofReal innerScore + ENNReal.ofReal boundaryCornerScore +
        ENNReal.ofReal edgeScore := encoded_score_eq
    _ ≤ NagamochiResource.innerArea size region +
          (NagamochiResource.boundaryLines size region +
            NagamochiResource.cornerPoints size region) +
        NagamochiResource.edgePoints size region :=
      add_le_add (add_le_add inner_bound boundary_corner_bound) edge_bound
    _ = NagamochiResource.measure size region := by
      simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
      ac_rfl

lemma score_gt_one_of_pinned_cut_bounds
    {size : ℕ} {region : Set Plane} {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5))
    (boundary_corner_nonnegative :
      0 ≤ pinnedBoundaryCornerScore tangentHalfAngle)
    (inner_bound :
      ENNReal.ofReal (pinnedCutArea tangentHalfAngle) ≤
        NagamochiResource.innerArea size region)
    (boundary_corner_bound :
      ENNReal.ofReal (pinnedBoundaryCornerScore tangentHalfAngle) ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region) :
    1 < NagamochiResource.measure size region := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have tangent_lt_one : tangentHalfAngle < 1 := by nlinarith
  have area_nonnegative : 0 ≤ pinnedCutArea tangentHalfAngle := by
    dsimp [pinnedCutArea]
    positivity
  apply score_gt_one_of_real_grouped_bounds
    (innerScore := pinnedCutArea tangentHalfAngle)
    (boundaryCornerScore := pinnedBoundaryCornerScore tangentHalfAngle)
    (edgeScore := 0)
    area_nonnegative boundary_corner_nonnegative (by norm_num)
    (by simpa using pinnedCut_score_gt_one tangent_positive tangent_lt)
    inner_bound boundary_corner_bound
  simp

lemma score_gt_one_of_boundary_chord_and_edge_point
    {size coordinate : ℕ} {region : Set Plane} {factor : ℝ}
    {side : NagamochiResource.BoundarySide}
    {kind : NagamochiResource.EdgePoint}
    (factor_gt_one : 1 < factor)
    (region_measurable : MeasurableSet region)
    (chord : NagamochiResource.HasBoundaryChord size side region factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have line_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
    region_measurable chord
  have boundary_bound :
      ENNReal.ofReal (factor / 2) ≤
        NagamochiResource.boundaryLines size region := by
    have scaled_bound := NagamochiResource.boundaryLines_lower_bound
      (size := size) (region := region) line_bound
    have encoded_half :
        ENNReal.ofReal (factor / 2) =
          (1 / 2 : ENNReal) * ENNReal.ofReal factor := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
      ac_rfl
    rw [encoded_half]
    exact scaled_bound
  have edge_bound :
      (1 / 2 : ENNReal) ≤ NagamochiResource.edgePoints size region :=
    NagamochiResource.edgePoints_lower_bound_of_mem kind coordinate_mem
      region_measurable point_mem
  have encoded_sum_gt_one :
      1 < ENNReal.ofReal (factor / 2) + (1 / 2 : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    norm_num
    linarith
  calc
    1 < ENNReal.ofReal (factor / 2) + (1 / 2 : ENNReal) :=
      encoded_sum_gt_one
    _ ≤ NagamochiResource.boundaryLines size region +
        NagamochiResource.edgePoints size region :=
      add_le_add boundary_bound edge_bound
    _ ≤ NagamochiResource.measure size region := by
      simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
      calc
        _ ≤ (NagamochiResource.innerArea size region +
              NagamochiResource.boundaryLines size region) +
            NagamochiResource.edgePoints size region :=
          add_le_add (le_add_of_nonneg_left bot_le) le_rfl
        _ ≤ ((NagamochiResource.innerArea size region +
                NagamochiResource.boundaryLines size region) +
              NagamochiResource.cornerPoints size region) +
            NagamochiResource.edgePoints size region :=
          add_le_add (le_add_of_nonneg_right bot_le) le_rfl

lemma score_gt_one_of_long_and_short_boundary_chords_and_corner_point
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    {longSide shortSide : NagamochiResource.BoundarySide}
    {cornerKind : NagamochiResource.CornerPoint}
    (factor_gt_one : 1 < factor)
    (different_sides : longSide ≠ shortSide)
    (region_measurable : MeasurableSet region)
    (long_chord :
      NagamochiResource.HasBoundaryChord size longSide region factor)
    (short_chord :
      NagamochiResource.HasBoundaryChord size shortSide region (1 / 10))
    (corner_point_mem :
      NagamochiResource.cornerPoint size cornerKind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have long_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable long_chord
  have short_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable short_chord
  have pair_subset :
      ({longSide, shortSide} : Finset NagamochiResource.BoundarySide) ⊆
        NagamochiResource.boundarySides := by
    intro side side_mem
    exact NagamochiResource.mem_boundarySides side
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := region) pair_subset
  rw [Finset.sum_pair different_sides] at pair_bound
  have boundary_bound :
      (1 / 2 : ENNReal) *
          (ENNReal.ofReal factor + ENNReal.ofReal (1 / 10 : ℝ)) ≤
        NagamochiResource.boundaryLines size region :=
    (mul_le_mul le_rfl (add_le_add long_line_bound short_line_bound)
      bot_le bot_le).trans pair_bound
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem
    cornerKind region_measurable corner_point_mem
  have encoded_score_eq :
      ENNReal.ofReal (factor / 2 + 1 / 2) =
        (1 / 2 : ENNReal) *
            (ENNReal.ofReal factor + ENNReal.ofReal (1 / 10 : ℝ)) +
          9 / 20 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal factor_positive.le]
    norm_num
    ring
  have boundary_corner_bound :
      ENNReal.ofReal (factor / 2 + 1 / 2) ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region := by
    rw [encoded_score_eq]
    exact add_le_add boundary_bound corner_bound
  apply score_gt_one_of_real_grouped_bounds
    (innerScore := 0) (boundaryCornerScore := factor / 2 + 1 / 2)
    (edgeScore := 0)
  · norm_num
  · positivity
  · norm_num
  · linarith
  · simp
  · exact boundary_corner_bound
  · simp

lemma score_gt_one_of_area_chord_and_edge_point
    {size coordinate : ℕ} {region : Set Plane} {area chordLength : ℝ}
    {side : NagamochiResource.BoundarySide}
    {kind : NagamochiResource.EdgePoint}
    (area_nonnegative : 0 ≤ area)
    (chord_nonnegative : 0 ≤ chordLength)
    (area_chord_gt_half : 1 / 2 < area + chordLength / 2)
    (region_measurable : MeasurableSet region)
    (inner_bound :
      ENNReal.ofReal area ≤ NagamochiResource.innerArea size region)
    (chord :
      NagamochiResource.HasBoundaryChord size side region chordLength)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have line_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
    region_measurable chord
  have scaled_bound := NagamochiResource.boundaryLines_lower_bound
    (size := size) (region := region) line_bound
  have boundary_bound :
      ENNReal.ofReal (chordLength / 2) ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region := by
    have encoded_half :
        ENNReal.ofReal (chordLength / 2) =
          (1 / 2 : ENNReal) * ENNReal.ofReal chordLength := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
      ac_rfl
    rw [encoded_half]
    exact scaled_bound.trans (le_add_of_nonneg_right bot_le)
  have edge_bound := NagamochiResource.edgePoints_lower_bound_of_mem kind
    coordinate_mem region_measurable point_mem
  apply score_gt_one_of_real_grouped_bounds
    (innerScore := area) (boundaryCornerScore := chordLength / 2)
    (edgeScore := 1 / 2)
  · exact area_nonnegative
  · positivity
  · norm_num
  · linarith
  · exact inner_bound
  · exact boundary_bound
  · simpa using edge_bound

lemma score_gt_one_of_case6_corner_cut_and_edge_point
    {size coordinate : ℕ} {region : Set Plane}
    {tangentHalfAngle chordGrowth : ℝ}
    {side : NagamochiResource.BoundarySide}
    {kind : NagamochiResource.EdgePoint}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1)
    (chord_growth_nonnegative : 0 ≤ chordGrowth)
    (region_measurable : MeasurableSet region)
    (inner_bound :
      ENNReal.ofReal
          ((unitCornerCutChord tangentHalfAngle + chordGrowth) ^ 2 *
            cornerCutAreaCoefficient tangentHalfAngle) ≤
        NagamochiResource.innerArea size region)
    (chord :
      NagamochiResource.HasBoundaryChord size side region
        (unitCornerCutChord tangentHalfAngle + chordGrowth))
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have one_add_tangent_positive : 0 < 1 + tangentHalfAngle := by linarith
  have one_minus_tangent_sq_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
    nlinarith
  have coefficient_positive :
      0 < cornerCutAreaCoefficient tangentHalfAngle := by
    dsimp [cornerCutAreaCoefficient]
    positivity
  have unit_area_positive : 0 < unitCornerCutArea tangentHalfAngle := by
    dsimp [unitCornerCutArea]
    exact div_pos (by nlinarith) one_add_tangent_positive
  have unit_chord_positive : 0 < unitCornerCutChord tangentHalfAngle := by
    dsimp [unitCornerCutChord]
    have unit_area_lt_one : unitCornerCutArea tangentHalfAngle < 1 := by
      rw [unitCornerCutArea, div_lt_one one_add_tangent_positive]
      nlinarith
    linarith
  have chord_nonnegative :
      0 ≤ unitCornerCutChord tangentHalfAngle + chordGrowth := by
    linarith
  have area_nonnegative :
      0 ≤ (unitCornerCutChord tangentHalfAngle + chordGrowth) ^ 2 *
        cornerCutAreaCoefficient tangentHalfAngle := by positivity
  exact score_gt_one_of_area_chord_and_edge_point area_nonnegative
    chord_nonnegative
    (cornerCut_area_add_half_chord_gt_half tangent_positive tangent_lt_one
      chord_growth_nonnegative)
    region_measurable inner_bound chord coordinate_mem point_mem

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

lemma score_gt_one_of_compensated_inner_area
    {size : ℕ} {region : Set Plane} {factor : ℝ} {loss : ENNReal}
    (factor_gt_one : 1 < factor)
    (inner_area_with_loss :
      ENNReal.ofReal (factor ^ 2) ≤
        NagamochiResource.innerArea size region + loss)
    (loss_compensated :
      loss ≤ NagamochiResource.boundaryLines size region) :
    1 < NagamochiResource.measure size region := by
  have factor_square_gt_one : 1 < factor ^ 2 := by nlinarith
  have area_score_gt_one : 1 < ENNReal.ofReal (factor ^ 2) := by
    rw [ENNReal.one_lt_ofReal]
    exact factor_square_gt_one
  calc
    1 < ENNReal.ofReal (factor ^ 2) := area_score_gt_one
    _ ≤ NagamochiResource.innerArea size region + loss := inner_area_with_loss
    _ ≤ NagamochiResource.innerArea size region +
        NagamochiResource.boundaryLines size region :=
      add_le_add le_rfl loss_compensated
    _ ≤ NagamochiResource.measure size region :=
      NagamochiResource.innerArea_add_boundaryLines_le_measure size region

lemma score_gt_one_of_positive_inner_and_boundary_corner
    {size : ℕ} {region : Set Plane}
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (boundary_corner_at_least_one :
      1 ≤ NagamochiResource.boundaryLines size region +
        NagamochiResource.cornerPoints size region) :
    1 < NagamochiResource.measure size region := by
  by_cases boundary_corner_top :
      NagamochiResource.boundaryLines size region +
        NagamochiResource.cornerPoints size region = ⊤
  · have components_top :
        NagamochiResource.innerArea size region +
              NagamochiResource.boundaryLines size region +
            NagamochiResource.cornerPoints size region = ⊤ := by
      rw [add_assoc, boundary_corner_top, add_top]
    have measure_top : NagamochiResource.measure size region = ⊤ := by
      apply top_unique
      rw [← components_top]
      exact NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure
        size region
    rw [measure_top]
    exact ENNReal.one_lt_top
  calc
    1 ≤ NagamochiResource.boundaryLines size region +
        NagamochiResource.cornerPoints size region :=
      boundary_corner_at_least_one
    _ = 0 + (NagamochiResource.boundaryLines size region +
        NagamochiResource.cornerPoints size region) := by rw [zero_add]
    _ < NagamochiResource.innerArea size region +
        (NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region) :=
      ENNReal.add_lt_add_right boundary_corner_top inner_positive
    _ = NagamochiResource.innerArea size region +
          NagamochiResource.boundaryLines size region +
        NagamochiResource.cornerPoints size region := by rw [add_assoc]
    _ ≤ NagamochiResource.measure size region :=
      NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure
        size region

lemma score_gt_one_of_positive_inner_and_two_half_resources
    {size : ℕ} {region : Set Plane}
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (boundary_corner_half :
      (1 / 2 : ENNReal) ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region)
    (edge_half :
      (1 / 2 : ENNReal) ≤ NagamochiResource.edgePoints size region) :
    1 < NagamochiResource.measure size region := by
  have combined_resources :
      (1 : ENNReal) ≤
        (NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region) +
            NagamochiResource.edgePoints size region := by
    have one_eq : (1 : ENNReal) = 1 / 2 + 1 / 2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
        (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rw [one_eq]
    exact add_le_add boundary_corner_half edge_half
  have inner_plus_one_gt :
      1 < NagamochiResource.innerArea size region + 1 := by
    calc
      1 = 0 + 1 := by rw [zero_add]
      _ < NagamochiResource.innerArea size region + 1 :=
        ENNReal.add_lt_add_right (by finiteness) inner_positive
  calc
    1 < NagamochiResource.innerArea size region + 1 := inner_plus_one_gt
    _ ≤ NagamochiResource.innerArea size region +
        ((NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region) +
            NagamochiResource.edgePoints size region) :=
      add_le_add le_rfl combined_resources
    _ = NagamochiResource.measure size region := by
      simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
      ac_rfl

lemma score_gt_one_of_case5_resource_bounds
    {size : ℕ} {region : Set Plane}
    {firstSide secondSide : NagamochiResource.BoundarySide}
    {firstKind secondKind : NagamochiResource.CornerPoint}
    (region_measurable : MeasurableSet region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (different_sides : firstSide ≠ secondSide)
    (different_kinds : firstKind ≠ secondKind)
    (first_chord :
      NagamochiResource.HasBoundaryChord size firstSide region (1 / 10))
    (second_chord :
      NagamochiResource.HasBoundaryChord size secondSide region (1 / 10))
    (first_point_mem :
      NagamochiResource.cornerPoint size firstKind ∈ region)
    (second_point_mem :
      NagamochiResource.cornerPoint size secondKind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have first_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable first_chord
  have second_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable second_chord
  have pair_subset :
      ({firstSide, secondSide} : Finset NagamochiResource.BoundarySide) ⊆
        NagamochiResource.boundarySides := by
    intro side side_mem
    exact NagamochiResource.mem_boundarySides side
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := region) pair_subset
  rw [Finset.sum_pair different_sides] at pair_bound
  have boundary_tenth :
      (1 / 10 : ENNReal) ≤ NagamochiResource.boundaryLines size region := by
    have two_chords_bound :
        (1 / 2 : ENNReal) *
            (ENNReal.ofReal (1 / 10 : ℝ) + ENNReal.ofReal (1 / 10 : ℝ)) ≤
          NagamochiResource.boundaryLines size region :=
      (mul_le_mul le_rfl (add_le_add first_line_bound second_line_bound)
        bot_le bot_le).trans pair_bound
    have weights_eq :
        (1 / 10 : ENNReal) =
          (1 / 2 : ENNReal) *
            (ENNReal.ofReal (1 / 10 : ℝ) + ENNReal.ofReal (1 / 10 : ℝ)) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rw [weights_eq]
    exact two_chords_bound
  have corner_nine_tenths :=
    NagamochiResource.cornerPoints_lower_bound_of_two_mem
      region_measurable different_kinds first_point_mem second_point_mem
  apply score_gt_one_of_positive_inner_and_boundary_corner inner_positive
  have weights_sum : (1 : ENNReal) = 1 / 10 + 9 / 10 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [weights_sum]
  exact add_le_add boundary_tenth corner_nine_tenths

lemma score_gt_one_of_two_corner_points_and_long_chord
    {size : ℕ} {region : Set Plane}
    {side : NagamochiResource.BoundarySide}
    {firstKind secondKind : NagamochiResource.CornerPoint}
    (region_measurable : MeasurableSet region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (different_kinds : firstKind ≠ secondKind)
    (chord :
      NagamochiResource.HasBoundaryChord size side region (1 / 5))
    (first_point_mem :
      NagamochiResource.cornerPoint size firstKind ∈ region)
    (second_point_mem :
      NagamochiResource.cornerPoint size secondKind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have line_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
    region_measurable chord
  have scaled_line_bound := NagamochiResource.boundaryLines_lower_bound
    (size := size) (region := region) line_bound
  have boundary_tenth :
      (1 / 10 : ENNReal) ≤ NagamochiResource.boundaryLines size region := by
    have weight_eq :
        (1 / 10 : ENNReal) =
          (1 / 2 : ENNReal) * ENNReal.ofReal (1 / 5 : ℝ) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
        (by finiteness)).mp
      rw [ENNReal.toReal_mul]
      norm_num
    rw [weight_eq]
    exact scaled_line_bound
  have corner_nine_tenths :=
    NagamochiResource.cornerPoints_lower_bound_of_two_mem
      region_measurable different_kinds first_point_mem second_point_mem
  apply score_gt_one_of_positive_inner_and_boundary_corner inner_positive
  have one_eq : (1 : ENNReal) = 1 / 10 + 9 / 10 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
      (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [one_eq]
  exact add_le_add boundary_tenth corner_nine_tenths

lemma score_gt_one_of_corner_chord_and_edge_point
    {size coordinate : ℕ} {region : Set Plane}
    {side : NagamochiResource.BoundarySide}
    {cornerKind : NagamochiResource.CornerPoint}
    {edgeKind : NagamochiResource.EdgePoint}
    (region_measurable : MeasurableSet region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (chord : NagamochiResource.HasBoundaryChord size side region (1 / 10))
    (corner_point_mem :
      NagamochiResource.cornerPoint size cornerKind ∈ region)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate edgeKind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have line_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
    region_measurable chord
  have scaled_line_bound := NagamochiResource.boundaryLines_lower_bound
    (size := size) (region := region) line_bound
  have boundary_twentieth :
      (1 / 20 : ENNReal) ≤ NagamochiResource.boundaryLines size region := by
    have weight_eq :
        (1 / 20 : ENNReal) =
          (1 / 2 : ENNReal) * ENNReal.ofReal (1 / 10 : ℝ) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
        (by finiteness)).mp
      rw [ENNReal.toReal_mul]
      norm_num
    rw [weight_eq]
    exact scaled_line_bound
  have corner_nine_twentieths :=
    NagamochiResource.cornerPoints_lower_bound_of_mem cornerKind
      region_measurable corner_point_mem
  have boundary_corner_half :
      (1 / 2 : ENNReal) ≤
        NagamochiResource.boundaryLines size region +
          NagamochiResource.cornerPoints size region := by
    have half_eq : (1 / 2 : ENNReal) = 1 / 20 + 9 / 20 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
        (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rw [half_eq]
    exact add_le_add boundary_twentieth corner_nine_twentieths
  have edge_half := NagamochiResource.edgePoints_lower_bound_of_mem edgeKind
    coordinate_mem region_measurable edge_point_mem
  exact score_gt_one_of_positive_inner_and_two_half_resources
    inner_positive boundary_corner_half edge_half

lemma exists_nat_in_open_interval_of_length_gt_one
    {size : ℕ} {intervalStart intervalEnd : ℝ}
    (start_nonnegative : 0 ≤ intervalStart)
    (end_at_most_size : intervalEnd ≤ size)
    (length_gt_one : 1 < intervalEnd - intervalStart) :
    ∃ coordinate ∈ Finset.Icc 1 (size - 1),
      (coordinate : ℝ) ∈ Ioo intervalStart intervalEnd := by
  let coordinate := ⌊intervalStart⌋₊ + 1
  have start_lt_coordinate : intervalStart < (coordinate : ℝ) := by
    dsimp [coordinate]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one intervalStart
  have floor_le_start : (⌊intervalStart⌋₊ : ℝ) ≤ intervalStart :=
    Nat.floor_le start_nonnegative
  have coordinate_lt_end : (coordinate : ℝ) < intervalEnd := by
    dsimp [coordinate]
    push_cast
    linarith
  have coordinate_lt_size : coordinate < size := by
    exact_mod_cast coordinate_lt_end.trans_le end_at_most_size
  refine ⟨coordinate, (by simp only [Finset.mem_Icc]; omega),
    start_lt_coordinate, coordinate_lt_end⟩

inductive GridPointWitness
    (size : ℕ) (region : Set Plane)
    (kind : NagamochiResource.EdgePoint) : Prop
  | firstCorner
      (point_mem :
        NagamochiResource.cornerPoint size kind.firstCornerPoint ∈ region)
  | secondCorner
      (point_mem :
        NagamochiResource.cornerPoint size kind.secondCornerPoint ∈ region)
  | edge
      (coordinate : ℕ)
      (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
      (point_mem :
        NagamochiResource.edgePoint size coordinate kind ∈ region)

def LongGridChordWitness
    (size : ℕ) (region : Set Plane)
    (kind : NagamochiResource.EdgePoint) : Prop :=
  ∃ intervalStart intervalEnd : ℝ,
    0 ≤ intervalStart ∧
      intervalEnd ≤ size ∧
        1 < intervalEnd - intervalStart ∧
          ∀ coordinate ∈ Ioo intervalStart intervalEnd,
            kind.pointAt size coordinate ∈ region

lemma edgePoint_coordinate_bounds_of_pointAt_mem_containerRegion
    {size : ℕ} (kind : NagamochiResource.EdgePoint) {coordinate : ℝ}
    (point_mem : kind.pointAt size coordinate ∈ containerRegion size) :
    0 ≤ coordinate ∧ coordinate ≤ size := by
  have bounds := (mem_containerRegion_iff size _).mp point_mem
  cases kind with
  | bottom =>
      exact ⟨by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.1,
        by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.1⟩
  | top =>
      exact ⟨by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.1,
        by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.1⟩
  | left =>
      exact ⟨by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.2.1,
        by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.2.2⟩
  | right =>
      exact ⟨by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.2.1,
        by simpa [NagamochiResource.EdgePoint.pointAt, Plane.toPoint]
          using bounds.2.2.2⟩

lemma openGridChord_endpoint_bounds
    {size : ℕ} {intervalStart intervalEnd : ℝ}
    (kind : NagamochiResource.EdgePoint)
    (interval_nonempty : intervalStart < intervalEnd)
    (chord_inside_container :
      ∀ coordinate ∈ Ioo intervalStart intervalEnd,
        kind.pointAt size coordinate ∈ containerRegion size) :
    0 ≤ intervalStart ∧ intervalEnd ≤ size := by
  constructor
  · by_contra start_not_nonnegative
    have start_negative : intervalStart < 0 := lt_of_not_ge start_not_nonnegative
    have start_lt_upper : intervalStart < min intervalEnd 0 :=
      lt_min interval_nonempty start_negative
    obtain ⟨coordinate, start_lt_coordinate, coordinate_lt_upper⟩ :=
      exists_between start_lt_upper
    have coordinate_mem : coordinate ∈ Ioo intervalStart intervalEnd :=
      ⟨start_lt_coordinate,
        coordinate_lt_upper.trans_le (min_le_left intervalEnd 0)⟩
    have coordinate_nonnegative :=
      edgePoint_coordinate_bounds_of_pointAt_mem_containerRegion kind
        (chord_inside_container coordinate coordinate_mem) |>.1
    have coordinate_negative :=
      coordinate_lt_upper.trans_le (min_le_right intervalEnd 0)
    linarith
  · by_contra end_not_at_most_size
    have size_lt_end : (size : ℝ) < intervalEnd :=
      lt_of_not_ge end_not_at_most_size
    have lower_lt_end : max intervalStart (size : ℝ) < intervalEnd :=
      max_lt interval_nonempty size_lt_end
    obtain ⟨coordinate, lower_lt_coordinate, coordinate_lt_end⟩ :=
      exists_between lower_lt_end
    have coordinate_mem : coordinate ∈ Ioo intervalStart intervalEnd :=
      ⟨(le_max_left intervalStart (size : ℝ)).trans_lt lower_lt_coordinate,
        coordinate_lt_end⟩
    have coordinate_at_most_size :=
      edgePoint_coordinate_bounds_of_pointAt_mem_containerRegion kind
        (chord_inside_container coordinate coordinate_mem) |>.2
    have size_lt_coordinate :=
      (le_max_right intervalStart (size : ℝ)).trans_lt lower_lt_coordinate
    linarith

lemma longGridChordWitness_of_open_chord
    {size : ℕ} {region : Set Plane} {intervalStart intervalEnd : ℝ}
    (kind : NagamochiResource.EdgePoint)
    (length_gt_one : 1 < intervalEnd - intervalStart)
    (chord_inside_region :
      ∀ coordinate ∈ Ioo intervalStart intervalEnd,
        kind.pointAt size coordinate ∈ region)
    (region_inside_container : region ⊆ containerRegion size) :
    LongGridChordWitness size region kind := by
  have interval_nonempty : intervalStart < intervalEnd := by linarith
  have endpoint_bounds := openGridChord_endpoint_bounds kind interval_nonempty
    (fun coordinate coordinate_mem =>
      region_inside_container (chord_inside_region coordinate coordinate_mem))
  exact ⟨intervalStart, intervalEnd, endpoint_bounds.1, endpoint_bounds.2,
    length_gt_one, chord_inside_region⟩

lemma bottomLongGridChordWitness_of_horizontalAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (length_gt_one :
      1 < square.horizontalAdjacentChordEnd factor (9 / 10) -
        square.horizontalAdjacentChordStart factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  apply longGridChordWitness_of_open_chord .bottom length_gt_one
  · simpa [NagamochiResource.EdgePoint.pointAt] using
      square.horizontalAdjacentChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive other_lower_at_most
        end_at_most_other_upper
  · exact inside_container

lemma bottomLongGridChordWitness_of_horizontalAdjacent_geometry
    {size : ℕ} (square : PlacedSquare)
    {factor offset tangentHalfAngle : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (cosine_eq :
      square.frame.cosine =
        (1 - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle ^ 2))
    (sine_eq :
      square.frame.sine =
        2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2))
    (vertical_offset :
      9 / 10 - factor * square.center.y = -offset)
    (offset_nonnegative : 0 ≤ offset)
    (offset_lt : offset < (Real.sqrt 2 - 1) / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have length_gt_one := horizontalAdjacentChord_length_gt_one square
    factor_gt_one.le cosine_positive sine_positive cosine_eq sine_eq
    vertical_offset offset_nonnegative offset_lt tangent_positive tangent_at_most
  exact bottomLongGridChordWitness_of_horizontalAdjacent square factor_positive
    cosine_positive sine_positive inside_container other_lower_at_most
    end_at_most_other_upper length_gt_one

lemma bottomLongGridChordWitness_of_centered_horizontalAdjacent
    {size : ℕ} (square : PlacedSquare) {factor offset : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (sine_le_cosine : square.frame.sine ≤ square.frame.cosine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (vertical_offset :
      9 / 10 - factor * square.center.y = -offset)
    (offset_nonnegative : 0 ≤ offset)
    (offset_lt : offset < (Real.sqrt 2 - 1) / 2) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
      cosine_eq, sine_eq⟩ :=
    Frame.exists_tangentHalfAngle_of_sine_le_cosine square.frame
      cosine_positive sine_positive sine_le_cosine
  exact bottomLongGridChordWitness_of_horizontalAdjacent_geometry square
    factor_gt_one cosine_positive sine_positive inside_container
    other_lower_at_most end_at_most_other_upper cosine_eq sine_eq
    vertical_offset offset_nonnegative offset_lt tangent_positive tangent_at_most

lemma bottomLongGridChordWitness_of_horizontalAdjacent_center_in_boundary_band
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (sine_le_cosine : square.frame.sine ≤ square.frame.cosine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (center_y_at_least_grid : 9 / 10 ≤ factor * square.center.y)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_two_gt_six_fifths : (6 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith
  let offset := factor * square.center.y - 9 / 10
  have offset_nonnegative : 0 ≤ offset := by
    dsimp [offset]
    linarith
  have offset_lt : offset < (Real.sqrt 2 - 1) / 2 := by
    dsimp [offset]
    linarith
  exact bottomLongGridChordWitness_of_centered_horizontalAdjacent square
    factor_gt_one cosine_positive sine_positive sine_le_cosine inside_container
    other_lower_at_most end_at_most_other_upper (by dsimp [offset]; ring)
    offset_nonnegative offset_lt

lemma bottomLongGridChordWitness_of_horizontalAdjacent_center_in_boundary_band_any_positive_frame
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (center_y_at_least_grid : 9 / 10 ≤ factor * square.center.y)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_two_gt_six_fifths : (6 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith
  let offset := factor * square.center.y - 9 / 10
  have offset_nonnegative : 0 ≤ offset := by
    dsimp [offset]
    linarith
  have offset_lt : offset < (Real.sqrt 2 - 1) / 2 := by
    dsimp [offset]
    linarith
  have length_gt_one :=
    horizontalAdjacentChord_length_gt_one_any_positive_frame
      (factor := factor) (height := 9 / 10) (offset := offset) square
      factor_gt_one.le cosine_positive sine_positive
      (by dsimp [offset]; ring) offset_nonnegative offset_lt
  exact bottomLongGridChordWitness_of_horizontalAdjacent square
    (zero_lt_one.trans factor_gt_one) cosine_positive sine_positive
    inside_container other_lower_at_most end_at_most_other_upper length_gt_one

lemma bottomLongGridChordWitness_of_horizontalAdjacent_center_at_most_grid
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10))
    (center_y_at_most_grid : factor * square.center.y ≤ 9 / 10) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have length_gt_one :=
    horizontalAdjacentChord_length_gt_one_of_center_at_most_line square
      factor_gt_one cosine_positive sine_positive center_y_at_most_grid
  exact bottomLongGridChordWitness_of_horizontalAdjacent square factor_positive
    cosine_positive sine_positive inside_container other_lower_at_most
    end_at_most_other_upper length_gt_one

lemma bottomLongGridChordWitness_of_horizontalOtherAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (other_upper_at_most_chord_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10))
    (length_gt_one :
      1 < square.horizontalAdjacentOtherUpper factor (9 / 10) -
        square.horizontalAdjacentOtherLower factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  apply longGridChordWitness_of_open_chord .bottom length_gt_one
  · simpa [NagamochiResource.EdgePoint.pointAt] using
      square.horizontalOtherAdjacentChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        chord_start_at_most_other_lower other_upper_at_most_chord_end
  · exact inside_container

lemma bottomLongGridChordWitness_of_horizontalOtherAdjacent_geometry
    {size : ℕ} (square : PlacedSquare)
    {factor tangentHalfAngle : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (other_upper_at_most_chord_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10))
    (cosine_eq :
      square.frame.cosine =
        (1 - tangentHalfAngle ^ 2) / (1 + tangentHalfAngle ^ 2))
    (sine_eq :
      square.frame.sine =
        2 * tangentHalfAngle / (1 + tangentHalfAngle ^ 2))
    (bottom_touch :
      factor * square.center.y =
        factor * (square.frame.cosine + square.frame.sine) / 2)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_at_most : tangentHalfAngle ≤ Real.sqrt 2 - 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have height_gt_half : (1 / 2 : ℝ) < 9 / 10 := by norm_num
  have height_lt : (9 / 10 : ℝ) < Real.sqrt 2 - 1 / 2 := by
    nlinarith
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have length_gt_one := horizontalOtherAdjacentChord_length_gt_one square
    factor_gt_one.le cosine_positive sine_positive cosine_eq sine_eq
    bottom_touch height_gt_half height_lt tangent_positive tangent_at_most
  exact bottomLongGridChordWitness_of_horizontalOtherAdjacent square
    factor_positive cosine_positive sine_positive inside_container
    chord_start_at_most_other_lower other_upper_at_most_chord_end length_gt_one

lemma bottomLongGridChordWitness_of_bottom_touching_horizontalOtherAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (sine_le_cosine : square.frame.sine ≤ square.frame.cosine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (other_upper_at_most_chord_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10))
    (bottom_touch :
      factor * square.center.y =
        factor * (square.frame.cosine + square.frame.sine) / 2) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
      cosine_eq, sine_eq⟩ :=
    Frame.exists_tangentHalfAngle_of_sine_le_cosine square.frame
      cosine_positive sine_positive sine_le_cosine
  exact bottomLongGridChordWitness_of_horizontalOtherAdjacent_geometry square
    factor_gt_one cosine_positive sine_positive inside_container
    chord_start_at_most_other_lower other_upper_at_most_chord_end
    cosine_eq sine_eq bottom_touch tangent_positive tangent_at_most

lemma bottomLongGridChordWitness_of_contained_horizontalOtherAdjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (sine_le_cosine : square.frame.sine ≤ square.frame.cosine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (other_upper_at_most_chord_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have height_gt_half : (1 / 2 : ℝ) < 9 / 10 := by norm_num
  have height_lt : (9 / 10 : ℝ) < Real.sqrt 2 - 1 / 2 := by
    nlinarith
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bottom_contained := square.dilatedCenterY_halfExtent_le
    factor_positive cosine_positive.le sine_positive.le inside_container
  obtain ⟨tangentHalfAngle, tangent_positive, tangent_at_most,
      cosine_eq, sine_eq⟩ :=
    Frame.exists_tangentHalfAngle_of_sine_le_cosine square.frame
      cosine_positive sine_positive sine_le_cosine
  have length_gt_one :=
    horizontalOtherAdjacentChord_length_gt_one_of_bottom_contained square
      factor_gt_one.le cosine_positive sine_positive cosine_eq sine_eq
      bottom_contained height_gt_half height_lt tangent_positive tangent_at_most
  exact bottomLongGridChordWitness_of_horizontalOtherAdjacent square
    factor_positive cosine_positive sine_positive inside_container
    chord_start_at_most_other_lower other_upper_at_most_chord_end length_gt_one

lemma bottomLongGridChordWitness_of_contained_horizontalOtherAdjacent_any_positive_frame
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (other_upper_at_most_chord_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have sqrt_two_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have height_gt_half : (1 / 2 : ℝ) < 9 / 10 := by norm_num
  have height_lt : (9 / 10 : ℝ) < Real.sqrt 2 - 1 / 2 := by
    nlinarith
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bottom_contained := square.dilatedCenterY_halfExtent_le
    factor_positive cosine_positive.le sine_positive.le inside_container
  have length_gt_one :=
    horizontalOtherAdjacentChord_length_gt_one_any_positive_frame square
      factor_gt_one.le cosine_positive sine_positive bottom_contained
      height_gt_half height_lt
  exact bottomLongGridChordWitness_of_horizontalOtherAdjacent square
    factor_positive cosine_positive sine_positive inside_container
    chord_start_at_most_other_lower other_upper_at_most_chord_end length_gt_one

lemma bottomLongGridChordWitness_of_horizontalCosineChord
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor (9 / 10) ≤
        square.horizontalAdjacentChordStart factor (9 / 10))
    (other_upper_at_most_end :
      square.horizontalAdjacentOtherUpper factor (9 / 10) ≤
        square.horizontalAdjacentChordEnd factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_le_length :=
    square.horizontalCosineChord_length_at_least_factor
      (height := 9 / 10) factor_positive.le cosine_positive
  apply longGridChordWitness_of_open_chord .bottom
    (factor_gt_one.trans_le factor_le_length)
  · simpa [NagamochiResource.EdgePoint.pointAt] using
      square.horizontalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive other_lower_at_most
        other_upper_at_most_end
  · exact inside_container

lemma bottomLongGridChordWitness_of_horizontalSineChord
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (chord_start_at_most_other_lower :
      square.horizontalAdjacentChordStart factor (9 / 10) ≤
        square.horizontalAdjacentOtherLower factor (9 / 10))
    (chord_end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor (9 / 10) ≤
        square.horizontalAdjacentOtherUpper factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_le_length :=
    square.horizontalSineChord_length_at_least_factor
      (height := 9 / 10) factor_positive.le sine_positive
  apply longGridChordWitness_of_open_chord .bottom
    (factor_gt_one.trans_le factor_le_length)
  · simpa [NagamochiResource.EdgePoint.pointAt] using
      square.horizontalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive
        chord_start_at_most_other_lower chord_end_at_most_other_upper
  · exact inside_container

lemma bottomLongGridChordWitness_of_horizontalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (opposite :
      HasHorizontalOppositeChordWithin size square factor (9 / 10)) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  rcases opposite with
    ⟨other_lower_at_most, other_upper_at_most_end, _⟩ |
      ⟨chord_start_at_most_other_lower, chord_end_at_most_other_upper, _⟩
  · exact bottomLongGridChordWitness_of_horizontalCosineChord square
      factor_gt_one cosine_positive sine_positive inside_container
      other_lower_at_most other_upper_at_most_end
  · exact bottomLongGridChordWitness_of_horizontalSineChord square
      factor_gt_one cosine_positive sine_positive inside_container
      chord_start_at_most_other_lower chord_end_at_most_other_upper

lemma bottomLongGridChordWitness_of_axis_aligned
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have axis_values :
      (square.frame.cosine = 0 ∧ square.frame.sine = 1) ∨
        (square.frame.cosine = 1 ∧ square.frame.sine = 0) := by
    rcases axis_aligned with cosine_zero | sine_zero
    · left
      refine ⟨cosine_zero, ?_⟩
      have frame_unit := square.frame.unit
      rw [cosine_zero] at frame_unit
      nlinarith
    · right
      refine ⟨?_, sine_zero⟩
      have frame_unit := square.frame.unit
      rw [sine_zero] at frame_unit
      nlinarith
  have component_sum_eq_one :
      square.frame.cosine + square.frame.sine = 1 := by
    rcases axis_values with ⟨cosine_zero, sine_one⟩ |
      ⟨cosine_one, sine_zero⟩
    · rw [cosine_zero, sine_one]
      norm_num
    · rw [cosine_one, sine_zero]
      norm_num
  have center_y_at_least_half_factor :
      factor / 2 ≤ factor * square.center.y := by
    have half_extent_bound := square.dilatedCenterY_halfExtent_le
      factor_positive cosine_nonnegative sine_nonnegative inside_container
    rw [component_sum_eq_one] at half_extent_bound
    norm_num at half_extent_bound ⊢
    exact half_extent_bound
  have vertical_offset_bound :
      |(9 / 10 : ℝ) - factor * square.center.y| < factor / 2 := by
    rw [abs_lt]
    constructor <;> nlinarith
  let intervalStart := factor * square.center.x - factor / 2
  let intervalEnd := factor * square.center.x + factor / 2
  apply longGridChordWitness_of_open_chord .bottom
      (intervalStart := intervalStart) (intervalEnd := intervalEnd)
  · dsimp [intervalStart, intervalEnd]
    linarith
  · intro coordinate coordinate_mem
    have horizontal_offset_bound :
        |coordinate - factor * square.center.x| < factor / 2 := by
      rw [abs_lt]
      dsimp [intervalStart, intervalEnd] at coordinate_mem
      exact ⟨by linarith [coordinate_mem.1],
        by linarith [coordinate_mem.2]⟩
    rcases axis_values with ⟨cosine_zero, sine_one⟩ |
      ⟨cosine_one, sine_zero⟩
    · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
      · simpa [NagamochiResource.EdgePoint.pointAt,
          PlacedSquare.dilatedLocalX, Plane.toPoint, cosine_zero,
          sine_one] using vertical_offset_bound
      · simpa [NagamochiResource.EdgePoint.pointAt,
          PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_zero,
          sine_one, abs_neg, abs_sub_comm] using horizontal_offset_bound
    · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
      · simpa [NagamochiResource.EdgePoint.pointAt,
          PlacedSquare.dilatedLocalX, Plane.toPoint, cosine_one,
          sine_zero] using horizontal_offset_bound
      · simpa [NagamochiResource.EdgePoint.pointAt,
          PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_one,
          sine_zero] using vertical_offset_bound
  · exact inside_container

lemma bottomLongGridChordWitness_of_center_in_bottom_strip_positive_frame
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  rcases le_total
      (square.horizontalAdjacentOtherLower factor (9 / 10))
      (square.horizontalAdjacentChordStart factor (9 / 10)) with
    other_lower_at_most | chord_start_at_most_other_lower
  · rcases le_total
        (square.horizontalAdjacentChordEnd factor (9 / 10))
        (square.horizontalAdjacentOtherUpper factor (9 / 10)) with
      chord_end_at_most_other_upper | other_upper_at_most_chord_end
    · by_cases center_y_at_most_grid :
          factor * square.center.y ≤ 9 / 10
      · exact
          bottomLongGridChordWitness_of_horizontalAdjacent_center_at_most_grid
            square factor_gt_one cosine_positive sine_positive inside_container
            other_lower_at_most chord_end_at_most_other_upper
            center_y_at_most_grid
      · exact
          bottomLongGridChordWitness_of_horizontalAdjacent_center_in_boundary_band_any_positive_frame
            square factor_gt_one cosine_positive sine_positive
            inside_container other_lower_at_most chord_end_at_most_other_upper
            (le_of_not_ge center_y_at_most_grid) center_y_at_most_boundary
    · exact bottomLongGridChordWitness_of_horizontalCosineChord square
        factor_gt_one cosine_positive sine_positive inside_container
        other_lower_at_most other_upper_at_most_chord_end
  · rcases le_total
        (square.horizontalAdjacentOtherUpper factor (9 / 10))
        (square.horizontalAdjacentChordEnd factor (9 / 10)) with
      other_upper_at_most_chord_end | chord_end_at_most_other_upper
    · exact
        bottomLongGridChordWitness_of_contained_horizontalOtherAdjacent_any_positive_frame
          square factor_gt_one cosine_positive sine_positive
          inside_container chord_start_at_most_other_lower
          other_upper_at_most_chord_end
    · exact bottomLongGridChordWitness_of_horizontalSineChord square
        factor_gt_one cosine_positive sine_positive inside_container
        chord_start_at_most_other_lower chord_end_at_most_other_upper

lemma bottomLongGridChordWitness_of_center_in_bottom_strip
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .bottom := by
  let normalizedSquare := square.firstQuadrant
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_eq :
      normalizedSquare.dilatedInteriorRegion factor =
        square.dilatedInteriorRegion factor := by
    exact square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_inside :
      normalizedSquare.dilatedInteriorRegion factor ⊆ containerRegion size := by
    rw [region_eq]
    exact inside_container
  have normalized_center_y_at_most_boundary :
      factor * normalizedSquare.center.y ≤ 1 := by
    simpa [normalizedSquare] using center_y_at_most_boundary
  have cosine_nonnegative : 0 ≤ normalizedSquare.frame.cosine := by
    simpa [normalizedSquare] using square.firstQuadrant_cosine_nonnegative
  have sine_nonnegative : 0 ≤ normalizedSquare.frame.sine := by
    simpa [normalizedSquare] using square.firstQuadrant_sine_nonnegative
  have normalized_witness :
      LongGridChordWitness size
        (normalizedSquare.dilatedInteriorRegion factor) .bottom := by
    by_cases cosine_zero : normalizedSquare.frame.cosine = 0
    · exact bottomLongGridChordWitness_of_axis_aligned normalizedSquare
        factor_gt_one cosine_nonnegative sine_nonnegative (Or.inl cosine_zero)
        normalized_inside normalized_center_y_at_most_boundary
    by_cases sine_zero : normalizedSquare.frame.sine = 0
    · exact bottomLongGridChordWitness_of_axis_aligned normalizedSquare
        factor_gt_one cosine_nonnegative sine_nonnegative (Or.inr sine_zero)
        normalized_inside normalized_center_y_at_most_boundary
    · have cosine_positive : 0 < normalizedSquare.frame.cosine :=
        lt_of_le_of_ne cosine_nonnegative (Ne.symm cosine_zero)
      have sine_positive : 0 < normalizedSquare.frame.sine :=
        lt_of_le_of_ne sine_nonnegative (Ne.symm sine_zero)
      exact bottomLongGridChordWitness_of_center_in_bottom_strip_positive_frame
        normalizedSquare factor_gt_one cosine_positive sine_positive
        normalized_inside normalized_center_y_at_most_boundary
  rw [region_eq] at normalized_witness
  exact normalized_witness

lemma topLongGridChordWitness_of_center_in_top_strip
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_least_boundary :
      (size : ℝ) - 1 ≤ factor * square.center.y) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .top := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let coordinateSum := (size : ℝ) / factor
  have coordinate_identity : factor * coordinateSum = size := by
    dsimp [coordinateSum]
    field_simp [factor_positive.ne']
  let reflectedSquare := square.reflectY coordinateSum
  have reflected_inside :
      reflectedSquare.dilatedInteriorRegion factor ⊆ containerRegion size := by
    exact square.reflectY_dilatedInteriorRegion_subset_containerRegion
      factor_positive coordinate_identity inside_container
  have reflected_center_y_at_most_boundary :
      factor * reflectedSquare.center.y ≤ 1 := by
    change factor * (coordinateSum - square.center.y) ≤ 1
    rw [mul_sub, coordinate_identity]
    linarith
  rcases bottomLongGridChordWitness_of_center_in_bottom_strip reflectedSquare
      factor_gt_one reflected_inside reflected_center_y_at_most_boundary with
    ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
      length_gt_one, chord_inside_reflected⟩
  refine ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
    length_gt_one, ?_⟩
  intro coordinate coordinate_mem
  apply (square.mem_reflectY_dilatedInteriorRegion_iff
    (coordinateSum := coordinateSum) factor_positive
    (NagamochiResource.EdgePoint.top.pointAt size coordinate)).mp
  have reflected_point_mem := chord_inside_reflected coordinate coordinate_mem
  simpa [reflectedSquare, NagamochiResource.EdgePoint.pointAt,
    Plane.reflectY, coordinate_identity] using reflected_point_mem

lemma leftLongGridChordWitness_of_center_in_left_strip
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_boundary : factor * square.center.x ≤ 1) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .left := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let swappedSquare := square.swap
  have swapped_inside :
      swappedSquare.dilatedInteriorRegion factor ⊆ containerRegion size := by
    exact square.swap_dilatedInteriorRegion_subset_containerRegion
      factor_positive inside_container
  have swapped_center_y_at_most_boundary :
      factor * swappedSquare.center.y ≤ 1 := by
    simpa [swappedSquare, PlacedSquare.swap, Point.swap] using
      center_x_at_most_boundary
  rcases bottomLongGridChordWitness_of_center_in_bottom_strip swappedSquare
      factor_gt_one swapped_inside swapped_center_y_at_most_boundary with
    ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
      length_gt_one, chord_inside_swapped⟩
  refine ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
    length_gt_one, ?_⟩
  intro coordinate coordinate_mem
  apply (square.mem_swap_dilatedInteriorRegion_iff factor_positive
    (NagamochiResource.EdgePoint.left.pointAt size coordinate)).mp
  have swapped_point_mem := chord_inside_swapped coordinate coordinate_mem
  simpa [swappedSquare, NagamochiResource.EdgePoint.pointAt,
    Plane.swap] using swapped_point_mem

lemma rightLongGridChordWitness_of_center_in_right_strip
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_boundary :
      (size : ℝ) - 1 ≤ factor * square.center.x) :
    LongGridChordWitness size (square.dilatedInteriorRegion factor) .right := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let coordinateSum := (size : ℝ) / factor
  have coordinate_identity : factor * coordinateSum = size := by
    dsimp [coordinateSum]
    field_simp [factor_positive.ne']
  let reflectedSquare := square.reflectX coordinateSum
  have reflected_inside :
      reflectedSquare.dilatedInteriorRegion factor ⊆ containerRegion size := by
    exact square.reflectX_dilatedInteriorRegion_subset_containerRegion
      factor_positive coordinate_identity inside_container
  have reflected_center_x_at_most_boundary :
      factor * reflectedSquare.center.x ≤ 1 := by
    change factor * (coordinateSum - square.center.x) ≤ 1
    rw [mul_sub, coordinate_identity]
    linarith
  rcases leftLongGridChordWitness_of_center_in_left_strip reflectedSquare
      factor_gt_one reflected_inside reflected_center_x_at_most_boundary with
    ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
      length_gt_one, chord_inside_reflected⟩
  refine ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
    length_gt_one, ?_⟩
  intro coordinate coordinate_mem
  apply (square.mem_reflectX_dilatedInteriorRegion_iff
    (coordinateSum := coordinateSum) factor_positive
    (NagamochiResource.EdgePoint.right.pointAt size coordinate)).mp
  have reflected_point_mem := chord_inside_reflected coordinate coordinate_mem
  simpa [reflectedSquare, NagamochiResource.EdgePoint.pointAt,
    Plane.reflectX, coordinate_identity] using reflected_point_mem

lemma gridPointWitness_of_open_grid_chord
    {size : ℕ} {region : Set Plane}
    (kind : NagamochiResource.EdgePoint)
    (size_at_least_three : 3 ≤ size)
    (chord : LongGridChordWitness size region kind) :
    GridPointWitness size region kind := by
  rcases chord with
    ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
      length_gt_one, chord_inside_region⟩
  obtain ⟨coordinate, coordinate_mem, coordinate_in_chord⟩ :=
    exists_nat_in_open_interval_of_length_gt_one start_nonnegative
      end_at_most_size length_gt_one
  have coordinate_bounds : 1 ≤ coordinate ∧ coordinate ≤ size - 1 := by
    simpa only [Finset.mem_Icc] using coordinate_mem
  have point_mem := chord_inside_region coordinate coordinate_in_chord
  by_cases coordinate_is_first : coordinate = 1
  · refine .firstCorner ?_
    simpa [coordinate_is_first] using point_mem
  by_cases coordinate_is_second : coordinate = size - 1
  · have one_le_size : 1 ≤ size := by omega
    have coordinate_cast :
        (coordinate : ℝ) = (size : ℝ) - 1 := by
      rw [coordinate_is_second, Nat.cast_sub one_le_size]
      norm_num
    refine .secondCorner ?_
    simpa [coordinate_cast] using point_mem
  · refine .edge coordinate (by simp only [Finset.mem_Icc]; omega) ?_
    simpa using point_mem

lemma bottomGridPointWitness_of_center_in_bottom_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_most_boundary : factor * square.center.y ≤ 1) :
    GridPointWitness size (square.dilatedInteriorRegion factor) .bottom := by
  exact gridPointWitness_of_open_grid_chord .bottom size_at_least_three
    (bottomLongGridChordWitness_of_center_in_bottom_strip square factor_gt_one
      inside_container center_y_at_most_boundary)

lemma topGridPointWitness_of_center_in_top_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_y_at_least_boundary :
      (size : ℝ) - 1 ≤ factor * square.center.y) :
    GridPointWitness size (square.dilatedInteriorRegion factor) .top := by
  exact gridPointWitness_of_open_grid_chord .top size_at_least_three
    (topLongGridChordWitness_of_center_in_top_strip square factor_gt_one
      inside_container center_y_at_least_boundary)

lemma leftGridPointWitness_of_center_in_left_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_boundary : factor * square.center.x ≤ 1) :
    GridPointWitness size (square.dilatedInteriorRegion factor) .left := by
  exact gridPointWitness_of_open_grid_chord .left size_at_least_three
    (leftLongGridChordWitness_of_center_in_left_strip square factor_gt_one
      inside_container center_x_at_most_boundary)

lemma rightGridPointWitness_of_center_in_right_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_boundary :
      (size : ℝ) - 1 ≤ factor * square.center.x) :
    GridPointWitness size (square.dilatedInteriorRegion factor) .right := by
  exact gridPointWitness_of_open_grid_chord .right size_at_least_three
    (rightLongGridChordWitness_of_center_in_right_strip square factor_gt_one
      inside_container center_x_at_least_boundary)

lemma bottomGridPointWitness_of_open_chord
    {size : ℕ} {region : Set Plane} {intervalStart intervalEnd : ℝ}
    (size_at_least_three : 3 ≤ size)
    (start_nonnegative : 0 ≤ intervalStart)
    (end_at_most_size : intervalEnd ≤ size)
    (length_gt_one : 1 < intervalEnd - intervalStart)
    (chord_inside_region :
      ∀ coordinate ∈ Ioo intervalStart intervalEnd,
        ![coordinate, (9 / 10 : ℝ)] ∈ region) :
    GridPointWitness size region .bottom := by
  exact gridPointWitness_of_open_grid_chord .bottom
    size_at_least_three
    ⟨intervalStart, intervalEnd, start_nonnegative, end_at_most_size,
      length_gt_one, chord_inside_region⟩

lemma corner_mem_of_gridPointWitness_of_no_edge_points
    {size : ℕ} {region : Set Plane}
    (kind : NagamochiResource.EdgePoint)
    (witness : GridPointWitness size region kind)
    (no_edge_points :
      ∀ coordinate,
        coordinate ∈ Finset.Icc 2 (size - 2) →
          NagamochiResource.edgePoint size coordinate kind ∉ region) :
    NagamochiResource.cornerPoint size kind.firstCornerPoint ∈ region ∨
      NagamochiResource.cornerPoint size kind.secondCornerPoint ∈ region := by
  cases witness with
  | firstCorner point_mem => exact Or.inl point_mem
  | secondCorner point_mem => exact Or.inr point_mem
  | edge coordinate coordinate_mem point_mem =>
      exact False.elim (no_edge_points coordinate coordinate_mem point_mem)

lemma edge_mem_of_gridPointWitness_of_no_corner_points
    {size : ℕ} {region : Set Plane}
    (kind : NagamochiResource.EdgePoint)
    (witness : GridPointWitness size region kind)
    (first_corner_not_mem :
      NagamochiResource.cornerPoint size kind.firstCornerPoint ∉ region)
    (second_corner_not_mem :
      NagamochiResource.cornerPoint size kind.secondCornerPoint ∉ region) :
    ∃ coordinate,
      coordinate ∈ Finset.Icc 2 (size - 2) ∧
        NagamochiResource.edgePoint size coordinate kind ∈ region := by
  cases witness with
  | firstCorner point_mem => exact False.elim (first_corner_not_mem point_mem)
  | secondCorner point_mem => exact False.elim (second_corner_not_mem point_mem)
  | edge coordinate coordinate_mem point_mem =>
      exact ⟨coordinate, coordinate_mem, point_mem⟩

inductive Case7ResourceWitness
    (size : ℕ) (region : Set Plane) : Prop
  | oppositeAndEdge
      (side : NagamochiResource.BoundarySide)
      (coordinate : ℕ)
      (kind : NagamochiResource.EdgePoint)
      (minimumLength : ℝ)
      (minimum_length_gt_one : 1 < minimumLength)
      (chord :
        NagamochiResource.HasBoundaryChord size side region minimumLength)
      (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
      (point_mem :
        NagamochiResource.edgePoint size coordinate kind ∈ region)
  | cornerAndEdge
      (side : NagamochiResource.BoundarySide)
      (cornerKind : NagamochiResource.CornerPoint)
      (coordinate : ℕ)
      (edgeKind : NagamochiResource.EdgePoint)
      (inner_positive : 0 < NagamochiResource.innerArea size region)
      (chord :
        NagamochiResource.HasBoundaryChord size side region (1 / 10))
      (corner_point_mem :
        NagamochiResource.cornerPoint size cornerKind ∈ region)
      (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
      (edge_point_mem :
        NagamochiResource.edgePoint size coordinate edgeKind ∈ region)
  | twoCorners
      (side : NagamochiResource.BoundarySide)
      (firstKind secondKind : NagamochiResource.CornerPoint)
      (inner_positive : 0 < NagamochiResource.innerArea size region)
      (different_kinds : firstKind ≠ secondKind)
      (chord :
        NagamochiResource.HasBoundaryChord size side region (1 / 5))
      (first_point_mem :
        NagamochiResource.cornerPoint size firstKind ∈ region)
      (second_point_mem :
        NagamochiResource.cornerPoint size secondKind ∈ region)
  | longAndShortAndCorner
      (factor : ℝ)
      (factor_gt_one : 1 < factor)
      (longSide shortSide : NagamochiResource.BoundarySide)
      (different_sides : longSide ≠ shortSide)
      (long_chord :
        NagamochiResource.HasBoundaryChord size longSide region factor)
      (short_chord :
        NagamochiResource.HasBoundaryChord size shortSide region (1 / 10))
      (cornerKind : NagamochiResource.CornerPoint)
      (corner_point_mem :
        NagamochiResource.cornerPoint size cornerKind ∈ region)

inductive BoundaryCornerConnection
    (size : ℕ) (region : Set Plane)
    (longSide : NagamochiResource.BoundarySide)
    (cornerKind : NagamochiResource.CornerPoint) : Prop
  | first
      (shortSide : NagamochiResource.BoundarySide)
      (different_sides : longSide ≠ shortSide)
      (corner_eq : cornerKind = shortSide.firstCornerPoint)
      (unit_point_mem : shortSide.pointAt size 1 ∈ region)
  | second
      (shortSide : NagamochiResource.BoundarySide)
      (different_sides : longSide ≠ shortSide)
      (corner_eq : cornerKind = shortSide.secondCornerPoint)
      (unit_point_mem :
        shortSide.pointAt size ((size : ℝ) - 1) ∈ region)

lemma score_gt_one_of_case7_resource_witness
    {size : ℕ} {region : Set Plane}
    (region_measurable : MeasurableSet region)
    (witness : Case7ResourceWitness size region) :
    1 < NagamochiResource.measure size region := by
  cases witness with
  | oppositeAndEdge side coordinate kind minimumLength minimum_length_gt_one
      chord coordinate_mem point_mem =>
      exact score_gt_one_of_boundary_chord_and_edge_point minimum_length_gt_one
        region_measurable chord coordinate_mem point_mem
  | cornerAndEdge side cornerKind coordinate edgeKind inner_positive chord
      corner_point_mem coordinate_mem edge_point_mem =>
      exact score_gt_one_of_corner_chord_and_edge_point region_measurable
        inner_positive chord corner_point_mem coordinate_mem edge_point_mem
  | twoCorners side firstKind secondKind inner_positive different_kinds chord
      first_point_mem second_point_mem =>
      exact score_gt_one_of_two_corner_points_and_long_chord
        region_measurable inner_positive different_kinds chord
        first_point_mem second_point_mem
  | longAndShortAndCorner factor factor_gt_one longSide shortSide
      different_sides long_chord short_chord cornerKind corner_point_mem =>
      exact score_gt_one_of_long_and_short_boundary_chords_and_corner_point
        factor_gt_one different_sides region_measurable long_chord short_chord
        corner_point_mem

lemma case7ResourceWitness_of_two_boundary_corner_points
    {size : ℕ} {region : Set Plane}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (side : NagamochiResource.BoundarySide)
    (first_point_mem :
      NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region)
    (second_point_mem :
      NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region) :
    Case7ResourceWitness size region := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have endpoints_ordered :
      (9 / 10 : ℝ) < (size : ℝ) - 9 / 10 := by linarith
  have first_point_at_mem : side.pointAt size (9 / 10) ∈ region := by
    simpa using first_point_mem
  have second_point_at_mem :
      side.pointAt size ((size : ℝ) - 9 / 10) ∈ region := by
    simpa using second_point_mem
  have chord : NagamochiResource.HasBoundaryChord size side region (1 / 5) :=
    boundaryChord_of_pointAt_mem side region_convex endpoints_ordered
      (by linarith) (fun _ point_mem => ⟨point_mem.1.le, point_mem.2.le⟩)
      first_point_at_mem second_point_at_mem
  exact .twoCorners side side.firstCornerPoint side.secondCornerPoint
    inner_positive side.cornerPoints_ne chord first_point_mem second_point_mem

lemma case7ResourceWitness_of_first_boundary_corner_and_edge_point
    {size coordinate : ℕ} {region : Set Plane}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (side : NagamochiResource.BoundarySide)
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region)
    (unit_point_mem : side.pointAt size 1 ∈ region)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint)
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈ region) :
    Case7ResourceWitness size region := by
  have chord : NagamochiResource.HasBoundaryChord size side region (1 / 10) :=
    firstBoundaryChord_of_corner_and_unit_point size_at_least_three side
      region_convex corner_point_mem unit_point_mem
  exact .cornerAndEdge side side.firstCornerPoint coordinate kind
    inner_positive chord corner_point_mem coordinate_mem edge_point_mem

lemma case7ResourceWitness_of_second_boundary_corner_and_edge_point
    {size coordinate : ℕ} {region : Set Plane}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (inner_positive : 0 < NagamochiResource.innerArea size region)
    (side : NagamochiResource.BoundarySide)
    (unit_point_mem : side.pointAt size ((size : ℝ) - 1) ∈ region)
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint)
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈ region) :
    Case7ResourceWitness size region := by
  have chord : NagamochiResource.HasBoundaryChord size side region (1 / 10) :=
    secondBoundaryChord_of_unit_and_corner_point size_at_least_three side
      region_convex unit_point_mem corner_point_mem
  exact .cornerAndEdge side side.secondCornerPoint coordinate kind
    inner_positive chord corner_point_mem coordinate_mem edge_point_mem

lemma case7ResourceWitness_of_long_chord_and_first_boundary_corner
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (factor_gt_one : 1 < factor)
    (longSide shortSide : NagamochiResource.BoundarySide)
    (different_sides : longSide ≠ shortSide)
    (long_chord :
      NagamochiResource.HasBoundaryChord size longSide region factor)
    (corner_point_mem :
      NagamochiResource.cornerPoint size shortSide.firstCornerPoint ∈ region)
    (unit_point_mem : shortSide.pointAt size 1 ∈ region) :
    Case7ResourceWitness size region := by
  have short_chord := firstBoundaryChord_of_corner_and_unit_point
    size_at_least_three shortSide region_convex corner_point_mem unit_point_mem
  exact .longAndShortAndCorner factor factor_gt_one longSide shortSide
    different_sides long_chord short_chord shortSide.firstCornerPoint
    corner_point_mem

lemma case7ResourceWitness_of_long_chord_and_second_boundary_corner
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (factor_gt_one : 1 < factor)
    (longSide shortSide : NagamochiResource.BoundarySide)
    (different_sides : longSide ≠ shortSide)
    (long_chord :
      NagamochiResource.HasBoundaryChord size longSide region factor)
    (unit_point_mem :
      shortSide.pointAt size ((size : ℝ) - 1) ∈ region)
    (corner_point_mem :
      NagamochiResource.cornerPoint size shortSide.secondCornerPoint ∈ region) :
    Case7ResourceWitness size region := by
  have short_chord := secondBoundaryChord_of_unit_and_corner_point
    size_at_least_three shortSide region_convex unit_point_mem corner_point_mem
  exact .longAndShortAndCorner factor factor_gt_one longSide shortSide
    different_sides long_chord short_chord shortSide.secondCornerPoint
    corner_point_mem

lemma case7ResourceWitness_of_long_chord_and_grid_point
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (factor_gt_one : 1 < factor)
    (longSide : NagamochiResource.BoundarySide)
    (long_chord :
      NagamochiResource.HasBoundaryChord size longSide region factor)
    (gridKind : NagamochiResource.EdgePoint)
    (grid_point : GridPointWitness size region gridKind)
    (connect_first_corner : BoundaryCornerConnection size region longSide
      gridKind.firstCornerPoint)
    (connect_second_corner : BoundaryCornerConnection size region longSide
      gridKind.secondCornerPoint) :
    Case7ResourceWitness size region := by
  cases grid_point with
  | edge coordinate coordinate_mem point_mem =>
      exact .oppositeAndEdge longSide coordinate gridKind factor factor_gt_one
        long_chord coordinate_mem point_mem
  | firstCorner corner_point_mem =>
      cases connect_first_corner with
      | first shortSide different_sides corner_eq unit_point_mem =>
          rw [corner_eq] at corner_point_mem
          exact case7ResourceWitness_of_long_chord_and_first_boundary_corner
            size_at_least_three region_convex factor_gt_one longSide shortSide
            different_sides long_chord corner_point_mem unit_point_mem
      | second shortSide different_sides corner_eq unit_point_mem =>
          rw [corner_eq] at corner_point_mem
          exact case7ResourceWitness_of_long_chord_and_second_boundary_corner
            size_at_least_three region_convex factor_gt_one longSide shortSide
            different_sides long_chord unit_point_mem corner_point_mem
  | secondCorner corner_point_mem =>
      cases connect_second_corner with
      | first shortSide different_sides corner_eq unit_point_mem =>
          rw [corner_eq] at corner_point_mem
          exact case7ResourceWitness_of_long_chord_and_first_boundary_corner
            size_at_least_three region_convex factor_gt_one longSide shortSide
            different_sides long_chord corner_point_mem unit_point_mem
      | second shortSide different_sides corner_eq unit_point_mem =>
          rw [corner_eq] at corner_point_mem
          exact case7ResourceWitness_of_long_chord_and_second_boundary_corner
            size_at_least_three region_convex factor_gt_one longSide shortSide
            different_sides long_chord unit_point_mem corner_point_mem

lemma case7ResourceWitness_of_long_chord_and_boundary_connection
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (region_convex : Convex ℝ region)
    (factor_gt_one : 1 < factor)
    (longSide : NagamochiResource.BoundarySide)
    (long_chord :
      NagamochiResource.HasBoundaryChord size longSide region factor)
    (cornerKind : NagamochiResource.CornerPoint)
    (corner_point_mem :
      NagamochiResource.cornerPoint size cornerKind ∈ region)
    (connection :
      BoundaryCornerConnection size region longSide cornerKind) :
    Case7ResourceWitness size region := by
  cases connection with
  | first shortSide different_sides corner_eq unit_point_mem =>
      rw [corner_eq] at corner_point_mem
      exact case7ResourceWitness_of_long_chord_and_first_boundary_corner
        size_at_least_three region_convex factor_gt_one longSide shortSide
        different_sides long_chord corner_point_mem unit_point_mem
  | second shortSide different_sides corner_eq unit_point_mem =>
      rw [corner_eq] at corner_point_mem
      exact case7ResourceWitness_of_long_chord_and_second_boundary_corner
        size_at_least_three region_convex factor_gt_one longSide shortSide
        different_sides long_chord unit_point_mem corner_point_mem

lemma innerArea_positive_of_inward_point_family
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (boundaryPoint : Plane) (inwardPoint : ℝ → Plane)
    (factor_nonzero : factor ≠ 0)
    (boundary_point_mem :
      boundaryPoint ∈ square.dilatedInteriorRegion factor)
    (inward_near :
      ∀ {radius delta : ℝ}, 0 < radius → 0 < delta → delta < radius →
        inwardPoint delta ∈ Metric.ball boundaryPoint radius)
    (inward_inside :
      ∀ {delta : ℝ}, 0 < delta → delta ≤ 1 / 2 →
        inwardPoint delta ∈
          Set.pi univ fun _ => Ioo (1 : ℝ) ((size : ℝ) - 1)) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  let region := square.dilatedInteriorRegion factor
  have region_open : IsOpen region :=
    square.isOpen_dilatedInteriorRegion factor_nonzero
  rcases Metric.isOpen_iff.mp region_open boundaryPoint boundary_point_mem with
    ⟨radius, radius_positive, ball_subset⟩
  let delta := min (radius / 2) (1 / 2)
  have delta_positive : 0 < delta := by
    dsimp [delta]
    positivity
  have delta_lt_radius : delta < radius := by
    have delta_at_most_half_radius : delta ≤ radius / 2 := min_le_left _ _
    linarith
  have delta_at_most_half : delta ≤ 1 / 2 := min_le_right _ _
  have interior_point_in_region : inwardPoint delta ∈ region :=
    ball_subset (inward_near radius_positive delta_positive delta_lt_radius)
  let innerOpen : Set Plane :=
    Set.pi univ fun _ => Ioo (1 : ℝ) ((size : ℝ) - 1)
  have inner_open : IsOpen innerOpen := by
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have interior_point_in_inner_open : inwardPoint delta ∈ innerOpen :=
    inward_inside delta_positive delta_at_most_half
  let openPatch := region ∩ innerOpen
  have open_patch_open : IsOpen openPatch := region_open.inter inner_open
  have open_patch_nonempty : openPatch.Nonempty :=
    ⟨inwardPoint delta, interior_point_in_region,
      interior_point_in_inner_open⟩
  have open_patch_volume_positive : 0 < volume openPatch :=
    open_patch_open.measure_pos volume open_patch_nonempty
  have open_patch_subset :
      openPatch ⊆ region ∩
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
    intro point point_mem
    refine ⟨point_mem.1, ?_⟩
    constructor
    · intro coordinate
      exact (point_mem.2 coordinate (mem_univ coordinate)).1.le
    · intro coordinate
      exact (point_mem.2 coordinate (mem_univ coordinate)).2.le
  have patch_measure_bound :
      volume openPatch ≤
        volume (region ∩
          Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) :=
    measure_mono open_patch_subset
  rw [NagamochiResource.innerArea,
    Measure.restrict_apply
      (square.measurableSet_dilatedInteriorRegion factor_nonzero)]
  simpa only [region] using
    open_patch_volume_positive.trans_le patch_measure_bound

inductive InnerBoundarySide
  | bottom
  | top
  | left
  | right

def InnerBoundarySide.toBoundarySide :
    InnerBoundarySide → NagamochiResource.BoundarySide
  | .bottom => .bottom
  | .top => .top
  | .left => .left
  | .right => .right

def InnerBoundarySide.toEdgePoint :
    InnerBoundarySide → NagamochiResource.EdgePoint
  | .bottom => .bottom
  | .top => .top
  | .left => .left
  | .right => .right

noncomputable def InnerBoundarySide.firstConnectionPoint
    (side : InnerBoundarySide) (size : ℕ) : Plane :=
  match side with
  | .bottom => NagamochiResource.BoundarySide.left.pointAt size 1
  | .top =>
      NagamochiResource.BoundarySide.left.pointAt size ((size : ℝ) - 1)
  | .left => NagamochiResource.BoundarySide.bottom.pointAt size 1
  | .right =>
      NagamochiResource.BoundarySide.bottom.pointAt size ((size : ℝ) - 1)

noncomputable def InnerBoundarySide.secondConnectionPoint
    (side : InnerBoundarySide) (size : ℕ) : Plane :=
  match side with
  | .bottom => NagamochiResource.BoundarySide.right.pointAt size 1
  | .top =>
      NagamochiResource.BoundarySide.right.pointAt size ((size : ℝ) - 1)
  | .left => NagamochiResource.BoundarySide.top.pointAt size 1
  | .right =>
      NagamochiResource.BoundarySide.top.pointAt size ((size : ℝ) - 1)

lemma firstBoundaryCornerConnection_of_mem
    {size : ℕ} {region : Set Plane} (side : InnerBoundarySide)
    (point_mem : side.firstConnectionPoint size ∈ region) :
    BoundaryCornerConnection size region side.toBoundarySide
      side.toEdgePoint.firstCornerPoint := by
  cases side with
  | bottom =>
      exact .first .left (by decide) rfl
        (by simpa [InnerBoundarySide.firstConnectionPoint] using point_mem)
  | top =>
      exact .second .left (by decide) rfl
        (by simpa [InnerBoundarySide.firstConnectionPoint] using point_mem)
  | left =>
      exact .first .bottom (by decide) rfl
        (by simpa [InnerBoundarySide.firstConnectionPoint] using point_mem)
  | right =>
      exact .second .bottom (by decide) rfl
        (by simpa [InnerBoundarySide.firstConnectionPoint] using point_mem)

lemma secondBoundaryCornerConnection_of_mem
    {size : ℕ} {region : Set Plane} (side : InnerBoundarySide)
    (point_mem : side.secondConnectionPoint size ∈ region) :
    BoundaryCornerConnection size region side.toBoundarySide
      side.toEdgePoint.secondCornerPoint := by
  cases side with
  | bottom =>
      exact .first .right (by decide) rfl
        (by simpa [InnerBoundarySide.secondConnectionPoint] using point_mem)
  | top =>
      exact .second .right (by decide) rfl
        (by simpa [InnerBoundarySide.secondConnectionPoint] using point_mem)
  | left =>
      exact .first .top (by decide) rfl
        (by simpa [InnerBoundarySide.secondConnectionPoint] using point_mem)
  | right =>
      exact .second .top (by decide) rfl
        (by simpa [InnerBoundarySide.secondConnectionPoint] using point_mem)

def InnerBoundarySide.centerInStrip
    (side : InnerBoundarySide) (size : ℕ) (square : PlacedSquare)
    (factor : ℝ) : Prop :=
  match side with
  | .bottom =>
      1 ≤ factor * square.center.x ∧
        factor * square.center.x ≤ (size : ℝ) - 1 ∧
          factor * square.center.y ≤ 1
  | .top =>
      1 ≤ factor * square.center.x ∧
        factor * square.center.x ≤ (size : ℝ) - 1 ∧
          (size : ℝ) - 1 ≤ factor * square.center.y
  | .left =>
      factor * square.center.x ≤ 1 ∧
        1 ≤ factor * square.center.y ∧
          factor * square.center.y ≤ (size : ℝ) - 1
  | .right =>
      (size : ℝ) - 1 ≤ factor * square.center.x ∧
        1 ≤ factor * square.center.y ∧
          factor * square.center.y ≤ (size : ℝ) - 1

lemma gridPointWitness_of_center_in_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor) :
    GridPointWitness size (square.dilatedInteriorRegion factor)
      side.toEdgePoint := by
  cases side with
  | bottom =>
      exact bottomGridPointWitness_of_center_in_bottom_strip_geometry square
        size_at_least_three factor_gt_one inside_container center_in_strip.2.2
  | top =>
      exact topGridPointWitness_of_center_in_top_strip_geometry square
        size_at_least_three factor_gt_one inside_container center_in_strip.2.2
  | left =>
      exact leftGridPointWitness_of_center_in_left_strip_geometry square
        size_at_least_three factor_gt_one inside_container center_in_strip.1
  | right =>
      exact rightGridPointWitness_of_center_in_right_strip_geometry square
        size_at_least_three factor_gt_one inside_container center_in_strip.1

lemma score_gt_one_of_case7_edge_strip_long_chord_and_connections
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor)
    (long_chord :
      NagamochiResource.HasBoundaryChord size side.toBoundarySide
        (square.dilatedInteriorRegion factor) factor)
    (connect_first_corner :
      BoundaryCornerConnection size (square.dilatedInteriorRegion factor)
        side.toBoundarySide side.toEdgePoint.firstCornerPoint)
    (connect_second_corner :
      BoundaryCornerConnection size (square.dilatedInteriorRegion factor)
        side.toBoundarySide side.toEdgePoint.secondCornerPoint) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have grid_point := gridPointWitness_of_center_in_edge_strip_geometry
    square side size_at_least_three factor_gt_one inside_container
    center_in_strip
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
  exact case7ResourceWitness_of_long_chord_and_grid_point
    size_at_least_three (square.convex_dilatedInteriorRegion factor)
    factor_gt_one side.toBoundarySide long_chord side.toEdgePoint grid_point
    connect_first_corner connect_second_corner

lemma score_gt_one_of_case7_edge_strip_long_chord_without_grid_corners
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor)
    (long_chord :
      NagamochiResource.HasBoundaryChord size side.toBoundarySide
        (square.dilatedInteriorRegion factor) factor)
    (first_corner_not_mem :
      NagamochiResource.cornerPoint size side.toEdgePoint.firstCornerPoint ∉
        square.dilatedInteriorRegion factor)
    (second_corner_not_mem :
      NagamochiResource.cornerPoint size side.toEdgePoint.secondCornerPoint ∉
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have grid_point := gridPointWitness_of_center_in_edge_strip_geometry
    square side size_at_least_three factor_gt_one inside_container
    center_in_strip
  obtain ⟨coordinate, coordinate_mem, edge_point_mem⟩ :=
    edge_mem_of_gridPointWitness_of_no_corner_points side.toEdgePoint
      grid_point first_corner_not_mem second_corner_not_mem
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
  exact .oppositeAndEdge side.toBoundarySide coordinate side.toEdgePoint
    factor factor_gt_one long_chord coordinate_mem edge_point_mem

inductive Case7EdgeStripOutcome
    (size : ℕ) (region : Set Plane) (side : InnerBoundarySide) : Prop
  | scored
      (score : 1 < NagamochiResource.measure size region)
  | firstDisconnected
      (corner_point_mem :
        NagamochiResource.cornerPoint size side.toEdgePoint.firstCornerPoint ∈
          region)
      (connection_point_not_mem : side.firstConnectionPoint size ∉ region)
  | secondDisconnected
      (corner_point_mem :
        NagamochiResource.cornerPoint size side.toEdgePoint.secondCornerPoint ∈
          region)
      (connection_point_not_mem : side.secondConnectionPoint size ∉ region)

lemma case7EdgeStripOutcome_of_long_chord
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor)
    (long_chord :
      NagamochiResource.HasBoundaryChord size side.toBoundarySide
        (square.dilatedInteriorRegion factor) factor) :
    Case7EdgeStripOutcome size (square.dilatedInteriorRegion factor) side := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_measurable :=
    square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have region_convex := square.convex_dilatedInteriorRegion factor
  have grid_point := gridPointWitness_of_center_in_edge_strip_geometry
    square side size_at_least_three factor_gt_one inside_container
    center_in_strip
  cases grid_point with
  | edge coordinate coordinate_mem edge_point_mem =>
      have score :
          1 < NagamochiResource.measure size
            (square.dilatedInteriorRegion factor) := by
        apply score_gt_one_of_case7_resource_witness region_measurable
        exact .oppositeAndEdge side.toBoundarySide coordinate side.toEdgePoint
          factor factor_gt_one long_chord coordinate_mem edge_point_mem
      exact Case7EdgeStripOutcome.scored score
  | firstCorner corner_point_mem =>
      by_cases connection_point_mem :
          side.firstConnectionPoint size ∈ square.dilatedInteriorRegion factor
      · have score :
            1 < NagamochiResource.measure size
              (square.dilatedInteriorRegion factor) := by
          apply score_gt_one_of_case7_resource_witness region_measurable
          exact case7ResourceWitness_of_long_chord_and_boundary_connection
            size_at_least_three region_convex factor_gt_one side.toBoundarySide
            long_chord side.toEdgePoint.firstCornerPoint corner_point_mem
            (firstBoundaryCornerConnection_of_mem side connection_point_mem)
        exact Case7EdgeStripOutcome.scored score
      · exact .firstDisconnected corner_point_mem connection_point_mem
  | secondCorner corner_point_mem =>
      by_cases connection_point_mem :
          side.secondConnectionPoint size ∈ square.dilatedInteriorRegion factor
      · have score :
            1 < NagamochiResource.measure size
              (square.dilatedInteriorRegion factor) := by
          apply score_gt_one_of_case7_resource_witness region_measurable
          exact case7ResourceWitness_of_long_chord_and_boundary_connection
            size_at_least_three region_convex factor_gt_one side.toBoundarySide
            long_chord side.toEdgePoint.secondCornerPoint corner_point_mem
            (secondBoundaryCornerConnection_of_mem side connection_point_mem)
        exact Case7EdgeStripOutcome.scored score
      · exact .secondDisconnected corner_point_mem connection_point_mem

def InnerBoundarySide.point
    (side : InnerBoundarySide) (size : ℕ) (coordinate : ℝ) : Plane :=
  match side with
  | .bottom => ![coordinate, (1 : ℝ)]
  | .top => ![coordinate, (size : ℝ) - 1]
  | .left => ![(1 : ℝ), coordinate]
  | .right => ![(size : ℝ) - 1, coordinate]

noncomputable def InnerBoundarySide.inwardPoint
    (side : InnerBoundarySide) (size : ℕ) (coordinate delta : ℝ)
    (positiveTangent : Bool) : Plane :=
  let tangentCoordinate :=
    if positiveTangent then coordinate + delta / 2 else coordinate - delta / 2
  match side with
  | .bottom => ![tangentCoordinate, 1 + delta / 2]
  | .top => ![tangentCoordinate, (size : ℝ) - 1 - delta / 2]
  | .left => ![1 + delta / 2, tangentCoordinate]
  | .right => ![(size : ℝ) - 1 - delta / 2, tangentCoordinate]

lemma innerArea_positive_of_innerBoundaryPoint_mem
    {size : ℕ} (square : PlacedSquare) {factor coordinate : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (coordinate_at_least_one : 1 ≤ coordinate)
    (coordinate_at_most_size_sub_one : coordinate ≤ (size : ℝ) - 1)
    (boundary_point_mem :
      side.point size coordinate ∈ square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  by_cases coordinate_in_left_half : coordinate ≤ (size : ℝ) / 2
  · apply innerArea_positive_of_inward_point_family square
      (side.point size coordinate)
      (fun delta => side.inwardPoint size coordinate delta true)
      factor_nonzero boundary_point_mem
    · intro radius delta radius_positive delta_positive delta_lt_radius
      rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
      intro axis
      cases side <;> fin_cases axis <;>
        simp [InnerBoundarySide.point, InnerBoundarySide.inwardPoint,
          abs_of_nonneg delta_positive.le] <;> linarith
    · intro delta delta_positive delta_at_most_half axis axis_mem
      cases side <;> fin_cases axis <;>
        simp [InnerBoundarySide.inwardPoint] <;>
        constructor <;> linarith
  · have coordinate_in_right_half : (size : ℝ) / 2 < coordinate :=
      lt_of_not_ge coordinate_in_left_half
    apply innerArea_positive_of_inward_point_family square
      (side.point size coordinate)
      (fun delta => side.inwardPoint size coordinate delta false)
      factor_nonzero boundary_point_mem
    · intro radius delta radius_positive delta_positive delta_lt_radius
      rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
      intro axis
      cases side <;> fin_cases axis <;>
        simp [InnerBoundarySide.point, InnerBoundarySide.inwardPoint,
          abs_of_nonneg delta_positive.le] <;> linarith
    · intro delta delta_positive delta_at_most_half axis axis_mem
      cases side <;> fin_cases axis <;>
        simp [InnerBoundarySide.inwardPoint] <;>
        constructor <;> linarith

lemma innerArea_positive_of_unitCornerPoint_mem
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (unit_corner_mem :
      ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  apply innerArea_positive_of_inward_point_family square
    ![(1 : ℝ), 1] (fun delta => ![1 + delta, 1 + delta])
    factor_nonzero unit_corner_mem
  · intro radius delta radius_positive delta_positive delta_lt_radius
    rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
    intro coordinate
    fin_cases coordinate <;>
      simp [abs_of_nonneg delta_positive.le, delta_lt_radius]
  · intro delta delta_positive delta_at_most_half coordinate coordinate_mem
    fin_cases coordinate <;>
      change 1 < 1 + delta ∧ 1 + delta < (size : ℝ) - 1 <;>
      constructor <;> linarith

lemma innerArea_positive_of_rightUnitCornerPoint_mem
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (unit_corner_mem :
      ![(size : ℝ) - 1, (1 : ℝ)] ∈
        square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  apply innerArea_positive_of_inward_point_family square
    ![(size : ℝ) - 1, (1 : ℝ)]
    (fun delta => ![(size : ℝ) - 1 - delta, 1 + delta])
    factor_nonzero unit_corner_mem
  · intro radius delta radius_positive delta_positive delta_lt_radius
    rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
    intro coordinate
    fin_cases coordinate <;>
      simp [abs_of_nonneg delta_positive.le, delta_lt_radius]
  · intro delta delta_positive delta_at_most_half coordinate coordinate_mem
    fin_cases coordinate
    · change 1 < (size : ℝ) - 1 - delta ∧
        (size : ℝ) - 1 - delta < (size : ℝ) - 1
      constructor <;> linarith
    · change 1 < 1 + delta ∧ 1 + delta < (size : ℝ) - 1
      constructor <;> linarith

lemma innerArea_positive_of_topUnitCornerPoint_mem
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (unit_corner_mem :
      ![(1 : ℝ), (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  apply innerArea_positive_of_inward_point_family square
    ![(1 : ℝ), (size : ℝ) - 1]
    (fun delta => ![1 + delta, (size : ℝ) - 1 - delta])
    factor_nonzero unit_corner_mem
  · intro radius delta radius_positive delta_positive delta_lt_radius
    rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
    intro coordinate
    fin_cases coordinate <;>
      simp [abs_of_nonneg delta_positive.le, delta_lt_radius]
  · intro delta delta_positive delta_at_most_half coordinate coordinate_mem
    fin_cases coordinate
    · change 1 < 1 + delta ∧ 1 + delta < (size : ℝ) - 1
      constructor <;> linarith
    · change 1 < (size : ℝ) - 1 - delta ∧
        (size : ℝ) - 1 - delta < (size : ℝ) - 1
      constructor <;> linarith

lemma innerArea_positive_of_topRightUnitCornerPoint_mem
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (unit_corner_mem :
      ![(size : ℝ) - 1, (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  apply innerArea_positive_of_inward_point_family square
    ![(size : ℝ) - 1, (size : ℝ) - 1]
    (fun delta =>
      ![(size : ℝ) - 1 - delta, (size : ℝ) - 1 - delta])
    factor_nonzero unit_corner_mem
  · intro radius delta radius_positive delta_positive delta_lt_radius
    rw [Metric.mem_ball, dist_pi_lt_iff radius_positive]
    intro coordinate
    fin_cases coordinate <;>
      simp [abs_of_nonneg delta_positive.le, delta_lt_radius]
  · intro delta delta_positive delta_at_most_half coordinate coordinate_mem
    fin_cases coordinate <;>
      change 1 < (size : ℝ) - 1 - delta ∧
        (size : ℝ) - 1 - delta < (size : ℝ) - 1 <;>
      constructor <;> linarith

lemma innerArea_positive_of_horizontal_center_point_mem
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (center_x_at_least_one : 1 ≤ factor * square.center.x)
    (center_x_at_most_size_sub_one :
      factor * square.center.x ≤ (size : ℝ) - 1)
    (horizontal_center_point_mem :
      ![factor * square.center.x, (1 : ℝ)] ∈
        square.dilatedInteriorRegion factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  exact innerArea_positive_of_innerBoundaryPoint_mem square .bottom
    size_at_least_three factor_nonzero center_x_at_least_one
    center_x_at_most_size_sub_one
    (by simpa [InnerBoundarySide.point] using horizontal_center_point_mem)

lemma innerArea_positive_of_bottom_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_one : 1 ≤ factor * square.center.x)
    (center_x_at_most_size_sub_one :
      factor * square.center.x ≤ (size : ℝ) - 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have horizontal_center_point_mem :=
    square.horizontalCenterPoint_mem_dilatedInteriorRegion_any_frame
      factor_gt_one inside_container center_y_at_most_one
  exact innerArea_positive_of_horizontal_center_point_mem square
    size_at_least_three factor_positive.ne' center_x_at_least_one
    center_x_at_most_size_sub_one horizontal_center_point_mem

lemma innerArea_positive_of_top_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_one : 1 ≤ factor * square.center.x)
    (center_x_at_most_size_sub_one :
      factor * square.center.x ≤ (size : ℝ) - 1)
    (center_y_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.y) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have boundary_point_mem :=
    square.topHorizontalCenterPoint_mem_dilatedInteriorRegion_any_frame
      factor_gt_one inside_container center_y_at_least_size_sub_one
  exact innerArea_positive_of_innerBoundaryPoint_mem square .top
    size_at_least_three factor_positive.ne' center_x_at_least_one
    center_x_at_most_size_sub_one
    (by simpa [InnerBoundarySide.point] using boundary_point_mem)

lemma innerArea_positive_of_left_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_least_one : 1 ≤ factor * square.center.y)
    (center_y_at_most_size_sub_one :
      factor * square.center.y ≤ (size : ℝ) - 1) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have boundary_point_mem :=
    square.verticalCenterPoint_mem_dilatedInteriorRegion_any_frame
      factor_gt_one inside_container center_x_at_most_one
  exact innerArea_positive_of_innerBoundaryPoint_mem square .left
    size_at_least_three factor_positive.ne' center_y_at_least_one
    center_y_at_most_size_sub_one
    (by simpa [InnerBoundarySide.point] using boundary_point_mem)

lemma innerArea_positive_of_right_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.x)
    (center_y_at_least_one : 1 ≤ factor * square.center.y)
    (center_y_at_most_size_sub_one :
      factor * square.center.y ≤ (size : ℝ) - 1) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have boundary_point_mem :=
    square.rightVerticalCenterPoint_mem_dilatedInteriorRegion_any_frame
      factor_gt_one inside_container center_x_at_least_size_sub_one
  exact innerArea_positive_of_innerBoundaryPoint_mem square .right
    size_at_least_three factor_positive.ne' center_y_at_least_one
    center_y_at_most_size_sub_one
    (by simpa [InnerBoundarySide.point] using boundary_point_mem)

lemma innerArea_positive_of_edge_strip_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor) :
    0 < NagamochiResource.innerArea size
      (square.dilatedInteriorRegion factor) := by
  cases side with
  | bottom =>
      exact innerArea_positive_of_bottom_edge_strip_geometry square
        size_at_least_three factor_gt_one inside_container
        center_in_strip.1 center_in_strip.2.1 center_in_strip.2.2
  | top =>
      exact innerArea_positive_of_top_edge_strip_geometry square
        size_at_least_three factor_gt_one inside_container
        center_in_strip.1 center_in_strip.2.1 center_in_strip.2.2
  | left =>
      exact innerArea_positive_of_left_edge_strip_geometry square
        size_at_least_three factor_gt_one inside_container
        center_in_strip.1 center_in_strip.2.1 center_in_strip.2.2
  | right =>
      exact innerArea_positive_of_right_edge_strip_geometry square
        size_at_least_three factor_gt_one inside_container
        center_in_strip.1 center_in_strip.2.1 center_in_strip.2.2

lemma score_gt_one_of_case5_geometry_and_corner_points
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1)
    (bottom_left_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor)
    (left_bottom_mem :
      NagamochiResource.cornerPoint size .leftBottom ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have unit_corner_mem :=
    square.unitCornerPoint_mem_dilatedInteriorRegion_of_center_le_one
      factor_gt_one cosine_nonnegative sine_nonnegative inside_container
      center_x_at_most_one center_y_at_most_one
  have inner_positive := innerArea_positive_of_unitCornerPoint_mem square
    size_at_least_three factor_nonzero unit_corner_mem
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have bottom_left_point_mem :
      ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using bottom_left_mem
  have left_bottom_point_mem :
      ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using left_bottom_mem
  have bottom_chord :
      NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact horizontal_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        bottom_left_point_mem unit_corner_mem
  have left_chord :
      NagamochiResource.HasBoundaryChord size .left
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact vertical_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        left_bottom_point_mem unit_corner_mem
  exact score_gt_one_of_case5_resource_bounds
    (firstSide := .bottom) (secondSide := .left)
    (firstKind := .bottomLeft) (secondKind := .leftBottom)
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
    inner_positive (by decide) (by decide) bottom_chord left_chord
    bottom_left_mem left_bottom_mem

lemma score_gt_one_of_case5_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have corner_points := square.case5CornerPoints_mem_dilatedInteriorRegion
    factor_gt_one cosine_nonnegative sine_nonnegative
    inside_container center_x_at_most_one center_y_at_most_one
  have bottom_left_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using corner_points.1
  have left_bottom_mem :
      NagamochiResource.cornerPoint size .leftBottom ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using corner_points.2
  exact score_gt_one_of_case5_geometry_and_corner_points square
    size_at_least_three factor_gt_one cosine_nonnegative sine_nonnegative
    inside_container center_x_at_most_one center_y_at_most_one
    bottom_left_mem left_bottom_mem

lemma score_gt_one_of_case5_any_frame
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_eq :=
    square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_inside :
      square.firstQuadrant.dilatedInteriorRegion factor ⊆
        containerRegion size := by
    rw [region_eq]
    exact inside_container
  have normalized_center_x :
      factor * square.firstQuadrant.center.x ≤ 1 := by
    simpa using center_x_at_most_one
  have normalized_center_y :
      factor * square.firstQuadrant.center.y ≤ 1 := by
    simpa using center_y_at_most_one
  have normalized_score := score_gt_one_of_case5_geometry
    square.firstQuadrant size_at_least_three factor_gt_one
    square.firstQuadrant_cosine_nonnegative
    square.firstQuadrant_sine_nonnegative normalized_inside
    normalized_center_x normalized_center_y
  rw [region_eq] at normalized_score
  exact normalized_score

lemma score_gt_one_of_case5_bottom_right
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.x)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have points := square.case5RightPoints_mem_dilatedInteriorRegion_any_frame
    factor_gt_one inside_container center_x_at_least_size_sub_one
    center_y_at_most_one
  have unit_corner_mem :
      ![(size : ℝ) - 1, (1 : ℝ)] ∈
        square.dilatedInteriorRegion factor := points.1
  have bottom_right_mem :
      NagamochiResource.cornerPoint size .bottomRight ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.1
  have right_bottom_mem :
      NagamochiResource.cornerPoint size .rightBottom ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.2
  have inner_positive := innerArea_positive_of_rightUnitCornerPoint_mem square
    size_at_least_three factor_nonzero unit_corner_mem
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have bottom_right_point_mem :
      ![(size : ℝ) - 9 / 10, (1 : ℝ)] ∈
        square.dilatedInteriorRegion factor := points.2.1
  have right_bottom_point_mem :
      ![(size : ℝ) - 1, (9 / 10 : ℝ)] ∈
        square.dilatedInteriorRegion factor := points.2.2
  have bottom_chord :
      NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨(size : ℝ) - 1, (size : ℝ) - 9 / 10, by norm_num,
      ?_, ?_⟩
    · intro coordinate coordinate_mem
      constructor
      · linarith [coordinate_mem.1]
      · exact coordinate_mem.2.le
    · exact horizontal_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        unit_corner_mem bottom_right_point_mem
  have right_chord :
      NagamochiResource.HasBoundaryChord size .right
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact vertical_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        right_bottom_point_mem unit_corner_mem
  exact score_gt_one_of_case5_resource_bounds
    (firstSide := .bottom) (secondSide := .right)
    (firstKind := .bottomRight) (secondKind := .rightBottom)
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
    inner_positive (by decide) (by decide) bottom_chord right_chord
    bottom_right_mem right_bottom_mem

lemma score_gt_one_of_case5_top_left
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.y) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have points := square.case5TopPoints_mem_dilatedInteriorRegion_any_frame
    factor_gt_one inside_container center_x_at_most_one
    center_y_at_least_size_sub_one
  have unit_corner_mem :
      ![(1 : ℝ), (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor := points.1
  have left_top_mem :
      NagamochiResource.cornerPoint size .leftTop ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.1
  have top_left_mem :
      NagamochiResource.cornerPoint size .topLeft ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.2
  have inner_positive := innerArea_positive_of_topUnitCornerPoint_mem square
    size_at_least_three factor_nonzero unit_corner_mem
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have left_top_point_mem :
      ![(1 : ℝ), (size : ℝ) - 9 / 10] ∈
        square.dilatedInteriorRegion factor := points.2.1
  have top_left_point_mem :
      ![(9 / 10 : ℝ), (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor := points.2.2
  have left_chord :
      NagamochiResource.HasBoundaryChord size .left
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨(size : ℝ) - 1, (size : ℝ) - 9 / 10, by norm_num,
      ?_, ?_⟩
    · intro coordinate coordinate_mem
      constructor
      · linarith [coordinate_mem.1]
      · exact coordinate_mem.2.le
    · exact vertical_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        unit_corner_mem left_top_point_mem
  have top_chord :
      NagamochiResource.HasBoundaryChord size .top
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact horizontal_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        top_left_point_mem unit_corner_mem
  exact score_gt_one_of_case5_resource_bounds
    (firstSide := .left) (secondSide := .top)
    (firstKind := .leftTop) (secondKind := .topLeft)
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
    inner_positive (by decide) (by decide) left_chord top_chord
    left_top_mem top_left_mem

lemma score_gt_one_of_case5_top_right
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.x)
    (center_y_at_least_size_sub_one :
      (size : ℝ) - 1 ≤ factor * square.center.y) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have points :=
    square.case5TopRightPoints_mem_dilatedInteriorRegion_any_frame
      factor_gt_one inside_container center_x_at_least_size_sub_one
      center_y_at_least_size_sub_one
  have unit_corner_mem :
      ![(size : ℝ) - 1, (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor := points.1
  have right_top_mem :
      NagamochiResource.cornerPoint size .rightTop ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.1
  have top_right_mem :
      NagamochiResource.cornerPoint size .topRight ∈
        square.dilatedInteriorRegion factor := by
    simpa [NagamochiResource.cornerPoint] using points.2.2
  have inner_positive :=
    innerArea_positive_of_topRightUnitCornerPoint_mem square
      size_at_least_three factor_nonzero unit_corner_mem
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have right_top_point_mem :
      ![(size : ℝ) - 1, (size : ℝ) - 9 / 10] ∈
        square.dilatedInteriorRegion factor := points.2.1
  have top_right_point_mem :
      ![(size : ℝ) - 9 / 10, (size : ℝ) - 1] ∈
        square.dilatedInteriorRegion factor := points.2.2
  have right_chord :
      NagamochiResource.HasBoundaryChord size .right
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨(size : ℝ) - 1, (size : ℝ) - 9 / 10, by norm_num,
      ?_, ?_⟩
    · intro coordinate coordinate_mem
      constructor
      · linarith [coordinate_mem.1]
      · exact coordinate_mem.2.le
    · exact vertical_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        unit_corner_mem right_top_point_mem
  have top_chord :
      NagamochiResource.HasBoundaryChord size .top
        (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨(size : ℝ) - 1, (size : ℝ) - 9 / 10, by norm_num,
      ?_, ?_⟩
    · intro coordinate coordinate_mem
      constructor
      · linarith [coordinate_mem.1]
      · exact coordinate_mem.2.le
    · exact horizontal_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (by norm_num)
        unit_corner_mem top_right_point_mem
  exact score_gt_one_of_case5_resource_bounds
    (firstSide := .right) (secondSide := .top)
    (firstKind := .rightTop) (secondKind := .topRight)
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
    inner_positive (by decide) (by decide) right_chord top_chord
    right_top_mem top_right_mem

lemma score_gt_one_of_case5
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_in_corner_strip :
      factor * square.center.x ≤ 1 ∨
        (size : ℝ) - 1 ≤ factor * square.center.x)
    (center_y_in_corner_strip :
      factor * square.center.y ≤ 1 ∨
        (size : ℝ) - 1 ≤ factor * square.center.y) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  rcases center_x_in_corner_strip with center_x_low | center_x_high
  · rcases center_y_in_corner_strip with center_y_low | center_y_high
    · exact score_gt_one_of_case5_any_frame square size_at_least_three
        factor_gt_one inside_container center_x_low center_y_low
    · exact score_gt_one_of_case5_top_left square size_at_least_three
        factor_gt_one inside_container center_x_low center_y_high
  · rcases center_y_in_corner_strip with center_y_low | center_y_high
    · exact score_gt_one_of_case5_bottom_right square size_at_least_three
        factor_gt_one inside_container center_x_high center_y_low
    · exact score_gt_one_of_case5_top_right square size_at_least_three
        factor_gt_one inside_container center_x_high center_y_high

lemma score_gt_one_of_case7_opposite_and_edge_point
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : NagamochiResource.BoundarySide)
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite : HasOppositeBoundaryChord size square factor side)
    (kind : NagamochiResource.EdgePoint)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have chord := boundaryChord_of_opposite square factor_positive
    cosine_positive sine_positive side opposite
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
  exact .oppositeAndEdge side coordinate kind factor factor_gt_one
    chord coordinate_mem edge_point_mem

lemma score_gt_one_of_case7_bottom_opposite_and_edge_point
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (opposite : HasHorizontalOppositeChordWithin size square factor 1)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate .bottom ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  exact score_gt_one_of_case7_opposite_and_edge_point square .bottom
    factor_gt_one cosine_positive sine_positive opposite .bottom
    coordinate_mem edge_point_mem

lemma score_gt_one_of_case7_first_boundary_corner_and_edge_point
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : NagamochiResource.BoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (inner_positive :
      0 < NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor))
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.firstCornerPoint ∈
        square.dilatedInteriorRegion factor)
    (unit_point_mem :
      side.pointAt size 1 ∈ square.dilatedInteriorRegion factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint)
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
  exact case7ResourceWitness_of_first_boundary_corner_and_edge_point
    size_at_least_three (square.convex_dilatedInteriorRegion factor)
    inner_positive side corner_point_mem unit_point_mem coordinate_mem kind
    edge_point_mem

lemma score_gt_one_of_case7_second_boundary_corner_and_edge_point
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : NagamochiResource.BoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (inner_positive :
      0 < NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor))
    (unit_point_mem :
      side.pointAt size ((size : ℝ) - 1) ∈
        square.dilatedInteriorRegion factor)
    (corner_point_mem :
      NagamochiResource.cornerPoint size side.secondCornerPoint ∈
        square.dilatedInteriorRegion factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint)
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate kind ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
  exact case7ResourceWitness_of_second_boundary_corner_and_edge_point
    size_at_least_three (square.convex_dilatedInteriorRegion factor)
    inner_positive side unit_point_mem corner_point_mem coordinate_mem kind
    edge_point_mem

lemma score_gt_one_of_case7_bottom_corner_and_edge_point
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (inner_positive :
      0 < NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor))
    (unit_point_mem :
      ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor)
    (corner_point_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate .bottom ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  exact score_gt_one_of_case7_first_boundary_corner_and_edge_point square
    .bottom size_at_least_three factor_nonzero inner_positive corner_point_mem
    (by simpa [NagamochiResource.BoundarySide.pointAt] using unit_point_mem)
    coordinate_mem .bottom edge_point_mem

lemma score_gt_one_of_case7_both_bottom_corner_points
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_nonzero : factor ≠ 0)
    (inner_positive :
      0 < NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor))
    (bottom_left_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor)
    (bottom_right_mem :
      NagamochiResource.cornerPoint size .bottomRight ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_nonzero)
  exact case7ResourceWitness_of_two_boundary_corner_points
    size_at_least_three (square.convex_dilatedInteriorRegion factor)
    inner_positive .bottom bottom_left_mem bottom_right_mem

lemma score_gt_one_of_case7_two_boundary_corner_points_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_in_strip : side.centerInStrip size square factor)
    (first_point_mem :
      NagamochiResource.cornerPoint size
          side.toBoundarySide.firstCornerPoint ∈
        square.dilatedInteriorRegion factor)
    (second_point_mem :
      NagamochiResource.cornerPoint size
          side.toBoundarySide.secondCornerPoint ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have inner_positive := innerArea_positive_of_edge_strip_geometry square side
    size_at_least_three factor_gt_one inside_container center_in_strip
  apply score_gt_one_of_case7_resource_witness
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
  exact case7ResourceWitness_of_two_boundary_corner_points
    size_at_least_three (square.convex_dilatedInteriorRegion factor)
    inner_positive side.toBoundarySide first_point_mem second_point_mem

lemma score_gt_one_of_case7_bottom_corner_and_edge_point_geometry
    {size coordinate : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_one : 1 ≤ factor * square.center.x)
    (center_x_at_most_size_sub_one :
      factor * square.center.x ≤ (size : ℝ) - 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1)
    (unit_point_mem :
      ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor)
    (corner_point_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (edge_point_mem :
      NagamochiResource.edgePoint size coordinate .bottom ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have inner_positive := innerArea_positive_of_bottom_edge_strip_geometry square
    size_at_least_three factor_gt_one inside_container center_x_at_least_one
    center_x_at_most_size_sub_one center_y_at_most_one
  exact score_gt_one_of_case7_bottom_corner_and_edge_point square
    size_at_least_three factor_positive.ne' inner_positive unit_point_mem
    corner_point_mem coordinate_mem edge_point_mem

lemma score_gt_one_of_case7_both_bottom_corner_points_geometry
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_x_at_least_one : 1 ≤ factor * square.center.x)
    (center_x_at_most_size_sub_one :
      factor * square.center.x ≤ (size : ℝ) - 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1)
    (bottom_left_mem :
      NagamochiResource.cornerPoint size .bottomLeft ∈
        square.dilatedInteriorRegion factor)
    (bottom_right_mem :
      NagamochiResource.cornerPoint size .bottomRight ∈
        square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  exact score_gt_one_of_case7_two_boundary_corner_points_geometry square .bottom
    size_at_least_three factor_gt_one inside_container
    ⟨center_x_at_least_one, center_x_at_most_size_sub_one,
      center_y_at_most_one⟩
    bottom_left_mem bottom_right_mem

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

lemma score_gt_one_of_two_boundary_chords
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    {firstSide secondSide : NagamochiResource.BoundarySide}
    (region_measurable : MeasurableSet region)
    (factor_gt_one : 1 < factor)
    (different_sides : firstSide ≠ secondSide)
    (first_chord :
      NagamochiResource.HasBoundaryChord size firstSide region factor)
    (second_chord :
      NagamochiResource.HasBoundaryChord size secondSide region factor) :
    1 < NagamochiResource.measure size region := by
  apply score_gt_one_of_two_boundaryLine_chords factor_gt_one different_sides
  · exact NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable first_chord
  · exact NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable second_chord

lemma score_gt_one_of_half_area_and_boundary_chord
    {size : ℕ} {region : Set Plane} {factor : ℝ}
    {side : NagamochiResource.BoundarySide}
    (region_measurable : MeasurableSet region)
    (factor_gt_one : 1 < factor)
    (half_area :
      (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
        NagamochiResource.innerArea size region)
    (chord : NagamochiResource.HasBoundaryChord size side region factor) :
    1 < NagamochiResource.measure size region := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have half_factor_le_half_square :
      (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤
        (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) := by
    exact mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by nlinarith)) bot_le bot_le
  have boundary_lower_bound :
      (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤
        NagamochiResource.boundaryLines size region := by
    apply NagamochiResource.boundaryLines_lower_bound
    exact NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable chord
  have factor_score_gt_one : 1 < ENNReal.ofReal factor := by
    rw [ENNReal.one_lt_ofReal]
    exact factor_gt_one
  have half_times_two : (2 : ENNReal)⁻¹ * 2 = 1 := by
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    1 < ENNReal.ofReal factor := factor_score_gt_one
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal factor +
        (1 / 2 : ENNReal) * ENNReal.ofReal factor := by
      rw [show (1 / 2 : ENNReal) = 2⁻¹ by norm_num]
      calc
        ENNReal.ofReal factor = 1 * ENNReal.ofReal factor := by rw [one_mul]
        _ = (2⁻¹ * 2) * ENNReal.ofReal factor := by rw [half_times_two]
        _ = 2⁻¹ * ENNReal.ofReal factor +
            2⁻¹ * ENNReal.ofReal factor := by ring
    _ ≤ NagamochiResource.innerArea size region +
        NagamochiResource.boundaryLines size region :=
      add_le_add (half_factor_le_half_square.trans half_area) boundary_lower_bound
    _ ≤ NagamochiResource.measure size region :=
      NagamochiResource.innerArea_add_boundaryLines_le_measure size region

lemma score_gt_one_of_two_opposite_boundary_chords
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    {firstSide secondSide : NagamochiResource.BoundarySide}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (different_sides : firstSide ≠ secondSide)
    (first_opposite :
      HasOppositeBoundaryChord size square factor firstSide)
    (second_opposite :
      HasOppositeBoundaryChord size square factor secondSide) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  apply score_gt_one_of_two_boundary_chords
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
    factor_gt_one different_sides
  · exact boundaryChord_of_opposite square factor_positive cosine_positive
      sine_positive firstSide first_opposite
  · exact boundaryChord_of_opposite square factor_positive cosine_positive
      sine_positive secondSide second_opposite

def HasCase3ResourceWitness
    (size : ℕ) (square : PlacedSquare) (factor : ℝ) : Prop :=
  (∃ firstSide secondSide : NagamochiResource.BoundarySide,
    firstSide ≠ secondSide ∧
      HasOppositeBoundaryChord size square factor firstSide ∧
        HasOppositeBoundaryChord size square factor secondSide) ∨
  (∃ side : NagamochiResource.BoundarySide,
    HasOppositeBoundaryChord size square factor side ∧
      (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
        NagamochiResource.innerArea size
          (square.dilatedInteriorRegion factor))

lemma score_gt_one_of_case3_resource_witness
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (witness : HasCase3ResourceWitness size square factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  rcases witness with
    ⟨firstSide, secondSide, different_sides, first_opposite, second_opposite⟩ |
      ⟨side, opposite, half_area⟩
  · exact score_gt_one_of_two_opposite_boundary_chords square factor_gt_one
      cosine_positive sine_positive different_sides first_opposite second_opposite
  · apply score_gt_one_of_half_area_and_boundary_chord
      (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
      factor_gt_one half_area
    exact boundaryChord_of_opposite square factor_positive cosine_positive
      sine_positive side opposite

lemma score_gt_one_of_bottom_top_horizontalOpposite
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (bottom_opposite : HasHorizontalOppositeChordWithin size square factor 1)
    (top_opposite :
      HasHorizontalOppositeChordWithin size square factor ((size : ℝ) - 1)) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  exact score_gt_one_of_two_opposite_boundary_chords
    (firstSide := .bottom) (secondSide := .top) square factor_gt_one
    cosine_positive sine_positive (by decide) bottom_opposite top_opposite

lemma score_gt_one_of_two_long_boundary_chords
    {size : ℕ} {region : Set Plane} {firstLength secondLength : ℝ}
    {firstSide secondSide : NagamochiResource.BoundarySide}
    (region_measurable : MeasurableSet region)
    (first_length_gt_one : 1 < firstLength)
    (second_length_gt_one : 1 < secondLength)
    (different_sides : firstSide ≠ secondSide)
    (first_chord :
      NagamochiResource.HasBoundaryChord size firstSide region firstLength)
    (second_chord :
      NagamochiResource.HasBoundaryChord size secondSide region secondLength) :
    1 < NagamochiResource.measure size region := by
  have common_length_gt_one : 1 < min firstLength secondLength := by
    rw [lt_min_iff]
    exact ⟨first_length_gt_one, second_length_gt_one⟩
  apply score_gt_one_of_two_boundary_chords region_measurable
    common_length_gt_one different_sides
  · exact first_chord.mono (min_le_left _ _)
  · exact second_chord.mono (min_le_right _ _)

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
