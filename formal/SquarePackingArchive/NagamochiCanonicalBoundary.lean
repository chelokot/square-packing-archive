import SquarePackingArchive.NagamochiCanonicalPinned

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma canonicalPinned_horizontal_start_eq
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherLower 1 1 =
      canonicalPinnedFirstCutVertex tangentHalfAngle 0 := by
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have cosine_ne :
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ≠ 0 := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    apply div_ne_zero
    · nlinarith
    · positivity
  have one_minus_square_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  have center_x :
      (canonicalPinnedSquare tangentHalfAngle).center.x =
        (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 0 := by
    change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 0 = _
    simp [canonicalPinnedSquare, pinnedSquare]
  have center_y :
      (canonicalPinnedSquare tangentHalfAngle).center.y =
        (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 1 := by
    change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 1 = _
    simp [canonicalPinnedSquare, pinnedSquare]
  simp only [PlacedSquare.horizontalAdjacentOtherLower]
  rw [center_x, center_y]
  simp [canonicalPinnedSquare,
    canonicalPinnedFirstCutVertex,
    pinnedNegativeVertex, pinnedEdgeParameter, Frame.rotation_apply_zero,
    Frame.rotation_apply_one, pinnedSquare_frame]
  field_simp [denominator_ne, cosine_ne, one_minus_square_ne]
  ring

lemma canonicalPinned_horizontal_end_eq
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherUpper 1 1 =
      canonicalPinnedSecondCutVertex tangentHalfAngle 0 := by
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have cosine_ne :
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ≠ 0 := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    apply div_ne_zero
    · nlinarith
    · positivity
  have one_minus_square_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  have one_add_tangent_ne : 1 + tangentHalfAngle ≠ 0 := by linarith
  have center_x :
      (canonicalPinnedSquare tangentHalfAngle).center.x =
        (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 0 := by
    change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 0 = _
    simp [canonicalPinnedSquare, pinnedSquare]
  have center_y :
      (canonicalPinnedSquare tangentHalfAngle).center.y =
        (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 1 := by
    change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 1 = _
    simp [canonicalPinnedSquare, pinnedSquare]
  simp only [PlacedSquare.horizontalAdjacentOtherUpper]
  rw [center_x, center_y]
  simp [canonicalPinnedSquare, canonicalPinnedSecondCutVertex,
    pinnedNegativeVertex, pinnedEdgeParameter, Frame.rotation_apply_zero,
    Frame.rotation_apply_one, pinnedSquare_frame]
  field_simp [denominator_ne, cosine_ne, one_minus_square_ne,
    one_add_tangent_ne]
  ring

lemma canonicalPinned_horizontal_other_order
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentChordStart 1 1 ≤
        (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherLower 1 1 ∧
      (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherUpper 1 1 ≤
        (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentChordEnd 1 1 := by
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have cosine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) denominator_positive
  have sine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).sine := by
    simp only [Frame.ofTangentHalfAngle_sine]
    exact div_pos (by positivity) denominator_positive
  have one_minus_square_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  have frame_eq := canonicalPinnedSquare_frame tangentHalfAngle
  constructor
  · have difference :
        (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherLower 1 1 -
            (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentChordStart 1 1 =
          tangentHalfAngle /
            (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
      simp only [PlacedSquare.horizontalAdjacentOtherLower,
        PlacedSquare.horizontalAdjacentChordStart]
      rw [canonicalPinnedSquare_center_x, canonicalPinnedSquare_center_y]
      rw [frame_eq]
      simp [pinnedNegativeVertex, pinnedEdgeParameter,
        Frame.rotation_apply_zero, Frame.rotation_apply_one]
      field_simp [ne_of_gt cosine_positive, one_minus_square_ne]
      ring
    rw [← sub_nonneg, difference]
    exact div_nonneg tangent_positive.le cosine_positive.le
  · have difference :
        (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentChordEnd 1 1 -
            (canonicalPinnedSquare tangentHalfAngle).horizontalAdjacentOtherUpper 1 1 =
          ((1 - tangentHalfAngle) / (1 + tangentHalfAngle)) /
            (Frame.ofTangentHalfAngle tangentHalfAngle).sine := by
      simp only [PlacedSquare.horizontalAdjacentChordEnd,
        PlacedSquare.horizontalAdjacentOtherUpper]
      rw [canonicalPinnedSquare_center_x, canonicalPinnedSquare_center_y]
      rw [frame_eq]
      simp [pinnedNegativeVertex, pinnedEdgeParameter,
        Frame.rotation_apply_zero, Frame.rotation_apply_one]
      have one_add_ne : 1 + tangentHalfAngle ≠ 0 := by linarith
      field_simp [ne_of_gt cosine_positive, ne_of_gt sine_positive, one_add_ne,
        one_minus_square_ne]
      ring
    rw [← sub_nonneg, difference]
    positivity

end SquarePackingArchive.Nagamochi
