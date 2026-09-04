import SquarePackingArchive.NagamochiHalfArea

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

noncomputable def horizontalCapHeight
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  height - factor * square.center.y +
    factor * (square.frame.cosine + square.frame.sine) / 2

noncomputable def dilatedNegativeVertex
    (square : PlacedSquare) (factor : ℝ) : Plane :=
  (square.dilatedPoint factor (-factor / 2) (-factor / 2)).toPlane

lemma dilatedNegativeVertex_add_rotation
    (square : PlacedSquare) (factor localX localY : ℝ) :
    dilatedNegativeVertex square factor +
        square.frame.rotation ![localX + factor / 2, localY + factor / 2] =
      (square.dilatedPoint factor localX localY).toPlane := by
  funext coordinate
  fin_cases coordinate <;>
    simp [dilatedNegativeVertex, Point.toPlane, PlacedSquare.dilatedPoint,
      Frame.place, Frame.rotation_apply_zero, Frame.rotation_apply_one] <;> ring

lemma horizontalLowerCap_subset_triangle
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height) :
    square.dilatedInteriorRegion factor ∩ {point | point 1 < height} ⊆
      orientedTranslatedRightTriangleRegion
        (dilatedNegativeVertex square factor) square.frame
        (horizontalCapHeight square factor height / square.frame.sine)
        (horizontalCapHeight square factor height / square.frame.cosine) := by
  intro point point_mem
  obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem.1
  have horizontal_positive : 0 < localX + factor / 2 := by
    have lower_bound := (abs_lt.mp localX_bound).1
    linarith
  have vertical_positive : 0 < localY + factor / 2 := by
    have lower_bound := (abs_lt.mp localY_bound).1
    linarith
  have vertical_eq := congrArg Point.y point_eq
  simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at vertical_eq
  have point_below : point 1 < height := point_mem.2
  have below_cut :
      square.frame.sine * (localX + factor / 2) +
          square.frame.cosine * (localY + factor / 2) <
        horizontalCapHeight square factor height := by
    dsimp [horizontalCapHeight]
    nlinarith
  have horizontal_at_most :
      localX + factor / 2 ≤ horizontalCapHeight square factor height / square.frame.sine := by
    rw [le_div_iff₀ sine_positive]
    nlinarith [mul_pos cosine_positive vertical_positive]
  have triangle_height_identity :
      (horizontalCapHeight square factor height / square.frame.cosine) *
          (1 - (localX + factor / 2) /
            (horizontalCapHeight square factor height / square.frame.sine)) =
        (horizontalCapHeight square factor height -
          square.frame.sine * (localX + factor / 2)) / square.frame.cosine := by
    field_simp [cap_positive.ne', cosine_positive.ne', sine_positive.ne']
  refine ⟨![localX + factor / 2, localY + factor / 2], ?_, ?_⟩
  · change
      (localX + factor / 2 ∈ Ioc 0 _) ∧
        (localY + factor / 2 ∈ Ioc 0 _)
    refine ⟨⟨horizontal_positive, horizontal_at_most⟩, vertical_positive, ?_⟩
    dsimp only [Matrix.cons_val_zero]
    rw [triangle_height_identity, le_div_iff₀ cosine_positive]
    nlinarith
  · rw [PlacedSquare.fromPlaneCenter_transform, dilatedNegativeVertex_add_rotation]
    simpa only [Plane.toPlane_toPoint] using congrArg Point.toPlane point_eq.symm

lemma volume_horizontalLowerCap_le
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height) :
    volume (square.dilatedInteriorRegion factor ∩ {point | point 1 < height}) ≤
      ENNReal.ofReal
        ((horizontalCapHeight square factor height / square.frame.sine) *
          (horizontalCapHeight square factor height / square.frame.cosine) / 2) := by
  calc
    _ ≤ volume (orientedTranslatedRightTriangleRegion
        (dilatedNegativeVertex square factor) square.frame
        (horizontalCapHeight square factor height / square.frame.sine)
        (horizontalCapHeight square factor height / square.frame.cosine)) :=
      measure_mono (horizontalLowerCap_subset_triangle square factor_positive
        cosine_positive sine_positive cap_positive)
    _ = _ := volume_orientedTranslatedRightTriangleRegion _ _
      (div_pos cap_positive sine_positive) (div_pos cap_positive cosine_positive).le

lemma horizontalAdjacentChord_of_cap_bounds
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_le_cosine :
      horizontalCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine :
      horizontalCapHeight square factor height ≤ factor * square.frame.sine) :
    ∀ coordinate ∈ Ioo (square.horizontalAdjacentChordStart factor height)
        (square.horizontalAdjacentChordEnd factor height),
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  have scaled_unit :
      (height - factor * square.center.y) * square.frame.cosine ^ 2 +
          (height - factor * square.center.y) * square.frame.sine ^ 2 =
        height - factor * square.center.y := by
    linear_combination (height - factor * square.center.y) * square.frame.unit
  apply square.horizontalAdjacentChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive
  · dsimp [PlacedSquare.horizontalAdjacentOtherLower,
      PlacedSquare.horizontalAdjacentChordStart]
    rw [add_le_add_iff_left, div_le_div_iff₀ sine_positive cosine_positive]
    dsimp [horizontalCapHeight] at cap_le_cosine
    nlinarith
  · dsimp [PlacedSquare.horizontalAdjacentOtherUpper,
      PlacedSquare.horizontalAdjacentChordEnd]
    rw [add_le_add_iff_left, div_le_div_iff₀ sine_positive cosine_positive]
    dsimp [horizontalCapHeight] at cap_le_sine
    nlinarith

lemma horizontalAdjacentChord_length_eq_cap
    (square : PlacedSquare) {factor height : ℝ}
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine) :
    square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height =
      horizontalCapHeight square factor height /
        (square.frame.sine * square.frame.cosine) := by
  rw [square.horizontalAdjacentChord_length cosine_positive.ne' sine_positive.ne']
  dsimp [horizontalCapHeight]
  field_simp
  ring

lemma horizontalAdjacentChord_straddles_negativeVertex
    (square : PlacedSquare) {factor height : ℝ}
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height) :
    square.horizontalAdjacentChordStart factor height < dilatedNegativeVertex square factor 0 ∧
      dilatedNegativeVertex square factor 0 < square.horizontalAdjacentChordEnd factor height := by
  have scaled_unit :
      factor * square.frame.cosine ^ 2 + factor * square.frame.sine ^ 2 = factor := by
    linear_combination factor * square.frame.unit
  have first_gap :
      dilatedNegativeVertex square factor 0 - square.horizontalAdjacentChordStart factor height =
        horizontalCapHeight square factor height * square.frame.sine / square.frame.cosine := by
    dsimp [dilatedNegativeVertex, Point.toPlane, PlacedSquare.dilatedPoint, Frame.place,
      PlacedSquare.horizontalAdjacentChordStart, horizontalCapHeight]
    field_simp [cosine_positive.ne']
    nlinarith
  have second_gap :
      square.horizontalAdjacentChordEnd factor height - dilatedNegativeVertex square factor 0 =
        horizontalCapHeight square factor height * square.frame.cosine / square.frame.sine := by
    dsimp [dilatedNegativeVertex, Point.toPlane, PlacedSquare.dilatedPoint, Frame.place,
      PlacedSquare.horizontalAdjacentChordEnd, horizontalCapHeight]
    field_simp [sine_positive.ne']
    nlinarith
  constructor
  · apply sub_pos.mp
    rw [first_gap]
    positivity
  · apply sub_pos.mp
    rw [second_gap]
    positivity

lemma horizontalAdjacentChord_inside_segment_of_missing_corners
    (square : PlacedSquare) {factor height segmentStart segmentEnd : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height)
    (cap_le_cosine :
      horizontalCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine :
      horizontalCapHeight square factor height ≤ factor * square.frame.sine)
    (vertex_in_segment : dilatedNegativeVertex square factor 0 ∈ Icc segmentStart segmentEnd)
    (first_corner_missing : ![segmentStart, height] ∉ square.dilatedInteriorRegion factor)
    (second_corner_missing : ![segmentEnd, height] ∉ square.dilatedInteriorRegion factor) :
    Ioo (square.horizontalAdjacentChordStart factor height)
        (square.horizontalAdjacentChordEnd factor height) ⊆
      Icc segmentStart segmentEnd := by
  have straddles := horizontalAdjacentChord_straddles_negativeVertex square
    cosine_positive sine_positive cap_positive
  have chord_inside := horizontalAdjacentChord_of_cap_bounds square factor_positive
    cosine_positive sine_positive cap_le_cosine cap_le_sine
  have lower_bound : segmentStart ≤ square.horizontalAdjacentChordStart factor height := by
    by_contra bound_fails
    apply first_corner_missing
    exact chord_inside segmentStart
      ⟨lt_of_not_ge bound_fails, vertex_in_segment.1.trans_lt straddles.2⟩
  have upper_bound : square.horizontalAdjacentChordEnd factor height ≤ segmentEnd := by
    by_contra bound_fails
    apply second_corner_missing
    exact chord_inside segmentEnd
      ⟨straddles.1.trans_le vertex_in_segment.2, lt_of_not_ge bound_fails⟩
  intro coordinate coordinate_mem
  exact ⟨lower_bound.trans coordinate_mem.1.le, coordinate_mem.2.le.trans upper_bound⟩

lemma horizontalCapArea_lt_half_chord
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height)
    (cap_le_cosine :
      horizontalCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine :
      horizontalCapHeight square factor height ≤ factor * square.frame.sine) :
    (horizontalCapHeight square factor height / square.frame.sine) *
        (horizontalCapHeight square factor height / square.frame.cosine) / 2 <
      (square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height) / 2 := by
  have cap_sq_le_cosine := mul_self_le_mul_self cap_positive.le cap_le_cosine
  have cap_sq_le_sine := mul_self_le_mul_self cap_positive.le cap_le_sine
  have scaled_unit :
      factor ^ 2 * square.frame.cosine ^ 2 + factor ^ 2 * square.frame.sine ^ 2 =
        factor ^ 2 := by
    linear_combination factor ^ 2 * square.frame.unit
  have cap_lt_one : horizontalCapHeight square factor height < 1 := by
    nlinarith
  rw [horizontalAdjacentChord_length_eq_cap square cosine_positive sine_positive]
  have chord_positive :
      0 < horizontalCapHeight square factor height /
        (square.frame.sine * square.frame.cosine) := by positivity
  have area_identity :
      (horizontalCapHeight square factor height / square.frame.sine) *
          (horizontalCapHeight square factor height / square.frame.cosine) / 2 =
        horizontalCapHeight square factor height *
          (horizontalCapHeight square factor height /
            (square.frame.sine * square.frame.cosine)) / 2 := by
    field_simp
  rw [area_identity]
  nlinarith

lemma horizontalLowerCap_compensated
    (square : PlacedSquare) {factor height segmentStart segmentEnd : ℝ}
    (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height)
    (cap_le_cosine :
      horizontalCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine :
      horizontalCapHeight square factor height ≤ factor * square.frame.sine)
    (chord_inside_segment :
      Ioo (square.horizontalAdjacentChordStart factor height)
          (square.horizontalAdjacentChordEnd factor height) ⊆
        Icc segmentStart segmentEnd) :
    volume (square.dilatedInteriorRegion factor ∩ {point | point 1 < height}) ≤
      (1 / 2 : ENNReal) * horizontalSegmentMeasure segmentStart segmentEnd height
        (square.dilatedInteriorRegion factor) := by
  have area_bound := volume_horizontalLowerCap_le square factor_positive
    cosine_positive sine_positive cap_positive
  have area_lt_half_chord := horizontalCapArea_lt_half_chord square factor_positive
    factor_at_most cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
  have chord_bound := horizontalSegmentMeasure_lower_bound
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')
    chord_inside_segment (horizontalAdjacentChord_of_cap_bounds square factor_positive
      cosine_positive sine_positive cap_le_cosine cap_le_sine)
  calc
    _ ≤ ENNReal.ofReal
        ((horizontalCapHeight square factor height / square.frame.sine) *
          (horizontalCapHeight square factor height / square.frame.cosine) / 2) := area_bound
    _ ≤ ENNReal.ofReal
        ((square.horizontalAdjacentChordEnd factor height -
          square.horizontalAdjacentChordStart factor height) / 2) :=
      ENNReal.ofReal_le_ofReal area_lt_half_chord.le
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal
        (square.horizontalAdjacentChordEnd factor height -
          square.horizontalAdjacentChordStart factor height) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num [div_eq_mul_inv, mul_comm]
    _ ≤ _ := mul_le_mul le_rfl chord_bound bot_le bot_le

lemma score_gt_one_of_single_bottom_adjacent_cut
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor 1)
    (cap_le_cosine : horizontalCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalCapHeight square factor 1 ≤ factor * square.frame.sine)
    (other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ .bottom →
          other.inwardThreshold size ≤ other.inwardNormal point) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have chord_inside := horizontalAdjacentChord_of_cap_bounds square factor_positive
    cosine_positive sine_positive cap_le_cosine cap_le_sine
  have direct_inside_segment :
      Ioo (square.horizontalAdjacentChordStart factor 1)
          (square.horizontalAdjacentChordEnd factor 1) ⊆
        Icc (9 / 10) ((size : ℝ) - 9 / 10) := by
    intro coordinate coordinate_mem
    have point_mem := chord_inside coordinate coordinate_mem
    have left_bound := other_sides_inside _ point_mem .left (by intro equality; cases equality)
    have right_bound := other_sides_inside _ point_mem .right (by intro equality; cases equality)
    change 1 ≤ coordinate at left_bound
    change 1 - (size : ℝ) ≤ -coordinate at right_bound
    constructor <;> linarith
  have loss_compensated :
      volume (square.dilatedInteriorRegion factor ∩ {point | point 1 < 1}) ≤
        NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) := by
    exact (horizontalLowerCap_compensated square factor_positive factor_at_most
      cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
      direct_inside_segment).trans
        (NagamochiResource.boundaryLine_le_boundaryLines size .bottom _)
  have area_covered :
      square.dilatedInteriorRegion factor ⊆
        (square.dilatedInteriorRegion factor ∩
          Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        (square.dilatedInteriorRegion factor ∩ {point | point 1 < 1}) := by
    intro point point_mem
    by_cases point_below : point 1 < 1
    · exact Or.inr ⟨point_mem, point_below⟩
    · left
      refine ⟨point_mem, (mem_innerRectangle_iff_inward_bounds size point).2 ?_⟩
      intro other
      by_cases same_side : other = .bottom
      · subst other
        exact le_of_not_gt point_below
      · exact other_sides_inside point point_mem other same_side
  apply score_gt_one_of_compensated_inner_area factor_gt_one
      (loss := volume (square.dilatedInteriorRegion factor ∩ {point | point 1 < 1}))
  · rw [← square.volume_dilatedInteriorRegion factor_positive.le,
      NagamochiResource.innerArea, Measure.restrict_apply
        (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
    exact (measure_mono area_covered).trans (measure_union_le _ _)
  · exact loss_compensated

lemma horizontalCapHeight_positive_of_line_intersects
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (line_intersects :
      ∃ coordinate, ![coordinate, height] ∈ square.dilatedInteriorRegion factor) :
    0 < horizontalCapHeight square factor height := by
  obtain ⟨coordinate, point_mem⟩ := line_intersects
  obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive _).1 point_mem
  have localX_positive : 0 < localX + factor / 2 := by
    linarith [(abs_lt.mp localX_bound).1]
  have localY_positive : 0 < localY + factor / 2 := by
    linarith [(abs_lt.mp localY_bound).1]
  have vertical_eq := congrArg Point.y point_eq
  simp only [Plane.toPoint, Matrix.cons_val_one, Matrix.cons_val_zero,
    PlacedSquare.dilatedPoint, Frame.place] at vertical_eq
  dsimp [horizontalCapHeight]
  nlinarith [mul_pos sine_positive localX_positive,
    mul_pos cosine_positive localY_positive]

lemma score_gt_one_of_single_bottom_crossing_positive_frame
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_above : 1 ≤ factor * square.center.y)
    (line_intersects :
      ∃ coordinate, ![coordinate, 1] ∈ square.dilatedInteriorRegion factor)
    (other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ .bottom →
          other.inwardThreshold size ≤ other.inwardNormal point) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  by_cases offset_bound :
      |1 - factor * square.center.y| ≤
        factor * |square.frame.cosine - square.frame.sine| / 2
  · obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
      exists_horizontal_chord_of_center_offset_le square factor_positive
        cosine_positive sine_positive offset_bound
    exact score_gt_one_of_single_inner_boundary_crossing square .bottom
      factor_gt_one center_above other_sides_inside
      (boundaryChord_of_line_chord_and_other_sides_inside .bottom
        length_bound chord_inside other_sides_inside)
  · have cap_positive := horizontalCapHeight_positive_of_line_intersects square
      factor_positive cosine_positive sine_positive line_intersects
    have offset_large := lt_of_not_ge offset_bound
    rw [abs_of_nonpos (by linarith : 1 - factor * square.center.y ≤ 0)] at offset_large
    have difference_bound := mul_le_mul_of_nonneg_left
      (le_abs_self (square.frame.cosine - square.frame.sine)) factor_positive.le
    have reverse_difference_bound := mul_le_mul_of_nonneg_left
      (neg_le_abs (square.frame.cosine - square.frame.sine)) factor_positive.le
    have cap_le_cosine :
        horizontalCapHeight square factor 1 ≤ factor * square.frame.cosine := by
      dsimp [horizontalCapHeight]
      nlinarith
    have cap_le_sine :
        horizontalCapHeight square factor 1 ≤ factor * square.frame.sine := by
      dsimp [horizontalCapHeight]
      nlinarith
    exact score_gt_one_of_single_bottom_adjacent_cut square factor_gt_one
      factor_at_most cosine_positive sine_positive cap_positive cap_le_cosine
      cap_le_sine other_sides_inside

lemma score_gt_one_of_single_bottom_crossing
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (center_above : 1 ≤ factor * square.center.y)
    (line_intersects :
      ∃ coordinate, ![coordinate, 1] ∈ square.dilatedInteriorRegion factor)
    (other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ .bottom →
          other.inwardThreshold size ≤ other.inwardNormal point) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_intersection :
      ∃ coordinate, ![coordinate, 1] ∈ square.firstQuadrant.dilatedInteriorRegion factor := by
    simpa only [region_eq] using line_intersects
  have normalized_center : 1 ≤ factor * square.firstQuadrant.center.y := by
    simpa only [square.firstQuadrant_center] using center_above
  have normalized_other_sides :
      ∀ point ∈ square.firstQuadrant.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ .bottom →
          other.inwardThreshold size ≤ other.inwardNormal point := by
    simpa only [region_eq] using other_sides_inside
  have normalized_score :
      1 < NagamochiResource.measure size (square.firstQuadrant.dilatedInteriorRegion factor) := by
    by_cases axis_aligned :
        square.firstQuadrant.frame.cosine = 0 ∨ square.firstQuadrant.frame.sine = 0
    · obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
        exists_horizontal_chord_of_axis_aligned square.firstQuadrant factor_positive
          square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
          axis_aligned normalized_intersection
      exact score_gt_one_of_single_inner_boundary_crossing square.firstQuadrant .bottom
        factor_gt_one normalized_center normalized_other_sides
        (boundaryChord_of_line_chord_and_other_sides_inside .bottom
          length_bound chord_inside normalized_other_sides)
    · push Not at axis_aligned
      exact score_gt_one_of_single_bottom_crossing_positive_frame square.firstQuadrant
        factor_gt_one factor_at_most
        (lt_of_le_of_ne square.firstQuadrant_cosine_nonnegative axis_aligned.1.symm)
        (lt_of_le_of_ne square.firstQuadrant_sine_nonnegative axis_aligned.2.symm)
        normalized_center normalized_intersection normalized_other_sides
  simpa only [region_eq] using normalized_score

end SquarePackingArchive.Nagamochi
