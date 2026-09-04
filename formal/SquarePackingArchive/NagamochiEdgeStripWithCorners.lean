import SquarePackingArchive.NagamochiBoundaryAnchor
import SquarePackingArchive.NagamochiCapLowerBound

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma upperCap_vertical_projection_inside
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_le_cosine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.sine)
    {point : Plane} (point_mem : point ∈ square.dilatedInteriorRegion factor)
    (above_cut : height ≤ point 1) :
    ![point 0, height] ∈ square.dilatedInteriorRegion factor := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem
  have horizontal_eq := congrArg Point.x point_eq
  have vertical_eq := congrArg Point.y point_eq
  simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at horizontal_eq vertical_eq
  let descent := point 1 - height
  have descent_nonnegative : 0 ≤ descent := sub_nonneg.mpr above_cut
  let projectedX := localX - descent * square.frame.sine
  let projectedY := localY - descent * square.frame.cosine
  have horizontal_upper : projectedX < factor / 2 := by
    dsimp [projectedX]
    nlinarith [abs_lt.mp horizontal_bound, mul_nonneg descent_nonnegative sine_positive.le]
  have vertical_upper : projectedY < factor / 2 := by
    dsimp [projectedY]
    nlinarith [abs_lt.mp vertical_bound, mul_nonneg descent_nonnegative cosine_positive.le]
  have horizontal_margin_identity :
      horizontalUpperCapHeight square factor height - square.frame.sine * (factor / 2 - projectedX) =
        square.frame.cosine * (factor / 2 - localY) + square.frame.cosine ^ 2 * descent := by
    dsimp [horizontalUpperCapHeight, projectedX, descent]
    linear_combination -vertical_eq - (point 1 - height) * square.frame.unit
  have vertical_margin_identity :
      horizontalUpperCapHeight square factor height - square.frame.cosine * (factor / 2 - projectedY) =
        square.frame.sine * (factor / 2 - localX) + square.frame.sine ^ 2 * descent := by
    dsimp [horizontalUpperCapHeight, projectedY, descent]
    linear_combination -vertical_eq - (point 1 - height) * square.frame.unit
  have horizontal_lower : -(factor / 2) < projectedX := by
    have positive := mul_pos cosine_positive (sub_pos.mpr (abs_lt.mp vertical_bound).2)
    have remainder := mul_nonneg (sq_nonneg square.frame.cosine) descent_nonnegative
    nlinarith
  have vertical_lower : -(factor / 2) < projectedY := by
    have positive := mul_pos sine_positive (sub_pos.mpr (abs_lt.mp horizontal_bound).2)
    have remainder := mul_nonneg (sq_nonneg square.frame.sine) descent_nonnegative
    nlinarith
  rw [square.mem_dilatedInteriorRegion_iff factor_positive]
  refine ⟨projectedX, projectedY, abs_lt.mpr ⟨horizontal_lower, horizontal_upper⟩,
    abs_lt.mpr ⟨vertical_lower, vertical_upper⟩, ?_⟩
  rw [Point.mk.injEq]
  constructor
  · dsimp [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place, projectedX, projectedY]
    nlinarith
  · dsimp [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place, projectedX, projectedY, descent]
    linear_combination vertical_eq + (point 1 - height) * square.frame.unit

lemma bottom_line_clipped_of_missing_horizontal_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_two : 2 ≤ size)
    (factor_gt_one : 1 < factor)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    ∀ horizontal, ![horizontal, 1] ∈ square.dilatedInteriorRegion factor →
      horizontal ∈ Icc (9 / 10 : ℝ) ((size : ℝ) - 9 / 10) := by
  have active := bottom_active_of_edge_strip square fits factor_gt_one size_at_least_two
    center_horizontal center_below
  intro horizontal point_mem
  constructor
  · by_contra outside
    exact first_missing (first_corner_mem_of_active_and_coordinate_below
      (square.convex_dilatedInteriorRegion factor) active point_mem (lt_of_not_ge outside))
  · by_contra outside
    exact second_missing (second_corner_mem_of_active_and_coordinate_above
      (square.convex_dilatedInteriorRegion factor) active point_mem (lt_of_not_ge outside))

lemma upperCap_le_innerArea_add_narrow_strip_loss
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (cap_positive : 0 < horizontalUpperCapHeight square factor 1)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ENNReal.ofReal (horizontalUpperCapHeight square factor 1 / 5) := by
  let cap := horizontalUpperCapHeight square factor 1
  let region := square.dilatedInteriorRegion factor
  let leftStrip := Icc ![(9 / 10 : ℝ), 1] ![1, 1 + cap]
  let rightStrip := Icc ![(size : ℝ) - 1, 1] ![(size : ℝ) - 9 / 10, 1 + cap]
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have component_sum_bound : square.frame.cosine + square.frame.sine ≤ 3 / 2 := by
    nlinarith [square.frame.unit, sq_nonneg (square.frame.cosine - square.frame.sine)]
  have cap_lt_one : cap < 1 := by
    dsimp [cap, horizontalUpperCapHeight]
    nlinarith [mul_le_mul_of_nonneg_left component_sum_bound factor_positive.le]
  have horizontal_clipped := bottom_line_clipped_of_missing_horizontal_corners square fits
    (by omega) factor_gt_one center_horizontal center_below first_missing second_missing
  have covered : region ∩ {point | 1 ≤ point 1} ⊆
      (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪ (leftStrip ∪ rightStrip) := by
    rintro point ⟨point_mem, point_above⟩
    have horizontal_bounds := horizontal_clipped (point 0)
      (upperCap_vertical_projection_inside square factor_positive cosine_positive sine_positive
        cap_le_cosine cap_le_sine point_mem point_above)
    have vertical_upper : point 1 ≤ 1 + cap := by
      obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ :=
        (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem
      have vertical_eq := congrArg Point.y point_eq
      simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at vertical_eq
      dsimp [cap, horizontalUpperCapHeight]
      nlinarith [mul_le_mul_of_nonneg_right (abs_lt.mp horizontal_bound).2.le sine_positive.le,
        mul_le_mul_of_nonneg_right (abs_lt.mp vertical_bound).2.le cosine_positive.le]
    by_cases left_bound : 1 ≤ point 0
    · by_cases right_bound : point 0 ≤ (size : ℝ) - 1
      · left
        refine ⟨point_mem, ?_, ?_⟩
        · intro axis
          fin_cases axis <;> assumption
        · intro axis
          fin_cases axis
          · exact right_bound
          · change point 1 ≤ (size : ℝ) - 1
            linarith
      · right
        right
        constructor <;> intro axis <;> fin_cases axis
        · exact (lt_of_not_ge right_bound).le
        · exact point_above
        · exact horizontal_bounds.2
        · exact vertical_upper
    · right
      left
      constructor <;> intro axis <;> fin_cases axis
      · exact horizontal_bounds.1
      · exact point_above
      · exact (lt_of_not_ge left_bound).le
      · exact vertical_upper
  have left_volume : volume leftStrip = ENNReal.ofReal (cap / 10) := by
    simp [leftStrip, Real.volume_Icc_pi, Fin.prod_univ_two]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 9 / 10)]
    congr 1
    ring
  have right_volume : volume rightStrip = ENNReal.ofReal (cap / 10) := by
    simp [rightStrip, Real.volume_Icc_pi, Fin.prod_univ_two]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 9 / 10)]
    congr 1
    ring
  have loss_volume : volume leftStrip + volume rightStrip = ENNReal.ofReal (cap / 5) := by
    rw [left_volume, right_volume, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have covered_bound : volume (region ∩ {point | 1 ≤ point 1}) ≤
      volume (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) +
        (volume leftStrip + volume rightStrip) :=
    (measure_mono covered).trans
      ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
  rw [loss_volume] at covered_bound
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact covered_bound

theorem area_add_half_bottom_line_gt_half_of_bottom_adjacent_missing_horizontal_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    (1 / 2 : ENNReal) < NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
  let cap := horizontalUpperCapHeight square factor 1
  let region := square.dilatedInteriorRegion factor
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bottom_bound := square.dilatedCenterY_halfExtent_le factor_positive
    cosine_positive.le sine_positive.le inside_container
  have sum_gt_one : 1 < square.frame.cosine + square.frame.sine := by
    nlinarith [square.frame.unit, mul_pos cosine_positive sine_positive]
  have cap_lower : square.frame.cosine + square.frame.sine - 1 ≤ cap := by
    dsimp [cap, horizontalUpperCapHeight]
    nlinarith [mul_nonneg (sub_nonneg.mpr factor_gt_one.le)
      (add_nonneg cosine_positive.le sine_positive.le)]
  have cap_positive : 0 < cap := by linarith
  have real_strict := cap_score_gt_half_add_fifth_height cosine_positive sine_positive
    square.frame.unit cap_lower
  have area_bound := horizontalUpperCap_volume_lower_bound square factor_positive
    cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
  have section_bound := horizontalUpperCap_section_lower_bound square factor_positive
    cosine_positive sine_positive cap_le_cosine cap_le_sine
  have cap_bound := upperCap_le_innerArea_add_narrow_strip_loss square fits size_at_least_three
    factor_gt_one factor_at_most cosine_positive sine_positive center_horizontal center_below
    cap_positive cap_le_cosine cap_le_sine first_missing second_missing
  have clipped := bottom_line_clipped_of_missing_horizontal_corners square fits (by omega)
    factor_gt_one center_horizontal center_below first_missing second_missing
  have full_section_eq : volume {horizontal : ℝ | ![horizontal, 1] ∈ region} =
      NagamochiResource.boundaryLine size .bottom region := by
    rw [NagamochiResource.boundaryLine, horizontalSegmentMeasure_apply
      (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
    congr 1
    ext horizontal
    exact ⟨fun point_inside => ⟨clipped horizontal point_inside, point_inside⟩,
      fun point_inside => point_inside.2⟩
  have half_encode (value : ℝ) : ENNReal.ofReal (value / 2) =
      (1 / 2 : ENNReal) * ENNReal.ofReal value := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul, mul_comm]
  have encoded_strict : (1 / 2 : ENNReal) + ENNReal.ofReal (cap / 5) <
      ENNReal.ofReal ((cap / square.frame.sine) * (cap / square.frame.cosine) / 2) +
        (1 / 2 : ENNReal) * ENNReal.ofReal (cap / (square.frame.sine * square.frame.cosine)) := by
    have strict := (ENNReal.ofReal_lt_ofReal_iff (by positivity :
      0 < (cap / square.frame.sine) * (cap / square.frame.cosine) / 2 +
        cap / (square.frame.sine * square.frame.cosine) / 2)).2 real_strict
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      half_encode (cap / (square.frame.sine * square.frame.cosine))] at strict
    have half_constant : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    rw [half_constant] at strict
    exact strict
  have score_bound : ENNReal.ofReal ((cap / square.frame.sine) * (cap / square.frame.cosine) / 2) +
      (1 / 2 : ENNReal) * ENNReal.ofReal (cap / (square.frame.sine * square.frame.cosine)) ≤
      (NagamochiResource.innerArea size region + (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom region) +
        ENNReal.ofReal (cap / 5) := by
    have line_bound : (1 / 2 : ENNReal) * ENNReal.ofReal (cap / (square.frame.sine * square.frame.cosine)) ≤
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom region := by
      change ENNReal.ofReal (cap / (square.frame.sine * square.frame.cosine)) ≤
        volume {horizontal : ℝ | ![horizontal, 1] ∈ region} at section_bound
      rw [full_section_eq] at section_bound
      exact mul_le_mul le_rfl section_bound bot_le bot_le
    calc
      _ ≤ (NagamochiResource.innerArea size region + ENNReal.ofReal (cap / 5)) +
          (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom region :=
        add_le_add (area_bound.trans cap_bound) line_bound
      _ = _ := by ac_rfl
  exact lt_of_add_lt_add_right (encoded_strict.trans_le score_bound)

theorem area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners_nonnegative_frame
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    (1 / 2 : ENNReal) < NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have clipped := bottom_line_clipped_of_missing_horizontal_corners square fits (by omega)
    factor_gt_one center_horizontal center_below first_missing second_missing
  have score_of_long (intervalStart intervalEnd : ℝ)
      (length_bound : factor ≤ intervalEnd - intervalStart)
      (chord_inside : ∀ horizontal ∈ Ioo intervalStart intervalEnd,
        ![horizontal, 1] ∈ square.dilatedInteriorRegion factor) :
      (1 / 2 : ENNReal) < NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
    have chord : NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) factor :=
      ⟨intervalStart, intervalEnd, length_bound,
        fun horizontal horizontal_mem => clipped horizontal (chord_inside horizontal horizontal_mem),
        chord_inside⟩
    have line_bound := mul_le_mul (a := (1 / 2 : ENNReal)) le_rfl
      (NagamochiResource.boundaryLine_lower_bound_of_chord
        (square.measurableSet_dilatedInteriorRegion factor_positive.ne') chord) bot_le bot_le
    have half_strict : (1 / 2 : ENNReal) < (1 / 2 : ENNReal) * ENNReal.ofReal factor := by
      simpa only [one_mul, mul_comm] using ENNReal.mul_lt_mul_left
        (a := (1 / 2 : ENNReal)) (by norm_num) (by finiteness)
        (ENNReal.one_lt_ofReal.mpr factor_gt_one)
    exact (half_strict.trans_le line_bound).trans_le (le_add_of_nonneg_left bot_le)
  by_cases axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0
  · obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
      exists_horizontal_chord_of_axis_aligned square factor_positive cosine_nonnegative
        sine_nonnegative axis_aligned ⟨_, anchor⟩
    exact score_of_long intervalStart intervalEnd length_bound chord_inside
  push Not at axis_aligned
  have cosine_positive : 0 < square.frame.cosine :=
    lt_of_le_of_ne cosine_nonnegative axis_aligned.1.symm
  have sine_positive : 0 < square.frame.sine :=
    lt_of_le_of_ne sine_nonnegative axis_aligned.2.symm
  by_cases offset_bound : |1 - factor * square.center.y| ≤
      factor * |square.frame.cosine - square.frame.sine| / 2
  · obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
      exists_horizontal_chord_of_center_offset_le square factor_positive
        cosine_positive sine_positive offset_bound
    exact score_of_long intervalStart intervalEnd length_bound chord_inside
  have offset_large := lt_of_not_ge offset_bound
  rw [abs_of_nonneg (sub_nonneg.mpr center_below)] at offset_large
  have difference_bound := mul_le_mul_of_nonneg_left
    (le_abs_self (square.frame.cosine - square.frame.sine)) factor_positive.le
  have reverse_difference_bound := mul_le_mul_of_nonneg_left
    (neg_le_abs (square.frame.cosine - square.frame.sine)) factor_positive.le
  apply area_add_half_bottom_line_gt_half_of_bottom_adjacent_missing_horizontal_corners square fits
    size_at_least_three factor_gt_one factor_at_most cosine_positive sine_positive
    inside_container center_horizontal center_below _ _ first_missing second_missing
  all_goals dsimp [horizontalUpperCapHeight]; nlinarith

theorem area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    (1 / 2 : ENNReal) < NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq (zero_lt_one.trans factor_gt_one)
  have normalized_score :=
    area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners_nonnegative_frame
      square.firstQuadrant ((square.firstQuadrant_fits_iff side).2 fits)
      size_at_least_three factor_gt_one factor_at_most
      square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
      (region_eq.symm ▸ inside_container)
      (by simpa using center_horizontal) (by simpa using center_below)
      (region_eq.symm ▸ first_missing) (region_eq.symm ▸ second_missing)
  rwa [region_eq] at normalized_score

theorem continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor) :
    (1 / 2 : ENNReal) < NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) := by
  exact (area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits size_at_least_three factor_gt_one factor_at_most inside_container center_horizontal
    center_below first_missing second_missing).trans_le
      (add_le_add le_rfl (NagamochiResource.boundaryLine_le_boundaryLines size .bottom _))

theorem score_gt_nineteen_twentieths_of_bottom_strip_with_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor)
    (kind : NagamochiResource.CornerPoint)
    (point_mem : NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor) :
    (19 / 20 : ENNReal) < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have continuous_strict := continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits size_at_least_three factor_gt_one factor_at_most inside_container center_horizontal
    center_below first_missing second_missing
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem kind
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne') point_mem
  have sum_strict := (ENNReal.add_lt_add_iff_right (by finiteness : (9 / 20 : ENNReal) ≠ ⊤)).2
    continuous_strict
  have score_identity : (1 / 2 : ENNReal) + 9 / 20 = 19 / 20 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [score_identity] at sum_strict
  exact (sum_strict.trans_le (add_le_add le_rfl corner_bound)).trans_le
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size _)

end SquarePackingArchive.Nagamochi
