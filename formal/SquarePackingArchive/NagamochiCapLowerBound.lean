import SquarePackingArchive.NagamochiCut

namespace SquarePackingArchive

open MeasureTheory Set

lemma PlacedSquare.dilatedPoint_mem_closure
    (square : PlacedSquare) {factor localX localY : ℝ}
    (factor_positive : 0 < factor)
    (horizontal_bound : |localX| ≤ factor / 2)
    (vertical_bound : |localY| ≤ factor / 2) :
    (square.dilatedPoint factor localX localY).toPlane ∈
      closure (square.dilatedInteriorRegion factor) := by
  have local_bound {coordinate : ℝ} (bound : |coordinate| ≤ factor / 2) :
      |coordinate / factor| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos factor_positive, div_le_iff₀ factor_positive]
    linarith
  have coordinates_mem : ![localX / factor, localY / factor] ∈ unitSquareClosure := by
    intro axis _
    fin_cases axis
    · change -(1 / 2) ≤ localX / factor ∧ localX / factor ≤ 1 / 2
      exact abs_le.mp (local_bound horizontal_bound)
    · change -(1 / 2) ≤ localY / factor ∧ localY / factor ≤ 1 / 2
      exact abs_le.mp (local_bound vertical_bound)
  have source_mem := square.transform_mem_closure_interiorRegion coordinates_mem
  have dilation_continuous : Continuous (dilatePlane factor) := by
    unfold dilatePlane
    fun_prop
  have image_mem := image_closure_subset_closure_image dilation_continuous
    (show dilatePlane factor (square.transform ![localX / factor, localY / factor]) ∈
      dilatePlane factor '' closure square.interiorRegion from ⟨_, source_mem, rfl⟩)
  have point_identity : (square.dilatedPoint factor localX localY).toPlane =
      dilatePlane factor (square.transform ![localX / factor, localY / factor]) := by
    funext axis
    fin_cases axis <;>
      simp [dilatePlane, PlacedSquare.transform, PlacedSquare.dilatedPoint, Point.toPlane,
        Frame.place, Matrix.vecHead, Matrix.vecTail,
        Frame.rotation_apply_zero, Frame.rotation_apply_one] <;>
      field_simp
  rw [point_identity]
  exact image_mem

namespace Nagamochi

lemma horizontalLowerCap_volume_lower_bound
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalCapHeight square factor height)
    (cap_le_cosine : horizontalCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalCapHeight square factor height ≤ factor * square.frame.sine) :
    ENNReal.ofReal
      ((horizontalCapHeight square factor height / square.frame.sine) *
        (horizontalCapHeight square factor height / square.frame.cosine) / 2) ≤
      volume (square.dilatedInteriorRegion factor ∩ {point | point 1 ≤ height}) := by
  let cap := horizontalCapHeight square factor height
  let width := cap / square.frame.sine
  let depth := cap / square.frame.cosine
  have width_positive : 0 < width := div_pos cap_positive sine_positive
  have depth_positive : 0 < depth := div_pos cap_positive cosine_positive
  have width_at_most : width ≤ factor := (div_le_iff₀ sine_positive).2 cap_le_sine
  have depth_at_most : depth ≤ factor := (div_le_iff₀ cosine_positive).2 cap_le_cosine
  have negative_bound : |-(factor / 2)| ≤ factor / 2 := by
    rw [abs_neg, abs_of_pos (half_pos factor_positive)]
  have shifted_bound {coordinate : ℝ} (nonnegative : 0 ≤ coordinate)
      (upper : coordinate ≤ factor) : |coordinate - factor / 2| ≤ factor / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have origin_mem : dilatedNegativeVertex square factor ∈
      closure (square.dilatedInteriorRegion factor) := by
    apply square.dilatedPoint_mem_closure factor_positive <;>
      simpa only [neg_div] using negative_bound
  have vertex_identity (horizontal vertical : ℝ) :
      dilatedNegativeVertex square factor + square.frame.rotation ![horizontal, vertical] =
        (square.dilatedPoint factor (horizontal - factor / 2)
          (vertical - factor / 2)).toPlane := by
    simpa only [sub_add_cancel] using dilatedNegativeVertex_add_rotation square factor
      (horizontal - factor / 2) (vertical - factor / 2)
  have horizontal_mem : dilatedNegativeVertex square factor + square.frame.rotation ![width, 0] ∈
      closure (square.dilatedInteriorRegion factor) := by
    rw [vertex_identity]
    apply square.dilatedPoint_mem_closure factor_positive
      (shifted_bound width_positive.le width_at_most)
    simpa using negative_bound
  have vertical_mem : dilatedNegativeVertex square factor + square.frame.rotation ![0, depth] ∈
      closure (square.dilatedInteriorRegion factor) := by
    rw [vertex_identity]
    apply square.dilatedPoint_mem_closure factor_positive _
      (shifted_bound depth_positive.le depth_at_most)
    simpa using negative_bound
  have region_nonempty : (square.dilatedInteriorRegion factor).Nonempty :=
    ⟨_, square.dilatedCenter_mem_dilatedInteriorRegion factor_positive⟩
  have triangle_in_square := openOrientedTranslatedRightTriangleRegion_subset_of_vertices_mem_closure
    (dilatedNegativeVertex square factor) square.frame width_positive depth_positive
    (square.convex_dilatedInteriorRegion factor)
    (square.isOpen_dilatedInteriorRegion factor_positive.ne') region_nonempty
    origin_mem horizontal_mem vertical_mem
  have triangle_below : orientedTranslatedRightTriangleRegion
      (dilatedNegativeVertex square factor) square.frame width depth ⊆
        {point | point 1 ≤ height} := by
    apply orientedTranslatedRightTriangleRegion_subset_of_vertices_mem _ _
      width_positive depth_positive
      (convex_halfSpace_le ((LinearMap.proj (R := ℝ) 1).isLinear) height)
    · change dilatedNegativeVertex square factor 1 ≤ height
      dsimp [dilatedNegativeVertex, PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
      dsimp [horizontalCapHeight] at cap_positive
      linarith
    · change dilatedNegativeVertex square factor 1 + (square.frame.rotation ![width, 0]) 1 ≤ height
      rw [Frame.rotation_apply_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero]
      dsimp [width, cap, horizontalCapHeight, dilatedNegativeVertex,
        PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
      rw [div_mul_cancel₀ _ sine_positive.ne']
      linarith
    · change dilatedNegativeVertex square factor 1 + (square.frame.rotation ![0, depth]) 1 ≤ height
      rw [Frame.rotation_apply_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, zero_add]
      dsimp [depth, cap, horizontalCapHeight, dilatedNegativeVertex,
        PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
      rw [div_mul_cancel₀ _ cosine_positive.ne']
      linarith
  rw [← volume_openOrientedTranslatedRightTriangleRegion
    (dilatedNegativeVertex square factor) square.frame width_positive depth_positive.le]
  exact measure_mono fun point point_mem =>
    ⟨triangle_in_square point_mem, triangle_below (interior_subset point_mem)⟩

noncomputable def horizontalUpperCapHeight
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  factor * square.center.y + factor * (square.frame.cosine + square.frame.sine) / 2 - height

lemma horizontalUpperCap_volume_lower_bound
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_positive : 0 < horizontalUpperCapHeight square factor height)
    (cap_le_cosine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.sine) :
    ENNReal.ofReal
      ((horizontalUpperCapHeight square factor height / square.frame.sine) *
        (horizontalUpperCapHeight square factor height / square.frame.cosine) / 2) ≤
      volume (square.dilatedInteriorRegion factor ∩ {point | height ≤ point 1}) := by
  let reflectedHeight := 2 * factor * square.center.y - height
  have cap_identity : horizontalCapHeight square factor reflectedHeight =
      horizontalUpperCapHeight square factor height := by
    dsimp [horizontalCapHeight, horizontalUpperCapHeight, reflectedHeight]
    ring
  have lower_bound := horizontalLowerCap_volume_lower_bound square factor_positive
    cosine_positive sine_positive (cap_identity.symm ▸ cap_positive)
    (cap_identity.symm ▸ cap_le_cosine) (cap_identity.symm ▸ cap_le_sine)
  rw [cap_identity] at lower_bound
  let upperCap := square.dilatedInteriorRegion factor ∩ {point | height ≤ point 1}
  have upper_measurable : MeasurableSet upperCap :=
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne').inter
      (measurableSet_le measurable_const (measurable_pi_apply 1))
  have reflected_cap :
      (fun point : Plane => (2 : ℝ) • (factor • square.center.toPlane) - point) ⁻¹' upperCap =
        square.dilatedInteriorRegion factor ∩ {point | point 1 ≤ reflectedHeight} := by
    ext point
    change ((2 : ℝ) • (factor • square.center.toPlane) - point ∈ square.dilatedInteriorRegion factor ∧
      height ≤ ((2 : ℝ) • (factor • square.center.toPlane) - point) 1) ↔ _
    rw [square.centralReflection_mem_dilatedInteriorRegion_iff factor_positive]
    simp only [mem_inter_iff, mem_ofPred_eq, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Point.toPlane]
    dsimp [reflectedHeight]
    constructor <;> rintro ⟨point_mem, bound⟩ <;> exact ⟨point_mem, by linarith⟩
  have volumes_equal : volume
      (square.dilatedInteriorRegion factor ∩ {point | point 1 ≤ reflectedHeight}) =
        volume upperCap := by
    rw [← reflected_cap]
    exact (volume.measurePreserving_sub_left ((2 : ℝ) • (factor • square.center.toPlane))).measure_preimage
      upper_measurable.nullMeasurableSet
  rwa [volumes_equal] at lower_bound

lemma horizontalUpperCap_section_lower_bound
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (cap_le_cosine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor height ≤ factor * square.frame.sine) :
    ENNReal.ofReal (horizontalUpperCapHeight square factor height /
      (square.frame.sine * square.frame.cosine)) ≤
      volume {coordinate : ℝ | ![coordinate, height] ∈ square.dilatedInteriorRegion factor} := by
  let reflectedHeight := 2 * factor * square.center.y - height
  have cap_identity : horizontalCapHeight square factor reflectedHeight =
      horizontalUpperCapHeight square factor height := by
    dsimp [horizontalCapHeight, horizontalUpperCapHeight, reflectedHeight]
    ring
  have chord := horizontalAdjacentChord_of_cap_bounds square factor_positive
    cosine_positive sine_positive (cap_identity.symm ▸ cap_le_cosine)
    (cap_identity.symm ▸ cap_le_sine)
  have lower_bound : ENNReal.ofReal (horizontalUpperCapHeight square factor height /
      (square.frame.sine * square.frame.cosine)) ≤
      volume {coordinate : ℝ | ![coordinate, reflectedHeight] ∈ square.dilatedInteriorRegion factor} := by
    rw [← cap_identity, ← horizontalAdjacentChord_length_eq_cap square cosine_positive sine_positive,
      ← Real.volume_Ioo]
    exact measure_mono chord
  let upperSection := {coordinate : ℝ | ![coordinate, height] ∈ square.dilatedInteriorRegion factor}
  have upper_measurable : MeasurableSet upperSection :=
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne').preimage (by fun_prop)
  have reflected_section : (fun coordinate : ℝ => 2 * factor * square.center.x - coordinate) ⁻¹' upperSection =
      {coordinate : ℝ | ![coordinate, reflectedHeight] ∈ square.dilatedInteriorRegion factor} := by
    ext coordinate
    have reflection_identity : ![2 * factor * square.center.x - coordinate, height] =
        (2 : ℝ) • (factor • square.center.toPlane) - ![coordinate, reflectedHeight] := by
      funext axis
      fin_cases axis <;> simp [reflectedHeight, Point.toPlane] <;> ring
    change (![2 * factor * square.center.x - coordinate, height] ∈
      square.dilatedInteriorRegion factor) ↔ _
    rw [reflection_identity, square.centralReflection_mem_dilatedInteriorRegion_iff factor_positive]
    rfl
  have volumes_equal : volume {coordinate : ℝ |
      ![coordinate, reflectedHeight] ∈ square.dilatedInteriorRegion factor} = volume upperSection := by
    rw [← reflected_section]
    exact (volume.measurePreserving_sub_left (2 * factor * square.center.x)).measure_preimage
      upper_measurable.nullMeasurableSet
  rwa [volumes_equal] at lower_bound

theorem upperCap_area_add_half_section_gt_half_of_fits
    (square : PlacedSquare) {factor side : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion side)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine) :
    (1 / 2 : ENNReal) <
      volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) +
        (1 / 2 : ENNReal) * volume {coordinate : ℝ |
          ![coordinate, 1] ∈ square.dilatedInteriorRegion factor} := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bottom_bound := square.dilatedCenterY_halfExtent_le factor_positive
    cosine_positive.le sine_positive.le inside_container
  have cosine_lt_one : square.frame.cosine < 1 := by
    nlinarith [square.frame.unit, sq_pos_of_pos sine_positive]
  have sine_lt_one : square.frame.sine < 1 := by
    nlinarith [square.frame.unit, sq_pos_of_pos cosine_positive]
  have sum_gt_one : 1 < square.frame.cosine + square.frame.sine := by
    nlinarith [square.frame.unit, mul_pos cosine_positive sine_positive]
  let cap := horizontalUpperCapHeight square factor 1
  have cap_lower : square.frame.cosine + square.frame.sine - 1 ≤ cap := by
    dsimp [cap, horizontalUpperCapHeight]
    nlinarith [mul_nonneg (sub_nonneg.mpr factor_gt_one.le)
      (add_nonneg cosine_positive.le sine_positive.le)]
  have cap_positive : 0 < cap := by linarith
  have cap_algebra : square.frame.sine * square.frame.cosine < cap ^ 2 + cap := by
    have product_positive := mul_pos (sub_pos.mpr cosine_lt_one) (sub_pos.mpr sine_lt_one)
    nlinarith [square.frame.unit, sq_nonneg (cap - (square.frame.cosine + square.frame.sine - 1))]
  have cap_score : (1 / 2 : ℝ) < (cap / square.frame.sine) *
      (cap / square.frame.cosine) / 2 + (cap / (square.frame.sine * square.frame.cosine)) / 2 := by
    field_simp
    nlinarith
  have area_bound := horizontalUpperCap_volume_lower_bound square factor_positive
    cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
  have section_bound := horizontalUpperCap_section_lower_bound square factor_positive
    cosine_positive sine_positive cap_le_cosine cap_le_sine
  have encoded : ENNReal.ofReal ((cap / square.frame.sine) * (cap / square.frame.cosine) / 2 +
      (cap / (square.frame.sine * square.frame.cosine)) / 2) =
      ENNReal.ofReal ((cap / square.frame.sine) * (cap / square.frame.cosine) / 2) +
        (1 / 2 : ENNReal) * ENNReal.ofReal (cap / (square.frame.sine * square.frame.cosine)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul, mul_comm]
  have strict_bound := (ENNReal.ofReal_lt_ofReal_iff (by positivity :
    0 < (cap / square.frame.sine) * (cap / square.frame.cosine) / 2 +
      (cap / (square.frame.sine * square.frame.cosine)) / 2)).2 cap_score
  rw [encoded] at strict_bound
  have half_constant : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [half_constant] at strict_bound
  exact strict_bound.trans_le (add_le_add area_bound
    (mul_le_mul le_rfl section_bound bot_le bot_le))

lemma cap_score_gt_half_add_fifth_height
    {cosine sine height : ℝ}
    (cosine_positive : 0 < cosine)
    (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (height_lower : cosine + sine - 1 ≤ height) :
    1 / 2 + height / 5 <
      (height / sine) * (height / cosine) / 2 + height / (sine * cosine) / 2 := by
  have product_positive : 0 < cosine * sine := mul_pos cosine_positive sine_positive
  have sum_gt_one : 1 < cosine + sine := by
    nlinarith
  have sum_lt_three_halves : cosine + sine < 3 / 2 := by
    nlinarith [sq_nonneg (cosine - sine)]
  have product_bound : cosine * sine ≤ 1 / 2 := by
    nlinarith [sq_nonneg (cosine - sine)]
  have base_positive : 0 < (cosine + sine - 1) ^ 2 * (3 / 2 - (cosine + sine)) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have base_identity :
      5 * (cosine + sine - 1) ^ 2 + (5 - 2 * cosine * sine) * (cosine + sine - 1) -
          5 * cosine * sine =
        (cosine + sine - 1) ^ 2 * (3 / 2 - (cosine + sine)) := by
    linear_combination (cosine + sine + 3 / 2) * unit
  have increase_nonnegative : 0 ≤ (height - (cosine + sine - 1)) *
      (5 * (height + (cosine + sine - 1)) + 5 - 2 * cosine * sine) :=
    mul_nonneg (by linarith) (by linarith)
  have polynomial_positive :
      0 < 5 * height ^ 2 + (5 - 2 * cosine * sine) * height - 5 * cosine * sine := by
    nlinarith [base_identity]
  field_simp
  nlinarith

end Nagamochi

end SquarePackingArchive
