import SquarePackingArchive.NagamochiLemmas
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace SquarePackingArchive

open MeasureTheory Set

lemma PlacedSquare.dilatedCenter_mem_dilatedInteriorRegion
    (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) :
    factor • square.center.toPlane ∈ square.dilatedInteriorRegion factor := by
  rw [square.mem_dilatedInteriorRegion_iff factor_positive]
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simpa only [abs_zero] using half_pos factor_positive
  · simpa only [abs_zero] using half_pos factor_positive
  · simp [Plane.toPoint, Point.toPlane, PlacedSquare.dilatedPoint, Frame.place]

lemma PlacedSquare.centralReflection_mem_dilatedInteriorRegion
    (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) {point : Plane}
    (point_mem : point ∈ square.dilatedInteriorRegion factor) :
    (2 : ℝ) • (factor • square.center.toPlane) - point ∈
      square.dilatedInteriorRegion factor := by
  rw [square.mem_dilatedInteriorRegion_iff factor_positive] at point_mem ⊢
  obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ := point_mem
  refine ⟨-localX, -localY, ?_, ?_, ?_⟩
  · simpa only [abs_neg] using localX_bound
  · simpa only [abs_neg] using localY_bound
  · have horizontal_eq := congrArg Point.x point_eq
    have vertical_eq := congrArg Point.y point_eq
    simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at horizontal_eq vertical_eq
    rw [Point.mk.injEq]
    constructor
    · simp [Plane.toPoint, Point.toPlane, PlacedSquare.dilatedPoint, Frame.place]
      linarith
    · simp [Plane.toPoint, Point.toPlane, PlacedSquare.dilatedPoint, Frame.place]
      linarith

lemma PlacedSquare.centralReflection_mem_dilatedInteriorRegion_iff
    (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) (point : Plane) :
    (2 : ℝ) • (factor • square.center.toPlane) - point ∈
        square.dilatedInteriorRegion factor ↔
      point ∈ square.dilatedInteriorRegion factor := by
  constructor
  · intro reflected_mem
    simpa only [sub_sub_cancel] using
      square.centralReflection_mem_dilatedInteriorRegion
        factor_positive reflected_mem
  · exact square.centralReflection_mem_dilatedInteriorRegion factor_positive

lemma PlacedSquare.half_volume_le_volume_innerHalfSpace
    (square : PlacedSquare) {factor threshold : ℝ}
    (normal : Plane →L[ℝ] ℝ)
    (factor_positive : 0 < factor)
    (center_inside : threshold ≤ normal (factor • square.center.toPlane)) :
    (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
      volume (square.dilatedInteriorRegion factor ∩
        {point | threshold ≤ normal point}) := by
  let center := factor • square.center.toPlane
  let region := square.dilatedInteriorRegion factor
  let upperHalf := region ∩ {point | normal center ≤ normal point}
  let lowerHalf := region ∩ {point | normal point ≤ normal center}
  have upper_measurable : MeasurableSet upperHalf :=
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne').inter
      (measurableSet_le measurable_const normal.continuous.measurable)
  have reflected_half :
      (fun point : Plane => (2 : ℝ) • center - point) ⁻¹' upperHalf = lowerHalf := by
    ext point
    change
      ((2 : ℝ) • center - point ∈ region ∧
        normal center ≤ normal ((2 : ℝ) • center - point)) ↔
      (point ∈ region ∧ normal point ≤ normal center)
    rw [square.centralReflection_mem_dilatedInteriorRegion_iff factor_positive]
    simp only [map_sub, map_smul, smul_eq_mul]
    constructor <;> rintro ⟨point_mem, normal_bound⟩ <;>
      exact ⟨point_mem, by linarith⟩
  have half_volumes_equal : volume lowerHalf = volume upperHalf := by
    rw [← reflected_half]
    exact (volume.measurePreserving_sub_left ((2 : ℝ) • center)).measure_preimage
      upper_measurable.nullMeasurableSet
  have covered : region ⊆ lowerHalf ∪ upperHalf := by
    intro point point_mem
    rcases le_total (normal point) (normal center) with below | above
    · exact Or.inl ⟨point_mem, below⟩
    · exact Or.inr ⟨point_mem, above⟩
  have total_le_twice_half : volume region ≤ volume upperHalf * 2 := by
    calc
      volume region ≤ volume (lowerHalf ∪ upperHalf) := measure_mono covered
      _ ≤ volume lowerHalf + volume upperHalf := measure_union_le _ _
      _ = volume upperHalf * 2 := by rw [half_volumes_equal]; ring
  have half_bound : volume region / 2 ≤ volume upperHalf :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).2 total_le_twice_half
  have upper_subset :
      upperHalf ⊆ region ∩ {point | threshold ≤ normal point} := by
    intro point point_mem
    exact ⟨point_mem.1, center_inside.trans point_mem.2⟩
  calc
    (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) = volume region / 2 := by
      rw [show volume region = ENNReal.ofReal (factor ^ 2) from
        square.volume_dilatedInteriorRegion factor_positive.le]
      simp only [div_eq_mul_inv, one_mul, mul_comm]
    _ ≤ volume upperHalf := half_bound
    _ ≤ _ := measure_mono upper_subset

namespace Nagamochi

noncomputable def InnerBoundarySide.inwardNormal :
    InnerBoundarySide → Plane →L[ℝ] ℝ
  | .bottom => ContinuousLinearMap.proj 1
  | .top => -ContinuousLinearMap.proj 1
  | .left => ContinuousLinearMap.proj 0
  | .right => -ContinuousLinearMap.proj 0

def InnerBoundarySide.inwardThreshold
    (side : InnerBoundarySide) (size : ℕ) : ℝ :=
  match side with
  | .bottom | .left => 1
  | .top | .right => 1 - size

lemma mem_innerRectangle_iff_inward_bounds
    (size : ℕ) (point : Plane) :
    point ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) ↔
      ∀ side : InnerBoundarySide,
        side.inwardThreshold size ≤ side.inwardNormal point := by
  constructor
  · intro point_mem side
    cases side <;>
      simp only [InnerBoundarySide.inwardThreshold,
        InnerBoundarySide.inwardNormal, ContinuousLinearMap.proj_apply,
        neg_apply] <;>
      have lower_x := point_mem.1 (0 : Fin 2) <;>
      have lower_y := point_mem.1 (1 : Fin 2) <;>
      have upper_x := point_mem.2 (0 : Fin 2) <;>
      have upper_y := point_mem.2 (1 : Fin 2) <;> linarith
  · intro bounds
    have bottom := bounds .bottom
    have top := bounds .top
    have left := bounds .left
    have right := bounds .right
    simp only [InnerBoundarySide.inwardThreshold,
      InnerBoundarySide.inwardNormal, ContinuousLinearMap.proj_apply,
      neg_apply] at bottom top left right
    constructor <;> intro coordinate <;> fin_cases coordinate <;> dsimp <;> linarith

lemma half_innerArea_of_single_inner_boundary_crossing
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (center_inside :
      side.inwardThreshold size ≤
        side.inwardNormal (factor • square.center.toPlane))
    (other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ side →
          other.inwardThreshold size ≤ other.inwardNormal point) :
    (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size
        (square.dilatedInteriorRegion factor) := by
  have half_bound := square.half_volume_le_volume_innerHalfSpace
    side.inwardNormal factor_positive center_inside
  have half_subset :
      square.dilatedInteriorRegion factor ∩
          {point | side.inwardThreshold size ≤ side.inwardNormal point} ⊆
        square.dilatedInteriorRegion factor ∩
          Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
    intro point point_mem
    refine ⟨point_mem.1, (mem_innerRectangle_iff_inward_bounds size point).2 ?_⟩
    intro other
    by_cases same_side : other = side
    · subst other
      exact point_mem.2
    · exact other_sides_inside point point_mem.1 other same_side
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact half_bound.trans (measure_mono half_subset)

lemma score_gt_one_of_single_inner_boundary_crossing
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_gt_one : 1 < factor)
    (center_inside :
      side.inwardThreshold size ≤
        side.inwardNormal (factor • square.center.toPlane))
    (other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ side →
          other.inwardThreshold size ≤ other.inwardNormal point)
    (chord : NagamochiResource.HasBoundaryChord size side.toBoundarySide
      (square.dilatedInteriorRegion factor) factor) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  exact score_gt_one_of_half_area_and_boundary_chord
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne') factor_gt_one
    (half_innerArea_of_single_inner_boundary_crossing square side
      factor_positive center_inside other_sides_inside) chord

lemma inward_bounds_of_center_inside_and_no_crossing
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (center_inside :
      side.inwardThreshold size ≤
        side.inwardNormal (factor • square.center.toPlane))
    (no_crossing :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        side.inwardNormal point ≠ side.inwardThreshold size) :
    ∀ point ∈ square.dilatedInteriorRegion factor,
      side.inwardThreshold size ≤ side.inwardNormal point := by
  intro point point_mem
  by_contra not_inside
  have below := lt_of_not_ge not_inside
  obtain ⟨intersection, intersection_mem, intersection_on_line⟩ :=
    (square.convex_dilatedInteriorRegion factor).isPreconnected.intermediate_value
      point_mem (square.dilatedCenter_mem_dilatedInteriorRegion factor_positive)
      side.inwardNormal.continuous.continuousOn ⟨below.le, center_inside⟩
  exact no_crossing intersection intersection_mem intersection_on_line

lemma score_gt_one_of_case3_single_crossed_line
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_inside :
      factor • square.center.toPlane ∈
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (only_crossed_line :
      ∀ other : InnerBoundarySide, other ≠ side →
        ∀ point ∈ square.dilatedInteriorRegion factor,
          other.inwardNormal point ≠ other.inwardThreshold size)
    (opposite_chord : HasOppositeBoundaryChord size square factor side.toBoundarySide) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_bounds :=
    (mem_innerRectangle_iff_inward_bounds size _).1 center_inside
  apply score_gt_one_of_single_inner_boundary_crossing square side
    factor_gt_one (center_bounds side)
  · intro point point_mem other different_side
    exact inward_bounds_of_center_inside_and_no_crossing square other
      factor_positive (center_bounds other) (only_crossed_line other different_side)
        point point_mem
  · exact boundaryChord_of_opposite square factor_positive
      cosine_positive sine_positive side.toBoundarySide opposite_chord

lemma exists_horizontal_chord_of_center_offset_le
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (offset_bound :
      |height - factor * square.center.y| ≤
        factor * |square.frame.cosine - square.frame.sine| / 2) :
    ∃ intervalStart intervalEnd : ℝ,
      factor ≤ intervalEnd - intervalStart ∧
        ∀ coordinate ∈ Ioo intervalStart intervalEnd,
          ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  have scaled_unit :
      (height - factor * square.center.y) * square.frame.cosine ^ 2 +
          (height - factor * square.center.y) * square.frame.sine ^ 2 =
        height - factor * square.center.y := by
    linear_combination (height - factor * square.center.y) * square.frame.unit
  by_cases sine_le_cosine : square.frame.sine ≤ square.frame.cosine
  · rw [abs_of_nonneg (sub_nonneg.mpr sine_le_cosine), abs_le] at offset_bound
    have lower_order :
        square.horizontalAdjacentOtherLower factor height ≤
          square.horizontalAdjacentChordStart factor height := by
      dsimp [PlacedSquare.horizontalAdjacentOtherLower,
        PlacedSquare.horizontalAdjacentChordStart]
      rw [add_le_add_iff_left, div_le_div_iff₀ sine_positive cosine_positive]
      nlinarith [offset_bound.2]
    have upper_order :
        square.horizontalAdjacentOtherUpper factor height ≤
          square.horizontalAdjacentChordEnd factor height := by
      dsimp [PlacedSquare.horizontalAdjacentOtherUpper,
        PlacedSquare.horizontalAdjacentChordEnd]
      rw [add_le_add_iff_left, div_le_div_iff₀ cosine_positive sine_positive]
      nlinarith [offset_bound.1]
    exact ⟨square.horizontalAdjacentChordStart factor height,
      square.horizontalAdjacentOtherUpper factor height,
      square.horizontalCosineChord_length_at_least_factor
        factor_positive.le cosine_positive,
      square.horizontalCosineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive lower_order upper_order⟩
  · have cosine_le_sine := le_of_not_ge sine_le_cosine
    rw [abs_of_nonpos (sub_nonpos.mpr cosine_le_sine), abs_le] at offset_bound
    have lower_order :
        square.horizontalAdjacentChordStart factor height ≤
          square.horizontalAdjacentOtherLower factor height := by
      dsimp [PlacedSquare.horizontalAdjacentOtherLower,
        PlacedSquare.horizontalAdjacentChordStart]
      rw [add_le_add_iff_left, div_le_div_iff₀ cosine_positive sine_positive]
      nlinarith [offset_bound.1]
    have upper_order :
        square.horizontalAdjacentChordEnd factor height ≤
          square.horizontalAdjacentOtherUpper factor height := by
      dsimp [PlacedSquare.horizontalAdjacentOtherUpper,
        PlacedSquare.horizontalAdjacentChordEnd]
      rw [add_le_add_iff_left, div_le_div_iff₀ sine_positive cosine_positive]
      nlinarith [offset_bound.2]
    exact ⟨square.horizontalAdjacentOtherLower factor height,
      square.horizontalAdjacentChordEnd factor height,
      square.horizontalSineChord_length_at_least_factor
        factor_positive.le sine_positive,
      square.horizontalSineChord_inside_dilatedInteriorRegion
        factor_positive cosine_positive sine_positive lower_order upper_order⟩

lemma exists_horizontal_chord_of_axis_aligned
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0)
    (line_intersects :
      ∃ coordinate, ![coordinate, height] ∈ square.dilatedInteriorRegion factor) :
    ∃ intervalStart intervalEnd : ℝ,
      factor ≤ intervalEnd - intervalStart ∧
        ∀ coordinate ∈ Ioo intervalStart intervalEnd,
          ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  have axis_values :
      (square.frame.cosine = 0 ∧ square.frame.sine = 1) ∨
        (square.frame.cosine = 1 ∧ square.frame.sine = 0) := by
    rcases axis_aligned with cosine_zero | sine_zero
    · exact Or.inl ⟨cosine_zero, by nlinarith [square.frame.unit]⟩
    · exact Or.inr ⟨by nlinarith [square.frame.unit], sine_zero⟩
  obtain ⟨intersection, intersection_mem⟩ := line_intersects
  rw [square.mem_dilatedInteriorRegion_iff factor_positive] at intersection_mem
  obtain ⟨localX, localY, localX_bound, localY_bound, intersection_eq⟩ := intersection_mem
  have vertical_eq := congrArg Point.y intersection_eq
  have vertical_offset_bound : |height - factor * square.center.y| < factor / 2 := by
    rcases axis_values with ⟨cosine_zero, sine_one⟩ | ⟨cosine_one, sine_zero⟩
    · simp [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place,
        cosine_zero, sine_one] at vertical_eq
      simpa [vertical_eq] using localX_bound
    · simp [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place,
        cosine_one, sine_zero] at vertical_eq
      simpa [vertical_eq] using localY_bound
  refine ⟨factor * square.center.x - factor / 2,
    factor * square.center.x + factor / 2, by linarith, ?_⟩
  intro coordinate coordinate_mem
  have horizontal_offset_bound : |coordinate - factor * square.center.x| < factor / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [coordinate_mem.1], by linarith [coordinate_mem.2]⟩
  rcases axis_values with ⟨cosine_zero, sine_one⟩ | ⟨cosine_one, sine_zero⟩
  · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
    · simpa [PlacedSquare.dilatedLocalX, Plane.toPoint, cosine_zero, sine_one]
        using vertical_offset_bound
    · simpa [PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_zero, sine_one,
        abs_sub_comm] using horizontal_offset_bound
  · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
    · simpa [PlacedSquare.dilatedLocalX, Plane.toPoint, cosine_one, sine_zero]
        using horizontal_offset_bound
    · simpa [PlacedSquare.dilatedLocalY, Plane.toPoint, cosine_one, sine_zero]
        using vertical_offset_bound

lemma firstQuadrant_frame_difference (square : PlacedSquare) :
    |square.firstQuadrant.frame.cosine - square.firstQuadrant.frame.sine| =
      abs (|square.frame.cosine| - |square.frame.sine|) := by
  simp only [PlacedSquare.firstQuadrant]
  split_ifs with cosine_nonnegative sine_nonnegative sine_nonnegative
  · rw [abs_of_nonneg cosine_nonnegative, abs_of_nonneg sine_nonnegative]
  · simp only [PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    rw [abs_of_nonneg cosine_nonnegative, abs_of_neg (lt_of_not_ge sine_nonnegative)]
    rw [show -square.frame.sine - square.frame.cosine =
      -(square.frame.cosine - -square.frame.sine) by ring, abs_neg]
  · simp only [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf,
      PlacedSquare.rotateQuarter, Frame.rotateQuarter, neg_neg]
    rw [abs_of_neg (lt_of_not_ge cosine_nonnegative), abs_of_nonneg sine_nonnegative]
    exact abs_sub_comm _ _
  · simp only [PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      Frame.rotateQuarter]
    rw [abs_of_neg (lt_of_not_ge cosine_nonnegative),
      abs_of_neg (lt_of_not_ge sine_nonnegative)]

lemma exists_horizontal_chord_of_center_offset_le_any_frame
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (line_intersects :
      ∃ coordinate, ![coordinate, height] ∈ square.dilatedInteriorRegion factor)
    (offset_bound :
      |height - factor * square.center.y| ≤
        factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2) :
    ∃ intervalStart intervalEnd : ℝ,
      factor ≤ intervalEnd - intervalStart ∧
        ∀ coordinate ∈ Ioo intervalStart intervalEnd,
          ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_intersection :
      ∃ coordinate,
        ![coordinate, height] ∈ square.firstQuadrant.dilatedInteriorRegion factor := by
    simpa only [region_eq] using line_intersects
  have normalized_offset :
      |height - factor * square.firstQuadrant.center.y| ≤
        factor * |square.firstQuadrant.frame.cosine - square.firstQuadrant.frame.sine| / 2 := by
    simpa only [square.firstQuadrant_center, firstQuadrant_frame_difference]
      using offset_bound
  have normalized_chord :
      ∃ intervalStart intervalEnd : ℝ,
        factor ≤ intervalEnd - intervalStart ∧
          ∀ coordinate ∈ Ioo intervalStart intervalEnd,
            ![coordinate, height] ∈ square.firstQuadrant.dilatedInteriorRegion factor := by
    by_cases axis_aligned :
        square.firstQuadrant.frame.cosine = 0 ∨ square.firstQuadrant.frame.sine = 0
    · exact exists_horizontal_chord_of_axis_aligned square.firstQuadrant
        factor_positive square.firstQuadrant_cosine_nonnegative
        square.firstQuadrant_sine_nonnegative axis_aligned normalized_intersection
    · push Not at axis_aligned
      exact exists_horizontal_chord_of_center_offset_le square.firstQuadrant
        factor_positive
        (lt_of_le_of_ne square.firstQuadrant_cosine_nonnegative axis_aligned.1.symm)
        (lt_of_le_of_ne square.firstQuadrant_sine_nonnegative axis_aligned.2.symm)
        normalized_offset
  simpa only [region_eq] using normalized_chord

lemma exists_boundary_line_chord_of_center_offset_le
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (line_intersects :
      ∃ coordinate, side.toBoundarySide.pointAt size coordinate ∈
        square.dilatedInteriorRegion factor)
    (offset_bound :
      |side.inwardThreshold size -
          side.inwardNormal (factor • square.center.toPlane)| ≤
        factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2) :
    ∃ intervalStart intervalEnd : ℝ,
      factor ≤ intervalEnd - intervalStart ∧
        ∀ coordinate ∈ Ioo intervalStart intervalEnd,
          side.toBoundarySide.pointAt size coordinate ∈
            square.dilatedInteriorRegion factor := by
  have vertical_chord :
      ∀ width : ℝ,
        (∃ coordinate, ![width, coordinate] ∈ square.dilatedInteriorRegion factor) →
        |width - factor * square.center.x| ≤
            factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2 →
          ∃ intervalStart intervalEnd : ℝ,
            factor ≤ intervalEnd - intervalStart ∧
              ∀ coordinate ∈ Ioo intervalStart intervalEnd,
                ![width, coordinate] ∈ square.dilatedInteriorRegion factor := by
    intro width vertical_intersection vertical_offset_bound
    have swapped_intersection :
        ∃ coordinate, ![coordinate, width] ∈ square.swap.dilatedInteriorRegion factor := by
      obtain ⟨coordinate, point_mem⟩ := vertical_intersection
      exact ⟨coordinate, (square.mem_swap_dilatedInteriorRegion_iff
        factor_positive ![width, coordinate]).2 point_mem⟩
    obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
      exists_horizontal_chord_of_center_offset_le_any_frame square.swap
        factor_positive swapped_intersection
        (by simpa [PlacedSquare.swap, Frame.swap, Point.swap, abs_sub_comm]
          using vertical_offset_bound)
    refine ⟨intervalStart, intervalEnd, length_bound, ?_⟩
    intro coordinate coordinate_mem
    exact (square.mem_swap_dilatedInteriorRegion_iff factor_positive
      ![width, coordinate]).1 (chord_inside coordinate coordinate_mem)
  cases side with
  | bottom =>
      exact exists_horizontal_chord_of_center_offset_le_any_frame square factor_positive
        line_intersects offset_bound
  | left =>
      exact vertical_chord 1 line_intersects offset_bound
  | top =>
      have height_bound :
          |(size : ℝ) - 1 - factor * square.center.y| ≤
            factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2 := by
        change |1 - (size : ℝ) - -(factor * square.center.y)| ≤ _ at offset_bound
        rwa [show 1 - (size : ℝ) - -(factor * square.center.y) =
          -((size : ℝ) - 1 - factor * square.center.y) by ring, abs_neg] at offset_bound
      exact exists_horizontal_chord_of_center_offset_le_any_frame square factor_positive
        line_intersects height_bound
  | right =>
      have width_bound :
          |(size : ℝ) - 1 - factor * square.center.x| ≤
            factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2 := by
        change |1 - (size : ℝ) - -(factor * square.center.x)| ≤ _ at offset_bound
        rwa [show 1 - (size : ℝ) - -(factor * square.center.x) =
          -((size : ℝ) - 1 - factor * square.center.x) by ring, abs_neg] at offset_bound
      exact vertical_chord ((size : ℝ) - 1) line_intersects width_bound

lemma boundaryChord_of_line_chord_and_other_sides_inside
    {size : ℕ} {region : Set Plane} {minimumLength intervalStart intervalEnd : ℝ}
    (side : InnerBoundarySide)
    (length_bound : minimumLength ≤ intervalEnd - intervalStart)
    (chord_inside :
      ∀ coordinate ∈ Ioo intervalStart intervalEnd,
        side.toBoundarySide.pointAt size coordinate ∈ region)
    (other_sides_inside :
      ∀ point ∈ region,
        ∀ other : InnerBoundarySide, other ≠ side →
          other.inwardThreshold size ≤ other.inwardNormal point) :
    NagamochiResource.HasBoundaryChord size side.toBoundarySide region
      minimumLength := by
  have inside_segment :
      Ioo intervalStart intervalEnd ⊆ Icc (9 / 10) ((size : ℝ) - 9 / 10) := by
    intro coordinate coordinate_mem
    have point_inside := chord_inside coordinate coordinate_mem
    have inner_point :
        side.toBoundarySide.pointAt size coordinate ∈
          Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
      apply (mem_innerRectangle_iff_inward_bounds size _).2
      intro other
      by_cases same_side : other = side
      · subst other
        cases side <;>
          simp [InnerBoundarySide.inwardThreshold, InnerBoundarySide.inwardNormal,
            InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt]
      · exact other_sides_inside _ point_inside other same_side
    have lower_x := inner_point.1 (0 : Fin 2)
    have lower_y := inner_point.1 (1 : Fin 2)
    have upper_x := inner_point.2 (0 : Fin 2)
    have upper_y := inner_point.2 (1 : Fin 2)
    cases side <;>
      simp only [InnerBoundarySide.toBoundarySide,
        NagamochiResource.BoundarySide.pointAt, Matrix.cons_val_zero,
        Matrix.cons_val_one] at lower_x lower_y upper_x upper_y
      <;> constructor <;> linarith
  cases side <;>
    exact ⟨intervalStart, intervalEnd, length_bound, inside_segment, chord_inside⟩

lemma score_gt_one_of_case3_single_crossed_line_offset
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_gt_one : 1 < factor)
    (line_intersects :
      ∃ coordinate, side.toBoundarySide.pointAt size coordinate ∈
        square.dilatedInteriorRegion factor)
    (center_inside :
      factor • square.center.toPlane ∈
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (only_crossed_line :
      ∀ other : InnerBoundarySide, other ≠ side →
        ∀ point ∈ square.dilatedInteriorRegion factor,
          other.inwardNormal point ≠ other.inwardThreshold size)
    (offset_bound :
      |side.inwardThreshold size -
          side.inwardNormal (factor • square.center.toPlane)| ≤
        factor * abs (|square.frame.cosine| - |square.frame.sine|) / 2) :
    1 < NagamochiResource.measure size
      (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_bounds :=
    (mem_innerRectangle_iff_inward_bounds size _).1 center_inside
  have other_sides_inside :
      ∀ point ∈ square.dilatedInteriorRegion factor,
        ∀ other : InnerBoundarySide, other ≠ side →
          other.inwardThreshold size ≤ other.inwardNormal point := by
    intro point point_mem other different_side
    exact inward_bounds_of_center_inside_and_no_crossing square other
      factor_positive (center_bounds other) (only_crossed_line other different_side)
        point point_mem
  obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ :=
    exists_boundary_line_chord_of_center_offset_le square side factor_positive
      line_intersects offset_bound
  exact score_gt_one_of_single_inner_boundary_crossing square side factor_gt_one
    (center_bounds side) other_sides_inside
    (boundaryChord_of_line_chord_and_other_sides_inside side
      length_bound chord_inside other_sides_inside)

end Nagamochi

end SquarePackingArchive
