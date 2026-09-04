import SquarePackingArchive.NagamochiInner

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

noncomputable def cornerExtension
    (size : ℕ) : NagamochiResource.CornerPoint → Measure Plane
  | .bottomLeft => horizontalSegmentMeasure 0 (9 / 10) 1
  | .bottomRight => horizontalSegmentMeasure ((size : ℝ) - 9 / 10) size 1
  | .topLeft => horizontalSegmentMeasure 0 (9 / 10) ((size : ℝ) - 1)
  | .topRight => horizontalSegmentMeasure ((size : ℝ) - 9 / 10) size ((size : ℝ) - 1)
  | .leftBottom => verticalSegmentMeasure 0 (9 / 10) 1
  | .leftTop => verticalSegmentMeasure ((size : ℝ) - 9 / 10) size 1
  | .rightBottom => verticalSegmentMeasure 0 (9 / 10) ((size : ℝ) - 1)
  | .rightTop => verticalSegmentMeasure ((size : ℝ) - 9 / 10) size ((size : ℝ) - 1)

lemma cornerExtension_univ (size : ℕ) (kind : NagamochiResource.CornerPoint) :
    cornerExtension size kind univ = 9 / 10 := by
  cases kind <;> simp only [cornerExtension, horizontalSegmentMeasure_univ,
    verticalSegmentMeasure_univ] <;> ring_nf <;> norm_num [ENNReal.ofReal_div_of_pos]

lemma cornerExtension_le (size : ℕ) (kind : NagamochiResource.CornerPoint)
    (region : Set Plane) : cornerExtension size kind region ≤ 9 / 10 := by
  rw [← cornerExtension_univ size kind]
  exact measure_mono (subset_univ region)

noncomputable def selectedCornerExtensions (size : ℕ) (region : Set Plane) : ENNReal := by
  classical
  exact (1 / 2 : ENNReal) * ∑ kind ∈ NagamochiResource.cornerPointKinds,
    if NagamochiResource.cornerPoint size kind ∈ region then
      cornerExtension size kind region else 0

lemma selectedCornerExtensions_le_cornerPoints
    {size : ℕ} {region : Set Plane} (measurable : MeasurableSet region) :
    selectedCornerExtensions size region ≤ NagamochiResource.cornerPoints size region := by
  classical
  simp only [selectedCornerExtensions, NagamochiResource.cornerPoints,
    Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro kind _
  rw [Measure.dirac_apply' _ measurable]
  by_cases contained : NagamochiResource.cornerPoint size kind ∈ region
  · simp [contained]
    have bound := mul_le_mul le_rfl (cornerExtension_le size kind region) bot_le bot_le
      (a := (1 / 2 : ENNReal))
    have weight : (1 / 2 : ENNReal) * (9 / 10) = 9 / 20 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_mul]
      norm_num
    rw [weight] at bound
    simpa using bound
  · simp [contained]

noncomputable def extendedBoundaryScore (size : ℕ) (region : Set Plane) : ENNReal :=
  NagamochiResource.boundaryLines size region + selectedCornerExtensions size region

noncomputable def extendedBoundaryLine (size : ℕ)
    (side : NagamochiResource.BoundarySide) (region : Set Plane) : ENNReal := by
  classical
  exact NagamochiResource.boundaryLine size side region +
    (if NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region then
      cornerExtension size side.firstCornerPoint region else 0) +
    (if NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region then
      cornerExtension size side.secondCornerPoint region else 0)

lemma sum_extendedBoundaryLine (size : ℕ) (region : Set Plane) :
    (1 / 2 : ENNReal) * ∑ side ∈ NagamochiResource.boundarySides,
        extendedBoundaryLine size side region = extendedBoundaryScore size region := by
  classical
  simp [extendedBoundaryLine, extendedBoundaryScore, selectedCornerExtensions,
    NagamochiResource.boundaryLines,
    NagamochiResource.boundarySides, NagamochiResource.cornerPointKinds,
    NagamochiResource.BoundarySide.firstCornerPoint,
    NagamochiResource.BoundarySide.secondCornerPoint]
  simp only [mul_add]
  ac_rfl

noncomputable def fullBoundaryLine
    (size : ℕ) : NagamochiResource.BoundarySide → Measure Plane
  | .bottom => horizontalSegmentMeasure 0 size 1
  | .top => horizontalSegmentMeasure 0 size ((size : ℝ) - 1)
  | .left => verticalSegmentMeasure 0 size 1
  | .right => verticalSegmentMeasure 0 size ((size : ℝ) - 1)

lemma fullBoundaryLine_apply
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (measurable : MeasurableSet region) :
    fullBoundaryLine size side region =
      volume (Icc (0 : ℝ) size ∩ (side.pointAt size) ⁻¹' region) := by
  cases side <;> simp [fullBoundaryLine, horizontalSegmentMeasure_apply measurable,
    verticalSegmentMeasure_apply measurable]
  all_goals rfl

lemma boundaryLine_apply_pointAt
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (measurable : MeasurableSet region) :
    NagamochiResource.boundaryLine size side region =
      volume (Icc (9 / 10 : ℝ) ((size : ℝ) - 9 / 10) ∩
        (side.pointAt size) ⁻¹' region) := by
  cases side <;> simp [NagamochiResource.boundaryLine,
    horizontalSegmentMeasure_apply measurable, verticalSegmentMeasure_apply measurable]
  all_goals rfl

lemma cornerExtension_first_apply
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (measurable : MeasurableSet region) :
    cornerExtension size side.firstCornerPoint region =
      volume (Icc (0 : ℝ) (9 / 10) ∩ (side.pointAt size) ⁻¹' region) := by
  cases side <;> simp [cornerExtension, NagamochiResource.BoundarySide.firstCornerPoint,
    horizontalSegmentMeasure_apply measurable, verticalSegmentMeasure_apply measurable]
  all_goals rfl

lemma cornerExtension_second_apply
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (measurable : MeasurableSet region) :
    cornerExtension size side.secondCornerPoint region =
      volume (Icc ((size : ℝ) - 9 / 10) size ∩ (side.pointAt size) ⁻¹' region) := by
  cases side <;> simp [cornerExtension, NagamochiResource.BoundarySide.secondCornerPoint,
    horizontalSegmentMeasure_apply measurable, verticalSegmentMeasure_apply measurable]
  all_goals rfl

lemma boundary_point_between
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (convex : Convex ℝ region) {left right coordinate : ℝ}
    (ordered : left < right)
    (left_mem : side.pointAt size left ∈ region)
    (right_mem : side.pointAt size right ∈ region)
    (between : coordinate ∈ Ioo left right) :
    side.pointAt size coordinate ∈ region := by
  cases side <;>
    first
    | exact horizontal_openSegment_subset_of_convex convex ordered left_mem right_mem
        coordinate between
    | exact vertical_openSegment_subset_of_convex convex ordered left_mem right_mem
        coordinate between

lemma fullBoundaryLine_le_extended_of_inner_anchor
    {size : ℕ} (side : NagamochiResource.BoundarySide) {region : Set Plane}
    (measurable : MeasurableSet region) (convex : Convex ℝ region)
    {anchor : ℝ} (anchor_lower : 1 ≤ anchor) (anchor_upper : anchor ≤ (size : ℝ) - 1)
    (anchor_mem : side.pointAt size anchor ∈ region) :
    fullBoundaryLine size side region ≤ extendedBoundaryLine size side region := by
  classical
  let coordinates := (side.pointAt size) ⁻¹' region
  let first := if NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region then
    Icc (0 : ℝ) (9 / 10) ∩ coordinates else ∅
  let second := if NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region then
    Icc ((size : ℝ) - 9 / 10) size ∩ coordinates else ∅
  have covered : Icc (0 : ℝ) size ∩ coordinates ⊆
      (Icc (9 / 10) ((size : ℝ) - 9 / 10) ∩ coordinates) ∪ first ∪ second := by
    intro coordinate coordinate_mem
    by_cases below : coordinate < 9 / 10
    · have corner_mem : NagamochiResource.cornerPoint size side.firstCornerPoint ∈ region := by
        rw [← NagamochiResource.BoundarySide.pointAt_firstCorner]
        exact boundary_point_between side convex (by linarith) coordinate_mem.2 anchor_mem
          ⟨below, by linarith⟩
      exact Or.inl (Or.inr (by
        simp only [first, corner_mem, if_pos]
        exact ⟨⟨coordinate_mem.1.1, below.le⟩, coordinate_mem.2⟩))
    by_cases above : (size : ℝ) - 9 / 10 < coordinate
    · have corner_mem : NagamochiResource.cornerPoint size side.secondCornerPoint ∈ region := by
        rw [← NagamochiResource.BoundarySide.pointAt_secondCorner]
        exact boundary_point_between side convex (by linarith) anchor_mem coordinate_mem.2
          ⟨by linarith, above⟩
      exact Or.inr (by
        simp only [second, corner_mem, if_pos]
        exact ⟨⟨above.le, coordinate_mem.1.2⟩, coordinate_mem.2⟩)
    exact Or.inl (Or.inl ⟨⟨le_of_not_gt below, le_of_not_gt above⟩, coordinate_mem.2⟩)
  have estimate := (measure_mono (μ := volume) covered).trans
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  rw [fullBoundaryLine_apply side measurable, extendedBoundaryLine,
    boundaryLine_apply_pointAt side measurable,
    cornerExtension_first_apply side measurable, cornerExtension_second_apply side measurable]
  simpa [first, second, coordinates, apply_ite volume, measure_empty] using estimate

lemma innerArea_add_extendedBoundaryScore_le_measure
    {size : ℕ} {region : Set Plane} (measurable : MeasurableSet region) :
    NagamochiResource.innerArea size region + extendedBoundaryScore size region ≤
      NagamochiResource.measure size region := by
  rw [extendedBoundaryScore, ← add_assoc]
  exact (add_le_add le_rfl (selectedCornerExtensions_le_cornerPoints measurable)).trans
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size region)

lemma score_gt_one_of_compensated_extended_inner_area
    {size : ℕ} {square : PlacedSquare} {factor : ℝ} {loss : ENNReal}
    (factor_gt_one : 1 < factor)
    (area_cover : ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        loss)
    (loss_compensated : loss ≤
      extendedBoundaryScore size (square.dilatedInteriorRegion factor)) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := by linarith
  have square_gt_one : (1 : ENNReal) < ENNReal.ofReal (factor ^ 2) := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith
  exact square_gt_one.trans_le (area_cover.trans
    ((add_le_add le_rfl loss_compensated).trans
      (innerArea_add_extendedBoundaryScore_le_measure
        (square.measurableSet_dilatedInteriorRegion factor_positive.ne'))))

lemma fullBoundaryLine_eq_canonical
    {size : ℕ} (side : InnerBoundarySide) (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) :
    fullBoundaryLine size side.toBoundarySide (square.dilatedInteriorRegion factor) =
      horizontalSegmentMeasure 0 size (side.inwardThreshold size)
        ((side.canonicalSquare square).dilatedInteriorRegion factor) := by
  rw [fullBoundaryLine_apply side.toBoundarySide
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne'),
    horizontalSegmentMeasure_apply
      ((side.canonicalSquare square).measurableSet_dilatedInteriorRegion factor_positive.ne')]
  congr 1
  ext coordinate
  apply and_congr_right
  intro _
  change side.toBoundarySide.pointAt size coordinate ∈ square.dilatedInteriorRegion factor ↔
    ![coordinate, side.inwardThreshold size] ∈
      (side.canonicalSquare square).dilatedInteriorRegion factor
  rw [← side.canonicalPoint_boundaryPoint size coordinate]
  exact (side.mem_canonicalSquare_iff square factor_positive _).symm

lemma boundaryPoint_coordinate_mem_container
    {size : ℕ} (side : NagamochiResource.BoundarySide) {coordinate : ℝ}
    (point_mem : side.pointAt size coordinate ∈ containerRegion size) :
    coordinate ∈ Icc (0 : ℝ) size := by
  have bounds := (mem_containerRegion_iff size _).1 point_mem
  cases side with
  | bottom => exact ⟨bounds.1, bounds.2.1⟩
  | top => exact ⟨bounds.1, bounds.2.1⟩
  | left => exact ⟨bounds.2.2.1, bounds.2.2.2⟩
  | right => exact ⟨bounds.2.2.1, bounds.2.2.2⟩

lemma fullBoundaryLine_cut_budget
    {size : ℕ} (square : PlacedSquare) {factor : ℝ} (side : InnerBoundarySide)
    (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_inside : side.inwardThreshold size ≤
      side.inwardNormal (factor • square.center.toPlane)) :
    volume (boundaryCutRegion side size (square.dilatedInteriorRegion factor)) ≤
        (1 / 2 : ENNReal) *
          fullBoundaryLine size side.toBoundarySide (square.dilatedInteriorRegion factor) ∨
      (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤
        (1 / 2 : ENNReal) *
          fullBoundaryLine size side.toBoundarySide (square.dilatedInteriorRegion factor) := by
  let canonical := side.canonicalSquare square
  have canonical_center : side.inwardThreshold size ≤ factor * canonical.center.y := by
    simpa only [canonical, side.canonicalSquare_center_vertical] using center_inside
  have clipped : ∀ coordinate,
      ![coordinate, side.inwardThreshold size] ∈ canonical.dilatedInteriorRegion factor →
        coordinate ∈ Icc (0 : ℝ) size := by
    intro coordinate point_mem
    rw [← side.canonicalPoint_boundaryPoint] at point_mem
    exact boundaryPoint_coordinate_mem_container side.toBoundarySide
      (inside_container ((side.mem_canonicalSquare_iff square factor_positive _).1 point_mem))
  rw [boundaryCutRegion_volume_eq_canonical side square factor_positive,
    fullBoundaryLine_eq_canonical side square factor_positive]
  rcases horizontal_cut_classification canonical factor_positive
      (side.canonicalSquare_cosine_nonnegative square)
      (side.canonicalSquare_sine_nonnegative square) canonical_center with (inside | adjacent) | long
  · left
    have empty_cut : canonical.dilatedInteriorRegion factor ∩
        {point | point 1 < side.inwardThreshold size} = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro point point_mem
      exact (not_lt_of_ge (inside point point_mem.1)) point_mem.2
    change volume (canonical.dilatedInteriorRegion factor ∩ _) ≤ _
    rw [empty_cut, measure_empty]
    exact bot_le
  · left
    obtain ⟨cosine_positive, sine_positive, cap_positive, cap_le_cosine, cap_le_sine⟩ := adjacent
    exact horizontalLowerCap_compensated canonical factor_positive factor_at_most
      cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
      (fun coordinate coordinate_mem => clipped coordinate
        (horizontalAdjacentChord_of_cap_bounds canonical factor_positive
          cosine_positive sine_positive cap_le_cosine cap_le_sine coordinate coordinate_mem))
  · right
    obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ := long
    have line_bound := (ENNReal.ofReal_le_ofReal length_bound).trans
      (horizontalSegmentMeasure_lower_bound
        (canonical.measurableSet_dilatedInteriorRegion factor_positive.ne')
        (fun coordinate coordinate_mem => clipped coordinate (chord_inside coordinate coordinate_mem))
        chord_inside)
    exact mul_le_mul le_rfl line_bound bot_le bot_le

lemma score_gt_one_of_center_inner
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_inside : factor • square.center.toPlane ∈
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let region := square.dilatedInteriorRegion factor
  let selected := NagamochiResource.boundarySides.filter fun side =>
    InnerBoundaryActive size region (boundarySideToInner side)
  let budget := fun side => (1 / 2 : ENNReal) * extendedBoundaryLine size side region
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  apply score_gt_one_of_center_inner_cut_budgets square selected budget factor_gt_one center_inside
  · intro point point_mem point_outside
    obtain ⟨side, active, violated⟩ := exists_active_boundary_of_outside
      (square.convex_dilatedInteriorRegion factor)
      (square.dilatedCenter_mem_dilatedInteriorRegion factor_positive)
      center_inside point_mem point_outside
    refine ⟨side.toBoundarySide, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨NagamochiResource.mem_boundarySides _, by simpa using active⟩
    · simpa using violated
  · have subset : selected ⊆ NagamochiResource.boundarySides := Finset.filter_subset _ _
    have budget_bound : ∑ side ∈ selected, budget side ≤ extendedBoundaryScore size region := by
      rw [← sum_extendedBoundaryLine, Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => bot_le)
    exact (add_le_add le_rfl budget_bound).trans
      (innerArea_add_extendedBoundaryScore_le_measure region_measurable)
  · intro side selected_side
    have active := (Finset.mem_filter.mp selected_side).2
    obtain ⟨anchor, anchor_bounds, anchor_mem⟩ := active.exists_coordinate
    have extension_bound := fullBoundaryLine_le_extended_of_inner_anchor side
      region_measurable (square.convex_dilatedInteriorRegion factor)
      anchor_bounds.1 anchor_bounds.2 (by simpa using anchor_mem)
    have budget_bound := mul_le_mul le_rfl extension_bound bot_le bot_le
      (a := (1 / 2 : ENNReal))
    have center_bound := (mem_innerRectangle_iff_inward_bounds size _).1 center_inside
      (boundarySideToInner side)
    rcases fullBoundaryLine_cut_budget square (boundarySideToInner side)
        factor_positive factor_at_most inside_container center_bound with compensated | long
    · simp only [boundarySideToInner_toBoundarySide] at compensated
      exact Or.inl (compensated.trans budget_bound)
    · simp only [boundarySideToInner_toBoundarySide] at long
      exact Or.inr (long.trans budget_bound)

end SquarePackingArchive.Nagamochi
