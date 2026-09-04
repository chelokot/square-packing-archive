import SquarePackingArchive.NagamochiClipping
import SquarePackingArchive.NagamochiCutSymmetry
import SquarePackingArchive.Records.NearSquare

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma inverse_bounds_of_dilatedInteriorRegion_mem
    (square : PlacedSquare) {factor : ℝ} {point : Plane}
    (factor_positive : 0 < factor)
    (point_mem : point ∈ square.dilatedInteriorRegion factor) :
    |square.dilatedLocalX factor point.toPoint| < factor / 2 ∧
      |square.dilatedLocalY factor point.toPoint| < factor / 2 := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem
  have horizontal_eq : square.dilatedLocalX factor point.toPoint = localX := by
    rw [point_eq]
    dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedPoint, Frame.place]
    linear_combination localX * square.frame.unit
  have vertical_eq : square.dilatedLocalY factor point.toPoint = localY := by
    rw [point_eq]
    dsimp [PlacedSquare.dilatedLocalY, PlacedSquare.dilatedPoint, Frame.place]
    linear_combination localY * square.frame.unit
  rw [horizontal_eq, vertical_eq]
  exact ⟨horizontal_bound, vertical_bound⟩

lemma vertical_offset_component_lt_half
    {component other factor center height : ℝ}
    (component_nonnegative : 0 ≤ component) (other_nonnegative : 0 ≤ other)
    (factor_positive : 0 < factor)
    (center_lower : factor * (component + other) / 2 ≤ center)
    (height_lt_factor : height < factor) :
    (height - center) * component < factor / 2 := by
  by_cases component_zero : component = 0
  · simp [component_zero, factor_positive]
  have component_positive : 0 < component :=
    lt_of_le_of_ne component_nonnegative (Ne.symm component_zero)
  have scaled_center := mul_le_mul_of_nonneg_right center_lower component_nonnegative
  have remainder_nonnegative :
      0 ≤ factor * ((1 - component) ^ 2 + component * other) :=
    mul_nonneg factor_positive.le
      (add_nonneg (sq_nonneg _) (mul_nonneg component_nonnegative other_nonnegative))
  have at_factor : (factor - center) * component ≤ factor / 2 := by
    nlinarith
  exact (mul_lt_mul_of_pos_right (by linarith : height - center < factor - center)
    component_positive).trans_le at_factor

lemma bottom_centerline_anchor
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (center_below : factor * square.center.y ≤ 1) :
    ![factor * square.center.x, 1] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_bound := (square.center_bounds fits).2.2.1
  unfold frameExtent at center_bound
  have scaled_center :
      factor * (|square.frame.cosine| + |square.frame.sine|) / 2 ≤
        factor * square.center.y := by
    nlinarith [mul_le_mul_of_nonneg_left center_bound factor_positive.le]
  have cosine_bound := vertical_offset_component_lt_half
    (abs_nonneg square.frame.cosine) (abs_nonneg square.frame.sine)
    factor_positive scaled_center factor_gt_one
  have sine_bound := vertical_offset_component_lt_half
    (abs_nonneg square.frame.sine) (abs_nonneg square.frame.cosine)
    factor_positive (by simpa [add_comm] using scaled_center) factor_gt_one
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · simpa [PlacedSquare.dilatedLocalX, Plane.toPoint, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr center_below)] using sine_bound
  · simpa [PlacedSquare.dilatedLocalY, Plane.toPoint, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr center_below)] using cosine_bound

lemma bottom_active_of_edge_strip
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (size_at_least_two : 2 ≤ size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1) :
    InnerBoundaryActive size (square.dilatedInteriorRegion factor) .bottom := by
  refine ⟨![factor * square.center.x, 1], ⟨
    bottom_centerline_anchor square fits factor_gt_one center_below, ?_⟩, ?_⟩
  · have size_real : (2 : ℝ) ≤ size := by exact_mod_cast size_at_least_two
    constructor
    · intro coordinate
      fin_cases coordinate
      · exact center_horizontal.1
      · norm_num
    · intro coordinate
      fin_cases coordinate
      · exact center_horizontal.2
      · dsimp
        linarith
  · simp [InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold]

lemma bottom_line_clipped_of_edge_strip_and_missing_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (size_at_least_two : 2 ≤ size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (missing_corners : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor) :
    ∀ coordinate, ![coordinate, 1] ∈ square.dilatedInteriorRegion factor →
      coordinate ∈ Icc (9 / 10 : ℝ) ((size : ℝ) - 9 / 10) := by
  have clipped := boundaryLine_clipped_of_active_and_missing_corners
    (square.convex_dilatedInteriorRegion factor)
    (bottom_active_of_edge_strip square fits factor_gt_one size_at_least_two
      center_horizontal center_below) missing_corners
  simpa [InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt] using clipped

noncomputable def activeNonbottomSides (size : ℕ) (region : Set Plane) :
    Finset NagamochiResource.BoundarySide := by
  classical
  exact NagamochiResource.boundarySides.filter fun side =>
    side ≠ .bottom ∧ InnerBoundaryActive size region (boundarySideToInner side)

lemma upperCap_le_innerArea_add_nonbottomCuts
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (size_at_least_two : 2 ≤ size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1) :
    volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ∑ boundary ∈ activeNonbottomSides size (square.dilatedInteriorRegion factor),
          volume (boundaryCutRegion (boundarySideToInner boundary) size
            (square.dilatedInteriorRegion factor)) := by
  classical
  let region := square.dilatedInteriorRegion factor
  have anchor := bottom_active_of_edge_strip square fits factor_gt_one
    size_at_least_two center_horizontal center_below
  obtain ⟨point, ⟨point_mem, point_inner⟩, _⟩ := anchor
  have covered : region ∩ {point | 1 ≤ point 1} ⊆
      (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        ⋃ boundary ∈ activeNonbottomSides size region,
          boundaryCutRegion (boundarySideToInner boundary) size region := by
    rintro candidate ⟨candidate_mem, candidate_above⟩
    by_cases candidate_inner : candidate ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)
    · exact Or.inl ⟨candidate_mem, candidate_inner⟩
    obtain ⟨boundary, active, violated⟩ := exists_active_boundary_of_outside
      (square.convex_dilatedInteriorRegion factor) point_mem point_inner
      candidate_mem candidate_inner
    have not_bottom : boundary.toBoundarySide ≠ .bottom := by
      intro equality
      cases boundary <;> simp_all [InnerBoundarySide.toBoundarySide,
        InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold]
      linarith
    have selected : boundary.toBoundarySide ∈ activeNonbottomSides size region := by
      apply Finset.mem_filter.mpr
      exact ⟨NagamochiResource.mem_boundarySides _, not_bottom, by simpa using active⟩
    exact Or.inr (mem_iUnion.2 ⟨boundary.toBoundarySide, mem_iUnion.2 ⟨selected,
      candidate_mem, by simpa using violated⟩⟩)
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne')]
  exact (measure_mono covered).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _)))

end SquarePackingArchive.Nagamochi
