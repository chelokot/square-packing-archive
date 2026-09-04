import SquarePackingArchive.NagamochiCutSymmetry
import SquarePackingArchive.NagamochiCutBudget
import SquarePackingArchive.NagamochiClipping

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma InnerBoundarySide.canonicalSquare_center_vertical
    (side : InnerBoundarySide) (square : PlacedSquare) (factor : ℝ) :
    factor * (side.canonicalSquare square).center.y =
      side.inwardNormal (factor • square.center.toPlane) := by
  cases side <;>
    simp [InnerBoundarySide.canonicalSquare, PlacedSquare.firstQuadrant_center,
      InnerBoundarySide.inwardNormal, PlacedSquare.reflectY, PlacedSquare.swap,
      Point.reflectY, Point.swap, Point.toPlane]

lemma InnerBoundarySide.canonicalSquare_cosine_nonnegative
    (side : InnerBoundarySide) (square : PlacedSquare) :
    0 ≤ (side.canonicalSquare square).frame.cosine := by
  cases side <;> exact PlacedSquare.firstQuadrant_cosine_nonnegative _

lemma InnerBoundarySide.canonicalSquare_sine_nonnegative
    (side : InnerBoundarySide) (square : PlacedSquare) :
    0 ≤ (side.canonicalSquare square).frame.sine := by
  cases side <;> exact PlacedSquare.firstQuadrant_sine_nonnegative _

def BoundaryLineClipped (size : ℕ) (region : Set Plane) (side : InnerBoundarySide) : Prop :=
  ∀ coordinate, side.toBoundarySide.pointAt size coordinate ∈ region →
    coordinate ∈ Icc (9 / 10) ((size : ℝ) - 9 / 10)

lemma horizontal_cut_classification
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_above : height ≤ factor * square.center.y) :
    ((∀ point ∈ square.dilatedInteriorRegion factor, height ≤ point 1) ∨
      (0 < square.frame.cosine ∧ 0 < square.frame.sine ∧
        0 < horizontalCapHeight square factor height ∧
        horizontalCapHeight square factor height ≤ factor * square.frame.cosine ∧
        horizontalCapHeight square factor height ≤ factor * square.frame.sine)) ∨
    ∃ intervalStart intervalEnd : ℝ, factor ≤ intervalEnd - intervalStart ∧
      ∀ coordinate ∈ Ioo intervalStart intervalEnd,
        ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  by_cases line_intersects : ∃ coordinate,
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor
  · by_cases axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0
    · exact Or.inr (exists_horizontal_chord_of_axis_aligned square factor_positive
        cosine_nonnegative sine_nonnegative axis_aligned line_intersects)
    · push Not at axis_aligned
      have cosine_positive : 0 < square.frame.cosine :=
        lt_of_le_of_ne cosine_nonnegative axis_aligned.1.symm
      have sine_positive : 0 < square.frame.sine :=
        lt_of_le_of_ne sine_nonnegative axis_aligned.2.symm
      by_cases offset_bound : |height - factor * square.center.y| ≤
          factor * |square.frame.cosine - square.frame.sine| / 2
      · exact Or.inr (exists_horizontal_chord_of_center_offset_le square factor_positive
          cosine_positive sine_positive offset_bound)
      · have cap_positive := horizontalCapHeight_positive_of_line_intersects square
          factor_positive cosine_positive sine_positive line_intersects
        have offset_large := lt_of_not_ge offset_bound
        rw [abs_of_nonpos (sub_nonpos.mpr center_above)] at offset_large
        have difference_bound := mul_le_mul_of_nonneg_left
          (le_abs_self (square.frame.cosine - square.frame.sine)) factor_positive.le
        have reverse_difference_bound := mul_le_mul_of_nonneg_left
          (neg_le_abs (square.frame.cosine - square.frame.sine)) factor_positive.le
        refine Or.inl (Or.inr ⟨cosine_positive, sine_positive, cap_positive, ?_, ?_⟩)
        all_goals dsimp [horizontalCapHeight]; nlinarith
  · left
    left
    intro point point_mem
    by_contra below
    have vertical_continuous : Continuous (fun point : Plane => point 1) := continuous_apply 1
    obtain ⟨intersection, intersection_mem, on_line⟩ :=
      (square.convex_dilatedInteriorRegion factor).isPreconnected.intermediate_value
        point_mem (square.dilatedCenter_mem_dilatedInteriorRegion factor_positive)
        vertical_continuous.continuousOn ⟨(lt_of_not_ge below).le, center_above⟩
    apply line_intersects
    refine ⟨intersection 0, ?_⟩
    convert intersection_mem using 1
    funext axis
    fin_cases axis <;> simp [on_line]

lemma inner_boundary_cut_classification
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (center_inside : side.inwardThreshold size ≤
      side.inwardNormal (factor • square.center.toPlane))
    (clipped : BoundaryLineClipped size (square.dilatedInteriorRegion factor) side) :
    ((∀ point ∈ square.dilatedInteriorRegion factor,
        side.inwardThreshold size ≤ side.inwardNormal point) ∨
      AdjacentBoundaryCut size square factor side) ∨
      NagamochiResource.HasBoundaryChord size side.toBoundarySide
        (square.dilatedInteriorRegion factor) factor := by
  let canonical := side.canonicalSquare square
  have canonical_center : side.inwardThreshold size ≤ factor * canonical.center.y := by
    simpa only [canonical, side.canonicalSquare_center_vertical] using center_inside
  have transport : ∀ coordinate,
      ![coordinate, side.inwardThreshold size] ∈ canonical.dilatedInteriorRegion factor →
        side.toBoundarySide.pointAt size coordinate ∈ square.dilatedInteriorRegion factor := by
    intro coordinate point_mem
    rw [← side.canonicalPoint_boundaryPoint] at point_mem
    exact (side.mem_canonicalSquare_iff square factor_positive _).1 point_mem
  rcases horizontal_cut_classification canonical factor_positive
      (side.canonicalSquare_cosine_nonnegative square)
      (side.canonicalSquare_sine_nonnegative square) canonical_center with (inside | adjacent) | long
  · left
    left
    intro point point_mem
    have canonical_mem := (side.mem_canonicalSquare_iff square factor_positive point).2 point_mem
    simpa only [side.canonicalPoint_vertical] using inside _ canonical_mem
  · obtain ⟨cosine_positive, sine_positive, cap_positive, cap_le_cosine, cap_le_sine⟩ := adjacent
    refine Or.inl (Or.inr ⟨cosine_positive, sine_positive, cap_positive,
      cap_le_cosine, cap_le_sine, ?_⟩)
    intro coordinate coordinate_mem
    exact clipped coordinate (transport coordinate
      (horizontalAdjacentChord_of_cap_bounds canonical factor_positive
        cosine_positive sine_positive cap_le_cosine cap_le_sine coordinate coordinate_mem))
  · right
    obtain ⟨intervalStart, intervalEnd, length_bound, chord_inside⟩ := long
    have original_chord := fun coordinate coordinate_mem =>
      transport coordinate (chord_inside coordinate coordinate_mem)
    have segment_bound := fun coordinate coordinate_mem =>
      clipped coordinate (original_chord coordinate coordinate_mem)
    cases side <;>
      exact ⟨intervalStart, intervalEnd, length_bound, segment_bound, original_chord⟩

lemma score_gt_one_of_center_inner_without_corners
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (center_inside : factor • square.center.toPlane ∈
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (missing_corners : ∀ kind, NagamochiResource.cornerPoint size kind ∉
      square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let region := square.dilatedInteriorRegion factor
  let selected := NagamochiResource.boundarySides.filter fun side =>
    InnerBoundaryActive size region (boundarySideToInner side)
  let budget := fun side => (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size side region
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
    have budget_bound : ∑ side ∈ selected, budget side ≤ NagamochiResource.boundaryLines size region := by
      dsimp only [budget]
      rw [← Finset.mul_sum]
      exact NagamochiResource.boundaryLines_subset_lower_bound subset
    exact (add_le_add le_rfl budget_bound).trans
      (NagamochiResource.innerArea_add_boundaryLines_le_measure size region)
  · intro side selected_side
    have active := (Finset.mem_filter.mp selected_side).2
    have center_bound := (mem_innerRectangle_iff_inward_bounds size _).1 center_inside
      (boundarySideToInner side)
    have clipped := boundaryLine_clipped_of_active_and_missing_corners
      (square.convex_dilatedInteriorRegion factor) active missing_corners
    rcases inner_boundary_cut_classification square (boundarySideToInner side)
        factor_positive center_bound clipped with adjacent | long
    · left
      simpa only [boundarySideToInner_toBoundarySide] using
        boundaryCut_compensated_of_inside_or_adjacent square (boundarySideToInner side)
          factor_positive factor_at_most adjacent
    · right
      have line_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
        (square.measurableSet_dilatedInteriorRegion factor_positive.ne') long
      simpa only [boundarySideToInner_toBoundarySide] using
        mul_le_mul le_rfl line_bound (by positivity : (0 : ENNReal) ≤ _) bot_le

end SquarePackingArchive.Nagamochi
