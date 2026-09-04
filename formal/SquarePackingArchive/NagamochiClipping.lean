import SquarePackingArchive.NagamochiCut

namespace SquarePackingArchive.Nagamochi

open Set

def InnerBoundaryActive (size : ℕ) (region : Set Plane)
    (side : InnerBoundarySide) : Prop :=
  ∃ point, point ∈ region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) ∧
    side.inwardNormal point = side.inwardThreshold size

lemma exists_active_boundary_of_outside
    {size : ℕ} {region : Set Plane} {center point : Plane}
    (region_convex : Convex ℝ region)
    (center_mem : center ∈ region)
    (center_inside : center ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (point_mem : point ∈ region)
    (point_outside : point ∉ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) :
    ∃ side, InnerBoundaryActive size region side ∧
      side.inwardNormal point < side.inwardThreshold size := by
  classical
  let sides : Finset InnerBoundarySide := {.bottom, .top, .left, .right}
  have every_side_mem (side : InnerBoundarySide) : side ∈ sides := by
    cases side <;> simp [sides]
  let crossed := sides.filter
    (fun side => side.inwardNormal point < side.inwardThreshold size)
  have crossed_iff (side : InnerBoundarySide) :
      side ∈ crossed ↔ side.inwardNormal point < side.inwardThreshold size := by
    simp [crossed, every_side_mem side]
  have crossed_nonempty : crossed.Nonempty := by
    have not_all : ¬∀ side : InnerBoundarySide,
        side.inwardThreshold size ≤ side.inwardNormal point := by
      simpa only [← mem_innerRectangle_iff_inward_bounds] using point_outside
    push Not at not_all
    obtain ⟨side, violated⟩ := not_all
    exact ⟨side, (crossed_iff side).2 violated⟩
  have center_bounds := (mem_innerRectangle_iff_inward_bounds size center).1 center_inside
  let entryRatio (side : InnerBoundarySide) :=
    (side.inwardThreshold size - side.inwardNormal point) /
      (side.inwardNormal center - side.inwardNormal point)
  have denominator_positive (side : InnerBoundarySide) (side_mem : side ∈ crossed) :
      0 < side.inwardNormal center - side.inwardNormal point := by
    have violated := (crossed_iff side).1 side_mem
    have center_bound := center_bounds side
    linarith
  have ratio_positive (side : InnerBoundarySide) (side_mem : side ∈ crossed) :
      0 < entryRatio side :=
    div_pos (sub_pos.mpr ((crossed_iff side).1 side_mem))
      (denominator_positive side side_mem)
  have ratio_upper (side : InnerBoundarySide) (side_mem : side ∈ crossed) :
      entryRatio side ≤ 1 := by
    dsimp [entryRatio]
    rw [div_le_one (denominator_positive side side_mem)]
    linarith [center_bounds side]
  obtain ⟨selected, selected_mem, maximum⟩ :=
    crossed.exists_max_image entryRatio crossed_nonempty
  let boundary := (1 - entryRatio selected) • point + entryRatio selected • center
  have boundary_mem : boundary ∈ region :=
    region_convex point_mem center_mem (sub_nonneg.mpr (ratio_upper selected selected_mem))
      (ratio_positive selected selected_mem).le (by ring)
  have boundary_value (side : InnerBoundarySide) :
      side.inwardNormal boundary =
        (1 - entryRatio selected) * side.inwardNormal point +
          entryRatio selected * side.inwardNormal center := by
    simp [boundary]
  have boundary_inside :
      boundary ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
    apply (mem_innerRectangle_iff_inward_bounds size boundary).2
    intro side
    rw [boundary_value]
    by_cases side_mem : side ∈ crossed
    · have ratio_le := maximum side side_mem
      dsimp [entryRatio] at ratio_le
      rw [div_le_iff₀ (denominator_positive side side_mem)] at ratio_le
      change side.inwardThreshold size - side.inwardNormal point ≤
        entryRatio selected *
          (side.inwardNormal center - side.inwardNormal point) at ratio_le
      nlinarith
    · have point_bound : side.inwardThreshold size ≤ side.inwardNormal point := by
        have := mt (crossed_iff side).2 side_mem
        linarith
      have ratio_nonnegative := (ratio_positive selected selected_mem).le
      have ratio_at_most := ratio_upper selected selected_mem
      nlinarith [mul_nonneg (sub_nonneg.mpr ratio_at_most)
        (sub_nonneg.mpr point_bound),
        mul_nonneg ratio_nonnegative (sub_nonneg.mpr (center_bounds side))]
  have boundary_on_side :
      selected.inwardNormal boundary = selected.inwardThreshold size := by
    rw [boundary_value]
    have cancellation : entryRatio selected *
        (selected.inwardNormal center - selected.inwardNormal point) =
        selected.inwardThreshold size - selected.inwardNormal point := by
      exact div_mul_cancel₀ _ (denominator_positive selected selected_mem).ne'
    nlinarith
  exact ⟨selected, ⟨boundary, ⟨boundary_mem, boundary_inside⟩, boundary_on_side⟩,
    (crossed_iff selected).1 selected_mem⟩

lemma InnerBoundaryActive.exists_coordinate
    {size : ℕ} {region : Set Plane} {side : InnerBoundarySide}
    (active : InnerBoundaryActive size region side) :
    ∃ coordinate, coordinate ∈ Icc (1 : ℝ) ((size : ℝ) - 1) ∧
      side.toBoundarySide.pointAt size coordinate ∈ region := by
  obtain ⟨point, ⟨point_mem, point_inner⟩, point_on_side⟩ := active
  have horizontal_bounds : point 0 ∈ Icc (1 : ℝ) ((size : ℝ) - 1) :=
    ⟨point_inner.1 0, point_inner.2 0⟩
  have vertical_bounds : point 1 ∈ Icc (1 : ℝ) ((size : ℝ) - 1) :=
    ⟨point_inner.1 1, point_inner.2 1⟩
  cases side with
  | bottom =>
      refine ⟨point 0, horizontal_bounds, ?_⟩
      convert point_mem using 1
      funext coordinate
      fin_cases coordinate <;>
        simp_all [InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold,
          InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt]
  | top =>
      refine ⟨point 0, horizontal_bounds, ?_⟩
      convert point_mem using 1
      funext coordinate
      fin_cases coordinate <;>
        simp_all [InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold,
          InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt]
      linarith
  | left =>
      refine ⟨point 1, vertical_bounds, ?_⟩
      convert point_mem using 1
      funext coordinate
      fin_cases coordinate <;>
        simp_all [InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold,
          InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt]
  | right =>
      refine ⟨point 1, vertical_bounds, ?_⟩
      convert point_mem using 1
      funext coordinate
      fin_cases coordinate <;>
        simp_all [InnerBoundarySide.inwardNormal, InnerBoundarySide.inwardThreshold,
          InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt]
      linarith

lemma boundary_openSegment_subset_of_convex
    {size : ℕ} {region : Set Plane}
    (side : NagamochiResource.BoundarySide)
    (region_convex : Convex ℝ region)
    {left right : ℝ} (left_lt_right : left < right)
    (left_mem : side.pointAt size left ∈ region)
    (right_mem : side.pointAt size right ∈ region) :
    ∀ coordinate ∈ Ioo left right, side.pointAt size coordinate ∈ region := by
  cases side with
  | bottom =>
      exact horizontal_openSegment_subset_of_convex region_convex
        left_lt_right left_mem right_mem
  | top =>
      exact horizontal_openSegment_subset_of_convex region_convex
        left_lt_right left_mem right_mem
  | left =>
      exact vertical_openSegment_subset_of_convex region_convex
        left_lt_right left_mem right_mem
  | right =>
      exact vertical_openSegment_subset_of_convex region_convex
        left_lt_right left_mem right_mem

lemma first_corner_mem_of_active_and_coordinate_below
    {size : ℕ} {region : Set Plane} {side : InnerBoundarySide} {coordinate : ℝ}
    (region_convex : Convex ℝ region)
    (active : InnerBoundaryActive size region side)
    (point_mem : side.toBoundarySide.pointAt size coordinate ∈ region)
    (coordinate_below : coordinate < 9 / 10) :
    NagamochiResource.cornerPoint size side.toBoundarySide.firstCornerPoint ∈ region := by
  obtain ⟨anchor, anchor_bounds, anchor_mem⟩ := active.exists_coordinate
  rw [← NagamochiResource.BoundarySide.pointAt_firstCorner]
  exact boundary_openSegment_subset_of_convex side.toBoundarySide region_convex
    (by linarith [anchor_bounds.1]) point_mem anchor_mem (9 / 10)
    ⟨coordinate_below, by linarith [anchor_bounds.1]⟩

lemma second_corner_mem_of_active_and_coordinate_above
    {size : ℕ} {region : Set Plane} {side : InnerBoundarySide} {coordinate : ℝ}
    (region_convex : Convex ℝ region)
    (active : InnerBoundaryActive size region side)
    (point_mem : side.toBoundarySide.pointAt size coordinate ∈ region)
    (coordinate_above : (size : ℝ) - 9 / 10 < coordinate) :
    NagamochiResource.cornerPoint size side.toBoundarySide.secondCornerPoint ∈ region := by
  obtain ⟨anchor, anchor_bounds, anchor_mem⟩ := active.exists_coordinate
  rw [← NagamochiResource.BoundarySide.pointAt_secondCorner]
  exact boundary_openSegment_subset_of_convex side.toBoundarySide region_convex
    (by linarith [anchor_bounds.2]) anchor_mem point_mem ((size : ℝ) - 9 / 10)
    ⟨by linarith [anchor_bounds.2], coordinate_above⟩

lemma boundaryLine_clipped_of_active_and_missing_corners
    {size : ℕ} {region : Set Plane} {side : InnerBoundarySide}
    (region_convex : Convex ℝ region)
    (active : InnerBoundaryActive size region side)
    (missing_corners : ∀ kind, NagamochiResource.cornerPoint size kind ∉ region) :
    ∀ coordinate, side.toBoundarySide.pointAt size coordinate ∈ region →
      coordinate ∈ Icc (9 / 10 : ℝ) ((size : ℝ) - 9 / 10) := by
  intro coordinate point_mem
  constructor
  · by_contra below
    exact missing_corners _ (first_corner_mem_of_active_and_coordinate_below
      region_convex active point_mem (lt_of_not_ge below))
  · by_contra above
    exact missing_corners _ (second_corner_mem_of_active_and_coordinate_above
      region_convex active point_mem (lt_of_not_ge above))

noncomputable def unclippedSquare : PlacedSquare where
  center := ⟨100 / 101, 165 / 101⟩
  frame := ⟨12 / 13, 5 / 13, by norm_num⟩

lemma unclippedSquare_center_inner :
    (101 / 100 : ℝ) * unclippedSquare.center.x ∈ Icc 1 3 ∧
      (101 / 100 : ℝ) * unclippedSquare.center.y ∈ Icc 1 3 := by
  norm_num [unclippedSquare]

lemma unclippedSquare_fits : unclippedSquare.Fits (400 / 101) := by
  intro point point_mem
  obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ := point_mem
  have horizontal := congrArg Point.x point_eq
  have vertical := congrArg Point.y point_eq
  rcases abs_le.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_le.mp localY_bound with ⟨localY_lower, localY_upper⟩
  simp [unclippedSquare, PlacedSquare.point, Frame.place] at horizontal vertical
  unfold Container.Contains
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma unclippedSquare_missing_corners
    (kind : NagamochiResource.CornerPoint) :
    NagamochiResource.cornerPoint 4 kind ∉
      unclippedSquare.dilatedInteriorRegion (101 / 100) := by
  intro point_mem
  rw [unclippedSquare.mem_dilatedInteriorRegion_iff (by norm_num)] at point_mem
  obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ := point_mem
  have horizontal := congrArg Point.x point_eq
  have vertical := congrArg Point.y point_eq
  rcases abs_lt.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_lt.mp localY_bound with ⟨localY_lower, localY_upper⟩
  cases kind <;>
    norm_num [unclippedSquare, NagamochiResource.cornerPoint, Plane.toPoint,
      PlacedSquare.dilatedPoint, Frame.place] at horizontal vertical <;>
    linarith

lemma unclippedSquare_bottom_point :
    ![(37 / 50 : ℝ), 1] ∈ unclippedSquare.dilatedInteriorRegion (101 / 100) := by
  apply unclippedSquare.mem_dilatedInteriorRegion_of_inverse_bounds (by norm_num)
  all_goals norm_num [unclippedSquare, PlacedSquare.dilatedLocalX,
    PlacedSquare.dilatedLocalY, Plane.toPoint]

theorem center_inner_missing_corners_does_not_imply_full_line_clipping :
    ¬(∀ (square : PlacedSquare),
      square.Fits (400 / 101) →
      (101 / 100 : ℝ) * square.center.x ∈ Icc 1 3 →
      (101 / 100 : ℝ) * square.center.y ∈ Icc 1 3 →
      (∀ kind, NagamochiResource.cornerPoint 4 kind ∉
        square.dilatedInteriorRegion (101 / 100)) →
      ∀ coordinate, ![coordinate, (1 : ℝ)] ∈
        square.dilatedInteriorRegion (101 / 100) →
        coordinate ∈ Icc (9 / 10 : ℝ) (4 - 9 / 10)) := by
  intro all_clipped
  have clipped := all_clipped unclippedSquare unclippedSquare_fits
    unclippedSquare_center_inner.1 unclippedSquare_center_inner.2
    unclippedSquare_missing_corners (37 / 50) unclippedSquare_bottom_point
  norm_num at clipped

end SquarePackingArchive.Nagamochi
