import SquarePackingArchive.NagamochiBoundaryAnchor
import SquarePackingArchive.NagamochiCapLowerBound
import SquarePackingArchive.NagamochiInner

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem score_gt_one_of_bottom_adjacent_without_corners_and_edge_point
    (square : PlacedSquare) {size coordinate : ℕ} {side factor : ℝ}
    (fits : square.Fits side)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine)
    (missing_corners : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (point_mem : NagamochiResource.edgePoint size coordinate .bottom ∈
      square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  classical
  let region := square.dilatedInteriorRegion factor
  let selected := activeNonbottomSides size region
  let budget := fun boundary => (1 / 2 : ENNReal) *
    NagamochiResource.boundaryLine size boundary region
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_measurable : MeasurableSet region :=
    square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have selected_inside (boundary) (selected_mem : boundary ∈ selected) :
      (boundarySideToInner boundary).inwardThreshold size ≤
        (boundarySideToInner boundary).inwardNormal (factor • square.center.toPlane) := by
    have not_bottom := (Finset.mem_filter.mp selected_mem).2.1
    cases boundary <;>
      simp [boundarySideToInner, InnerBoundarySide.inwardThreshold,
        InnerBoundarySide.inwardNormal, Point.toPlane] at not_bottom ⊢
    · linarith
    · exact center_horizontal.1
    · linarith [center_horizontal.2]
  have classification (boundary) (selected_mem : boundary ∈ selected) :
      volume (boundaryCutRegion (boundarySideToInner boundary) size region) ≤ budget boundary ∨
        NagamochiResource.HasBoundaryChord size boundary region factor := by
    have active := (Finset.mem_filter.mp selected_mem).2.2
    have clipped := boundaryLine_clipped_of_active_and_missing_corners
      (square.convex_dilatedInteriorRegion factor) active missing_corners
    rcases inner_boundary_cut_classification square (boundarySideToInner boundary)
      factor_positive (selected_inside boundary selected_mem) clipped with adjacent | long
    · apply Or.inl
      simpa only [boundarySideToInner_toBoundarySide] using
        (boundaryCut_compensated_of_inside_or_adjacent square (boundarySideToInner boundary)
          factor_positive factor_at_most adjacent)
    · exact Or.inr (by simpa only [boundarySideToInner_toBoundarySide] using long)
  by_cases long_exists : ∃ boundary ∈ selected,
      NagamochiResource.HasBoundaryChord size boundary region factor
  · obtain ⟨boundary, _, long⟩ := long_exists
    exact score_gt_one_of_boundary_chord_and_edge_point factor_gt_one
      region_measurable long coordinate_mem point_mem
  have cuts_bound :
      (∑ boundary ∈ selected, volume (boundaryCutRegion (boundarySideToInner boundary) size region)) ≤
        ∑ boundary ∈ selected, budget boundary := by
    apply Finset.sum_le_sum
    intro boundary selected_mem
    rcases classification boundary selected_mem with compensated | long
    · exact compensated
    · exact False.elim (long_exists ⟨boundary, selected_mem, long⟩)
  have cap_bound := (upperCap_le_innerArea_add_nonbottomCuts square fits factor_gt_one
    (by omega) center_horizontal center_below).trans (add_le_add le_rfl cuts_bound)
  have clipped := bottom_line_clipped_of_edge_strip_and_missing_corners square fits
    factor_gt_one (by omega) center_horizontal center_below missing_corners
  have full_section_eq : volume {horizontal : ℝ | ![horizontal, 1] ∈ region} =
      NagamochiResource.boundaryLine size .bottom region := by
    rw [NagamochiResource.boundaryLine, horizontalSegmentMeasure_apply region_measurable]
    congr 1
    ext horizontal
    constructor
    · intro point_inside
      exact ⟨clipped horizontal point_inside, point_inside⟩
    · exact fun point_inside => point_inside.2
  have cap_strict := upperCap_area_add_half_section_gt_half_of_fits square factor_gt_one
    cosine_positive sine_positive inside_container cap_le_cosine cap_le_sine
  change (1 / 2 : ENNReal) < volume (region ∩ {point | 1 ≤ point 1}) +
    (1 / 2 : ENNReal) * volume {horizontal : ℝ | ![horizontal, 1] ∈ region} at cap_strict
  rw [full_section_eq] at cap_strict
  have selected_subset : insert NagamochiResource.BoundarySide.bottom selected ⊆
      NagamochiResource.boundarySides := by
    intro boundary _
    exact NagamochiResource.mem_boundarySides boundary
  have bottom_not_selected : NagamochiResource.BoundarySide.bottom ∉ selected := by
    simp [selected, activeNonbottomSides]
  have budgets_bound : (∑ boundary ∈ selected, budget boundary) + budget .bottom ≤
      NagamochiResource.boundaryLines size region := by
    have sum_bound := NagamochiResource.boundaryLines_subset_lower_bound
      (size := size) (region := region) selected_subset
    rw [Finset.sum_insert bottom_not_selected, mul_add] at sum_bound
    simpa only [budget, Finset.mul_sum, add_comm] using sum_bound
  have continuous_strict : (1 / 2 : ENNReal) < NagamochiResource.innerArea size region +
      NagamochiResource.boundaryLines size region :=
    cap_strict.trans_le ((add_le_add cap_bound le_rfl).trans (by
      rw [add_assoc]
      exact add_le_add le_rfl budgets_bound))
  have edge_bound := NagamochiResource.edgePoints_lower_bound_of_mem .bottom coordinate_mem
    region_measurable point_mem
  have strict_sum : (1 / 2 : ENNReal) + 1 / 2 <
      (NagamochiResource.innerArea size region + NagamochiResource.boundaryLines size region) + 1 / 2 :=
    (ENNReal.add_lt_add_iff_right (by finiteness)).2 continuous_strict
  have halves_eq : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [halves_eq] at strict_sum
  apply strict_sum.trans_le
  simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
  exact add_le_add (le_add_of_nonneg_right bot_le) edge_bound

theorem score_gt_one_of_bottom_adjacent_without_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine)
    (missing_corners : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have grid_witness := gridPointWitness_of_center_in_edge_strip_geometry square .bottom
    size_at_least_three factor_gt_one inside_container
    ⟨center_horizontal.1, center_horizontal.2, center_below⟩
  obtain ⟨coordinate, coordinate_mem, point_mem⟩ :=
    edge_mem_of_gridPointWitness_of_no_corner_points .bottom grid_witness
      (missing_corners _) (missing_corners _)
  exact score_gt_one_of_bottom_adjacent_without_corners_and_edge_point square fits
    size_at_least_three factor_gt_one factor_at_most cosine_positive sine_positive
    inside_container center_horizontal center_below cap_le_cosine cap_le_sine
    missing_corners coordinate_mem point_mem

theorem score_gt_one_of_bottom_strip_without_corners_nonnegative_frame
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (missing_corners : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have clipped := bottom_line_clipped_of_edge_strip_and_missing_corners square fits
    factor_gt_one (by omega) center_horizontal center_below missing_corners
  have grid_witness := gridPointWitness_of_center_in_edge_strip_geometry square .bottom
    size_at_least_three factor_gt_one inside_container
    ⟨center_horizontal.1, center_horizontal.2, center_below⟩
  obtain ⟨coordinate, coordinate_mem, point_mem⟩ :=
    edge_mem_of_gridPointWitness_of_no_corner_points .bottom grid_witness
      (missing_corners _) (missing_corners _)
  have score_of_long (intervalStart intervalEnd : ℝ)
      (length_bound : factor ≤ intervalEnd - intervalStart)
      (chord_inside : ∀ horizontal ∈ Ioo intervalStart intervalEnd,
        ![horizontal, 1] ∈ square.dilatedInteriorRegion factor) :
      1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
    have chord : NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) factor :=
      ⟨intervalStart, intervalEnd, length_bound,
        fun horizontal horizontal_mem => clipped horizontal (chord_inside horizontal horizontal_mem),
        chord_inside⟩
    exact score_gt_one_of_boundary_chord_and_edge_point factor_gt_one
      (square.measurableSet_dilatedInteriorRegion factor_positive.ne') chord coordinate_mem point_mem
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
  apply score_gt_one_of_bottom_adjacent_without_corners_and_edge_point square fits
    size_at_least_three factor_gt_one factor_at_most cosine_positive sine_positive
    inside_container center_horizontal center_below _ _ missing_corners coordinate_mem point_mem
  all_goals dsimp [horizontalUpperCapHeight]; nlinarith

theorem score_gt_one_of_bottom_strip_without_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side)
    (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (missing_corners : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq
    (zero_lt_one.trans factor_gt_one)
  have normalized_inside : square.firstQuadrant.dilatedInteriorRegion factor ⊆ containerRegion size :=
    region_eq.symm ▸ inside_container
  have normalized_missing : ∀ kind,
      NagamochiResource.cornerPoint size kind ∉ square.firstQuadrant.dilatedInteriorRegion factor := by
    simpa only [region_eq] using missing_corners
  have normalized_score := score_gt_one_of_bottom_strip_without_corners_nonnegative_frame
    square.firstQuadrant ((square.firstQuadrant_fits_iff side).2 fits)
    size_at_least_three factor_gt_one factor_at_most
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    normalized_inside (by simpa using center_horizontal) (by simpa using center_below)
    normalized_missing
  rwa [region_eq] at normalized_score

end SquarePackingArchive.Nagamochi
