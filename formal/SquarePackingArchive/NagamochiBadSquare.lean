import SquarePackingArchive.NagamochiEdgeStripWithCorners

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma dilated_square_squared_distance_lt_twice_factor_sq
    (square : PlacedSquare) {factor : ℝ} {first second : Plane}
    (factor_positive : 0 < factor)
    (first_mem : first ∈ square.dilatedInteriorRegion factor)
    (second_mem : second ∈ square.dilatedInteriorRegion factor) :
    (first 0 - second 0) ^ 2 + (first 1 - second 1) ^ 2 < 2 * factor ^ 2 := by
  obtain ⟨firstX, firstY, firstX_bound, firstY_bound, first_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive first).1 first_mem
  obtain ⟨secondX, secondY, secondX_bound, secondY_bound, second_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive second).1 second_mem
  have horizontal_difference : |firstX - secondX| < factor := by
    rw [abs_lt] at firstX_bound secondX_bound ⊢
    constructor <;> linarith
  have vertical_difference : |firstY - secondY| < factor := by
    rw [abs_lt] at firstY_bound secondY_bound ⊢
    constructor <;> linarith
  have first_horizontal := congrArg Point.x first_eq
  have first_vertical := congrArg Point.y first_eq
  have second_horizontal := congrArg Point.x second_eq
  have second_vertical := congrArg Point.y second_eq
  simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at first_horizontal first_vertical second_horizontal second_vertical
  have norm_identity : (first 0 - second 0) ^ 2 + (first 1 - second 1) ^ 2 =
      (firstX - secondX) ^ 2 + (firstY - secondY) ^ 2 := by
    rw [first_horizontal, first_vertical, second_horizontal, second_vertical]
    linear_combination ((firstX - secondX) ^ 2 + (firstY - secondY) ^ 2) * square.frame.unit
  nlinarith [sq_abs (firstX - secondX), sq_abs (firstY - secondY),
    abs_nonneg (firstX - secondX), abs_nonneg (firstY - secondY)]

lemma dilated_square_coordinate_distance_lt_two
    (square : PlacedSquare) {factor : ℝ} {first second : Plane}
    (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (first_mem : first ∈ square.dilatedInteriorRegion factor)
    (second_mem : second ∈ square.dilatedInteriorRegion factor) :
    |first 0 - second 0| < 2 ∧ |first 1 - second 1| < 2 := by
  have norm_bound := dilated_square_squared_distance_lt_twice_factor_sq square
    factor_positive first_mem second_mem
  constructor <;> rw [abs_lt] <;> constructor <;>
    nlinarith [sq_nonneg (first 0 - second 0), sq_nonneg (first 1 - second 1)]

lemma score_gt_one_of_half_bottom_budget_and_corner_connection
    {size : ℕ} {region : Set Plane}
    (region_measurable : MeasurableSet region)
    (bottom_budget : (1 / 2 : ENNReal) < NagamochiResource.innerArea size region +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom region)
    (boundary : NagamochiResource.BoundarySide) (not_bottom : boundary ≠ .bottom)
    (chord : NagamochiResource.HasBoundaryChord size boundary region (1 / 10))
    (kind : NagamochiResource.CornerPoint)
    (point_mem : NagamochiResource.cornerPoint size kind ∈ region) :
    1 < NagamochiResource.measure size region := by
  have side_bound := NagamochiResource.boundaryLine_lower_bound_of_chord region_measurable chord
  have weighted_side_bound : (1 / 20 : ENNReal) ≤
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size boundary region := by
    have bound := mul_le_mul (a := (1 / 2 : ENNReal)) le_rfl side_bound bot_le bot_le
    have constant_eq : (1 / 2 : ENNReal) * ENNReal.ofReal (1 / 10 : ℝ) = 1 / 20 := by
      norm_num [ENNReal.ofReal_div_of_pos, div_eq_mul_inv, mul_assoc, ← ENNReal.mul_inv]
    rwa [constant_eq] at bound
  have pair_subset : ({boundary, NagamochiResource.BoundarySide.bottom} : Finset _) ⊆
      NagamochiResource.boundarySides := by
    intro selected _
    exact NagamochiResource.mem_boundarySides selected
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := region) pair_subset
  rw [Finset.sum_pair not_bottom, mul_add] at pair_bound
  have added_bound : (NagamochiResource.innerArea size region +
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom region) + 1 / 20 ≤
        NagamochiResource.innerArea size region + NagamochiResource.boundaryLines size region := by
    rw [add_assoc]
    exact add_le_add le_rfl ((add_le_add le_rfl weighted_side_bound).trans
      (by simpa only [add_comm] using pair_bound))
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem kind region_measurable point_mem
  have first_strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 / 20 : ENNReal) ≠ ⊤)).2 bottom_budget
  have second_strict := (ENNReal.add_lt_add_iff_right (by finiteness : (9 / 20 : ENNReal) ≠ ⊤)).2 first_strict
  have constants : ((1 / 2 : ENNReal) + 1 / 20) + 9 / 20 = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [constants] at second_strict
  exact (second_strict.trans_le (add_le_add added_bound corner_bound)).trans_le
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size region)

theorem score_gt_one_of_bottom_strip_bottomLeft_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : NagamochiResource.cornerPoint size .bottomLeft ∈ square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have inner_corner_mem : ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
    by_cases center_eq : factor * square.center.x = 1
    · simpa only [center_eq] using anchor
    have center_gt : 1 < factor * square.center.x := lt_of_le_of_ne center_horizontal.1 (Ne.symm center_eq)
    exact horizontal_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
      (by linarith : (9 / 10 : ℝ) < factor * square.center.x) corner_mem anchor 1
      ⟨by norm_num, center_gt⟩
  have inner_positive := innerArea_positive_of_bottom_edge_strip_geometry square (by omega)
    factor_gt_one inside_container center_horizontal.1 center_horizontal.2 center_below
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have grid_witness := gridPointWitness_of_center_in_edge_strip_geometry square .bottom
    (by omega) factor_gt_one inside_container
    ⟨center_horizontal.1, center_horizontal.2, center_below⟩
  cases grid_witness with
  | firstCorner vertical_corner_mem =>
    have bottom_chord : NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) (1 / 10) := by
      refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
      · intro coordinate coordinate_mem
        exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
      · exact horizontal_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
          (by norm_num) corner_mem inner_corner_mem
    have left_chord : NagamochiResource.HasBoundaryChord size .left
        (square.dilatedInteriorRegion factor) (1 / 10) := by
      refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
      · intro coordinate coordinate_mem
        exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
      · exact vertical_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
          (by norm_num) vertical_corner_mem inner_corner_mem
    exact score_gt_one_of_case5_resource_bounds region_measurable inner_positive
      (by decide : NagamochiResource.BoundarySide.bottom ≠ .left)
      (by decide : NagamochiResource.CornerPoint.bottomLeft ≠ .leftBottom)
      bottom_chord left_chord corner_mem vertical_corner_mem
  | secondCorner vertical_corner_mem =>
    have distance := (dilated_square_coordinate_distance_lt_two square factor_positive factor_at_most
      corner_mem vertical_corner_mem).1
    norm_num [NagamochiResource.cornerPoint, NagamochiResource.EdgePoint.secondCornerPoint,
      InnerBoundarySide.toEdgePoint] at distance
    rw [abs_lt] at distance
    linarith
  | edge coordinate coordinate_mem point_mem =>
    exact score_gt_one_of_case7_first_boundary_corner_and_edge_point square .bottom
      (by omega) factor_positive.ne' inner_positive corner_mem inner_corner_mem
      coordinate_mem .bottom point_mem

theorem score_gt_one_of_bottom_strip_bottomRight_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : NagamochiResource.cornerPoint size .bottomRight ∈ square.dilatedInteriorRegion factor) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have inner_corner_mem : ![(size : ℝ) - 1, 1] ∈ square.dilatedInteriorRegion factor := by
    by_cases center_eq : factor * square.center.x = (size : ℝ) - 1
    · simpa only [center_eq] using anchor
    have center_lt : factor * square.center.x < (size : ℝ) - 1 :=
      lt_of_le_of_ne center_horizontal.2 center_eq
    exact horizontal_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
      (by linarith : factor * square.center.x < (size : ℝ) - 9 / 10) anchor corner_mem
      ((size : ℝ) - 1) ⟨center_lt, by linarith⟩
  have inner_positive := innerArea_positive_of_bottom_edge_strip_geometry square (by omega)
    factor_gt_one inside_container center_horizontal.1 center_horizontal.2 center_below
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have grid_witness := gridPointWitness_of_center_in_edge_strip_geometry square .bottom
    (by omega) factor_gt_one inside_container
    ⟨center_horizontal.1, center_horizontal.2, center_below⟩
  cases grid_witness with
  | firstCorner vertical_corner_mem =>
    have distance := (dilated_square_coordinate_distance_lt_two square factor_positive factor_at_most
      corner_mem vertical_corner_mem).1
    norm_num [NagamochiResource.cornerPoint, NagamochiResource.EdgePoint.firstCornerPoint,
      InnerBoundarySide.toEdgePoint] at distance
    rw [abs_lt] at distance
    linarith
  | secondCorner vertical_corner_mem =>
    have bottom_chord : NagamochiResource.HasBoundaryChord size .bottom
        (square.dilatedInteriorRegion factor) (1 / 10) := by
      refine ⟨(size : ℝ) - 1, (size : ℝ) - 9 / 10, by ring_nf; norm_num, ?_, ?_⟩
      · intro coordinate coordinate_mem
        exact ⟨by linarith [coordinate_mem.1], coordinate_mem.2.le⟩
      · exact horizontal_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
          (by linarith) inner_corner_mem corner_mem
    have right_chord : NagamochiResource.HasBoundaryChord size .right
        (square.dilatedInteriorRegion factor) (1 / 10) := by
      refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
      · intro coordinate coordinate_mem
        exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
      · exact vertical_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
          (by norm_num) vertical_corner_mem inner_corner_mem
    exact score_gt_one_of_case5_resource_bounds region_measurable inner_positive
      (by decide : NagamochiResource.BoundarySide.bottom ≠ .right)
      (by decide : NagamochiResource.CornerPoint.bottomRight ≠ .rightBottom)
      bottom_chord right_chord corner_mem vertical_corner_mem
  | edge coordinate coordinate_mem point_mem =>
    exact score_gt_one_of_case7_second_boundary_corner_and_edge_point square .bottom
      (by omega) factor_positive.ne' inner_positive inner_corner_mem corner_mem
      coordinate_mem .bottom point_mem

theorem bottom_bad_square_misses_horizontal_corners
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor ∧
      NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor := by
  constructor
  · intro point_mem
    exact (not_lt_of_ge bad) (score_gt_one_of_bottom_strip_bottomLeft_corner square fits
      size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below point_mem)
  · intro point_mem
    exact (not_lt_of_ge bad) (score_gt_one_of_bottom_strip_bottomRight_corner square fits
      size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below point_mem)

theorem bottom_bad_square_excludes_adjacent_inner_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor)
    (corner_mem : NagamochiResource.cornerPoint size .leftBottom ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor := by
  intro inner_corner_mem
  have bottom_budget := area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits size_at_least_three factor_gt_one factor_at_most inside_container
    center_horizontal center_below first_missing second_missing
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have chord : NagamochiResource.HasBoundaryChord size .left
      (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact vertical_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
        (by norm_num) corner_mem inner_corner_mem
  have score := score_gt_one_of_half_bottom_budget_and_corner_connection
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne')
    bottom_budget .left (by decide) chord .leftBottom corner_mem
  exact (not_lt_of_ge bad) score

theorem bottom_bad_square_has_no_edge_points
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉ square.dilatedInteriorRegion factor := by
  intro coordinate coordinate_mem kind point_mem
  have continuous_strict := continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits size_at_least_three factor_gt_one factor_at_most inside_container
    center_horizontal center_below first_missing second_missing
  have edge_bound := NagamochiResource.edgePoints_lower_bound_of_mem kind coordinate_mem
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne') point_mem
  have sum_strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 / 2 : ENNReal) ≠ ⊤)).2
    continuous_strict
  have constants : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [constants] at sum_strict
  have score : 1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
    apply sum_strict.trans_le
    simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
    exact add_le_add (le_add_of_nonneg_right bot_le) edge_bound
  exact (not_lt_of_ge bad) score

theorem bottom_bad_square_covers_vertical_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    NagamochiResource.cornerPoint size .leftBottom ∈ square.dilatedInteriorRegion factor ∨
      NagamochiResource.cornerPoint size .rightBottom ∈ square.dilatedInteriorRegion factor := by
  have no_edge_points := bottom_bad_square_has_no_edge_points square fits size_at_least_three
    factor_gt_one factor_at_most inside_container center_horizontal center_below
    first_missing second_missing bad
  have grid_witness := gridPointWitness_of_center_in_edge_strip_geometry square .bottom
    size_at_least_three factor_gt_one inside_container
    ⟨center_horizontal.1, center_horizontal.2, center_below⟩
  exact corner_mem_of_gridPointWitness_of_no_edge_points .bottom grid_witness
    (fun coordinate coordinate_mem => no_edge_points coordinate coordinate_mem .bottom)

theorem bottom_bad_square_excludes_right_inner_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor)
    (second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor)
    (corner_mem : NagamochiResource.cornerPoint size .rightBottom ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ![(size : ℝ) - 1, 1] ∉ square.dilatedInteriorRegion factor := by
  intro inner_corner_mem
  have bottom_budget := area_add_half_bottom_line_gt_half_of_bottom_strip_missing_horizontal_corners
    square fits size_at_least_three factor_gt_one factor_at_most inside_container
    center_horizontal center_below first_missing second_missing
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have chord : NagamochiResource.HasBoundaryChord size .right
      (square.dilatedInteriorRegion factor) (1 / 10) := by
    refine ⟨9 / 10, 1, by norm_num, ?_, ?_⟩
    · intro coordinate coordinate_mem
      exact ⟨coordinate_mem.1.le, by linarith [coordinate_mem.2]⟩
    · exact vertical_openSegment_subset_of_convex (square.convex_dilatedInteriorRegion factor)
        (by norm_num) corner_mem inner_corner_mem
  have score := score_gt_one_of_half_bottom_budget_and_corner_connection
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne')
    bottom_budget .right (by decide) chord .rightBottom corner_mem
  exact (not_lt_of_ge bad) score

theorem bottom_bad_square_location
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    (∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉ square.dilatedInteriorRegion factor) ∧
    ((NagamochiResource.cornerPoint size .leftBottom ∈ square.dilatedInteriorRegion factor ∧
      NagamochiResource.cornerPoint size .rightBottom ∉ square.dilatedInteriorRegion factor ∧
      ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) ∨
     (NagamochiResource.cornerPoint size .rightBottom ∈ square.dilatedInteriorRegion factor ∧
      NagamochiResource.cornerPoint size .leftBottom ∉ square.dilatedInteriorRegion factor ∧
      ![(size : ℝ) - 1, 1] ∉ square.dilatedInteriorRegion factor)) := by
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners
    square fits size_at_least_four factor_gt_one factor_at_most inside_container
    center_horizontal center_below bad
  have no_edge_points := bottom_bad_square_has_no_edge_points square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below
    first_missing second_missing bad
  have vertical_corner := bottom_bad_square_covers_vertical_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below
    first_missing second_missing bad
  have different_corners : ¬ (NagamochiResource.cornerPoint size .leftBottom ∈
      square.dilatedInteriorRegion factor ∧ NagamochiResource.cornerPoint size .rightBottom ∈
      square.dilatedInteriorRegion factor) := by
    rintro ⟨left_mem, right_mem⟩
    have distance := (dilated_square_coordinate_distance_lt_two square
      (zero_lt_one.trans factor_gt_one) factor_at_most left_mem right_mem).1
    norm_num [NagamochiResource.cornerPoint] at distance
    rw [abs_lt] at distance
    have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
    linarith
  refine ⟨no_edge_points, ?_⟩
  rcases vertical_corner with left_mem | right_mem
  · exact Or.inl ⟨left_mem, (fun right_mem => different_corners ⟨left_mem, right_mem⟩),
      bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega) factor_gt_one
        factor_at_most inside_container center_horizontal center_below first_missing
        second_missing left_mem bad⟩
  · exact Or.inr ⟨right_mem, (fun left_mem => different_corners ⟨left_mem, right_mem⟩),
      bottom_bad_square_excludes_right_inner_corner square fits (by omega) factor_gt_one
        factor_at_most inside_container center_horizontal center_below first_missing
        second_missing right_mem bad⟩

theorem bottom_bad_square_has_exactly_one_corner_point
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ∃ kind, (kind = NagamochiResource.CornerPoint.leftBottom ∨ kind = .rightBottom) ∧
      ∀ candidate, NagamochiResource.cornerPoint size candidate ∈
        square.dilatedInteriorRegion factor ↔ candidate = kind := by
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners
    square fits size_at_least_four factor_gt_one factor_at_most inside_container
    center_horizontal center_below bad
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have upper_missing : ∀ kind : NagamochiResource.CornerPoint,
      3 ≤ (NagamochiResource.cornerPoint size kind) 1 →
      NagamochiResource.cornerPoint size kind ∉ square.dilatedInteriorRegion factor := by
    intro kind height_bound point_mem
    have distance := (dilated_square_coordinate_distance_lt_two square
      (zero_lt_one.trans factor_gt_one) factor_at_most point_mem anchor).2
    norm_num at distance
    rw [abs_lt] at distance
    linarith
  have top_left_missing := upper_missing .topLeft (by
    norm_num [NagamochiResource.cornerPoint]; linarith)
  have top_right_missing := upper_missing .topRight (by
    norm_num [NagamochiResource.cornerPoint]; linarith)
  have left_top_missing := upper_missing .leftTop (by
    norm_num [NagamochiResource.cornerPoint]; linarith)
  have right_top_missing := upper_missing .rightTop (by
    norm_num [NagamochiResource.cornerPoint]; linarith)
  have location := (bottom_bad_square_location square fits size_at_least_four factor_gt_one
    factor_at_most inside_container center_horizontal center_below bad).2
  rcases location with ⟨left_mem, right_missing, _⟩ | ⟨right_mem, left_missing, _⟩
  · refine ⟨.leftBottom, Or.inl rfl, ?_⟩
    intro candidate
    cases candidate <;> simp_all
  · refine ⟨.rightBottom, Or.inr rfl, ?_⟩
    intro candidate
    cases candidate <;> simp_all

theorem score_gt_nineteen_twentieths_of_bottom_strip
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1) :
    (19 / 20 : ENNReal) < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  by_cases bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1
  · obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners
      square fits size_at_least_four factor_gt_one factor_at_most inside_container
      center_horizontal center_below bad
    have vertical_corner := bottom_bad_square_covers_vertical_corner square fits (by omega)
      factor_gt_one factor_at_most inside_container center_horizontal center_below
      first_missing second_missing bad
    rcases vertical_corner with left_mem | right_mem
    · exact score_gt_nineteen_twentieths_of_bottom_strip_with_corner square fits (by omega)
        factor_gt_one factor_at_most inside_container center_horizontal center_below
        first_missing second_missing .leftBottom left_mem
    · exact score_gt_nineteen_twentieths_of_bottom_strip_with_corner square fits (by omega)
        factor_gt_one factor_at_most inside_container center_horizontal center_below
        first_missing second_missing .rightBottom right_mem
  · have constant_lt : (19 / 20 : ENNReal) < 1 := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      norm_num
    exact constant_lt.trans (lt_of_not_ge bad)

end SquarePackingArchive.Nagamochi
