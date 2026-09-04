import SquarePackingArchive.NagamochiBadSquare

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma unit_corner_localX_lt_half_factor
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine) :
    square.dilatedLocalX factor ⟨1, 1⟩ < factor / 2 := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have horizontal_bound := (square.center_bounds fits).1
  have vertical_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative,
    abs_of_nonneg sine_nonnegative] at horizontal_bound vertical_bound
  have cosine_at_most : square.frame.cosine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.sine]
  have sine_at_most : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.cosine]
  have product_bound := mul_nonneg (sub_nonneg.mpr cosine_at_most) (sub_nonneg.mpr sine_at_most)
  have scaled_horizontal := mul_le_mul_of_nonneg_left horizontal_bound
    (mul_nonneg factor_positive.le cosine_nonnegative)
  have scaled_vertical := mul_le_mul_of_nonneg_left vertical_bound
    (mul_nonneg factor_positive.le sine_nonnegative)
  have strict_factor := mul_lt_mul_of_pos_right factor_gt_one
    (by positivity : 0 < 1 + square.frame.cosine * square.frame.sine)
  dsimp [PlacedSquare.dilatedLocalX]
  nlinarith [square.frame.unit, mul_nonneg factor_positive.le
    (sq_nonneg (square.frame.cosine + square.frame.sine))]

lemma unit_corner_localY_ge_half_factor_of_bottom_corner_and_missing_inner_corner
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) :
    factor / 2 ≤ square.dilatedLocalY factor ⟨1, 1⟩ := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have corner_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive corner_mem
  rw [abs_lt, abs_lt] at corner_bounds
  have horizontal_upper := unit_corner_localX_lt_half_factor square fits factor_gt_one
    cosine_nonnegative sine_positive.le
  have vertical_upper_failure : factor / 2 ≤ square.dilatedLocalY factor ⟨1, 1⟩ := by
    by_contra! vertical_upper
    apply inner_corner_missing
    apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
    · rw [abs_lt]
      refine ⟨?_, horizontal_upper⟩
      dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at corner_bounds ⊢
      linarith [corner_bounds.1.1]
    · rw [abs_lt]
      refine ⟨?_, vertical_upper⟩
      dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at corner_bounds ⊢
      linarith [corner_bounds.2.1]
  exact vertical_upper_failure

theorem rightmost_vertex_beyond_two_of_bottom_corner_and_missing_inner_corner
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) :
    2 < factor * square.center.x +
      factor * (square.frame.cosine + square.frame.sine) / 2 := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have vertical_upper_failure := unit_corner_localY_ge_half_factor_of_bottom_corner_and_missing_inner_corner
    square fits factor_gt_one cosine_nonnegative sine_positive corner_mem inner_corner_missing
  have vertical_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative,
    abs_of_nonneg sine_positive.le] at vertical_bound
  have scaled_vertical := mul_le_mul_of_nonneg_left vertical_bound
    (mul_nonneg factor_positive.le cosine_nonnegative)
  have cosine_at_most : square.frame.cosine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.sine]
  have sine_at_most : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.cosine]
  have product_bound := mul_nonneg (sub_nonneg.mpr cosine_at_most) (sub_nonneg.mpr sine_at_most)
  have strict_factor := mul_lt_mul_of_pos_right factor_gt_one
    (by positivity : 0 < 1 + square.frame.cosine * square.frame.sine)
  dsimp [PlacedSquare.dilatedLocalY] at vertical_upper_failure
  apply (mul_lt_mul_iff_left₀ sine_positive).mp
  nlinarith [square.frame.unit]

lemma center_horizontal_distance_lt_one_of_mem
    (square : PlacedSquare) {factor : ℝ} {point : Plane}
    (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (point_mem : point ∈ square.dilatedInteriorRegion factor) :
    |point 0 - factor * square.center.x| < 1 := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem
  have horizontal_eq := congrArg Point.x point_eq
  have vertical_eq := congrArg Point.y point_eq
  simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at horizontal_eq vertical_eq
  have norm_identity : (point 0 - factor * square.center.x) ^ 2 +
      (point 1 - factor * square.center.y) ^ 2 = localX ^ 2 + localY ^ 2 := by
    rw [horizontal_eq, vertical_eq]
    linear_combination (localX ^ 2 + localY ^ 2) * square.frame.unit
  have norm_bound : (point 0 - factor * square.center.x) ^ 2 +
      (point 1 - factor * square.center.y) ^ 2 < 1 := by
    nlinarith [sq_abs localX, sq_abs localY, abs_nonneg localX, abs_nonneg localY]
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (point 1 - factor * square.center.y)]

lemma vertical_band_crossing_of_open_convex_closure
    {region : Set Plane} (region_convex : Convex ℝ region) (region_open : IsOpen region)
    {first second : Plane} {horizontal lower upper : ℝ}
    (first_mem : first ∈ region) (second_mem : second ∈ closure region)
    (first_horizontal : first 0 < horizontal) (second_horizontal : horizontal < second 0)
    (first_height : first 1 ∈ Icc lower upper) (second_height : second 1 ∈ Icc lower upper) :
    ∃ height ∈ Icc lower upper, ![horizontal, height] ∈ region := by
  let ratio := (horizontal - first 0) / (second 0 - first 0)
  have denominator_positive : 0 < second 0 - first 0 := by linarith
  have ratio_positive : 0 < ratio := div_pos (sub_pos.mpr first_horizontal) denominator_positive
  have ratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_one denominator_positive]
    linarith
  have segment_mem := lineMap_mem_openSegment ℝ first second ⟨ratio_positive, ratio_lt_one⟩
  have interior_mem := region_convex.openSegment_interior_closure_subset_interior
    (by simpa [region_open.interior_eq] using first_mem) second_mem segment_mem
  rw [region_open.interior_eq] at interior_mem
  let height := (1 - ratio) * first 1 + ratio * second 1
  have height_mem : height ∈ Icc lower upper := by
    dsimp [height]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ratio_lt_one.le) (sub_nonneg.mpr first_height.1),
        mul_nonneg ratio_positive.le (sub_nonneg.mpr second_height.1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ratio_lt_one.le) (sub_nonneg.mpr first_height.2),
        mul_nonneg ratio_positive.le (sub_nonneg.mpr second_height.2)]
  refine ⟨height, height_mem, ?_⟩
  convert interior_mem using 1
  funext coordinate
  fin_cases coordinate
  · simp [AffineMap.lineMap_apply_module, ratio]
    field_simp [ne_of_gt denominator_positive]
    ring
  · simp [AffineMap.lineMap_apply_module, height]

theorem boundary_band_crossing_of_rightmost_vertex_height
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor)
    (vertex_height : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 ∈ Icc (9 / 10 : ℝ) 1) :
    ∃ height ∈ Icc (9 / 10 : ℝ) 1, ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have rightmost := rightmost_vertex_beyond_two_of_bottom_corner_and_missing_inner_corner square
    fits factor_gt_one cosine_nonnegative sine_positive corner_mem inner_corner_missing
  have vertex_mem := square.dilatedPoint_mem_closure factor_positive
    (by rw [abs_of_nonneg (by positivity)] : |factor / 2| ≤ factor / 2)
    (by rw [abs_neg, abs_of_nonneg (by positivity)] : |-(factor / 2)| ≤ factor / 2)
  apply vertical_band_crossing_of_open_convex_closure
    (square.convex_dilatedInteriorRegion factor) (square.isOpen_dilatedInteriorRegion factor_positive.ne')
    corner_mem vertex_mem (by norm_num)
  · convert rightmost using 1
    dsimp [PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
    ring
  · norm_num
  · convert vertex_height using 1
    simp [PlacedSquare.dilatedPoint, Frame.place, Point.toPlane]
    ring

theorem boundary_band_crossing_of_high_rightmost_vertex
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor)
    (vertex_height : 1 ≤ factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2) :
    ∃ height ∈ Icc (9 / 10 : ℝ) 1, ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_distance := center_horizontal_distance_lt_one_of_mem square factor_positive factor_at_most corner_mem
  norm_num at center_distance
  rw [abs_lt] at center_distance
  have center_lt_two : factor * square.center.x < 2 := by linarith
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  let localX := (1 - factor * square.center.y + factor * square.frame.cosine / 2) / square.frame.sine
  have horizontal_lower : -(factor / 2) ≤ localX := by
    dsimp [localX]
    rw [le_div_iff₀ sine_positive]
    nlinarith [mul_nonneg factor_positive.le cosine_nonnegative,
      mul_nonneg factor_positive.le sine_positive.le]
  have horizontal_upper : localX ≤ factor / 2 := by
    dsimp [localX]
    rw [div_le_iff₀ sine_positive]
    linarith
  let edgePoint := square.dilatedPoint factor localX (-(factor / 2))
  have edge_mem : edgePoint.toPlane ∈ closure (square.dilatedInteriorRegion factor) :=
    square.dilatedPoint_mem_closure factor_positive (abs_le.mpr ⟨horizontal_lower, horizontal_upper⟩)
      (by rw [abs_neg, abs_of_nonneg (by positivity)])
  have edge_height : edgePoint.y = 1 := by
    dsimp [edgePoint, localX, PlacedSquare.dilatedPoint, Frame.place]
    field_simp
    ring
  have vertical_upper_failure := unit_corner_localY_ge_half_factor_of_bottom_corner_and_missing_inner_corner
    square fits factor_gt_one cosine_nonnegative sine_positive corner_mem inner_corner_missing
  have product_identity : square.frame.sine * edgePoint.x =
      square.dilatedLocalY factor ⟨1, 1⟩ + square.frame.sine + factor / 2 := by
    calc
      square.frame.sine * edgePoint.x = square.dilatedLocalY factor ⟨1, 1⟩ +
          square.frame.sine + factor * (square.frame.cosine ^ 2 + square.frame.sine ^ 2) / 2 := by
        dsimp [edgePoint, localX, PlacedSquare.dilatedPoint, Frame.place, PlacedSquare.dilatedLocalY]
        field_simp
        ring
      _ = _ := by rw [square.frame.unit, mul_one]
  have sine_at_most : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit, sq_nonneg square.frame.cosine]
  have edge_right : 2 < edgePoint.x := by
    apply (mul_lt_mul_iff_left₀ sine_positive).mp
    linarith
  apply vertical_band_crossing_of_open_convex_closure
    (square.convex_dilatedInteriorRegion factor) (square.isOpen_dilatedInteriorRegion factor_positive.ne')
    anchor edge_mem center_lt_two edge_right
  · norm_num
  · change edgePoint.y ∈ Icc (9 / 10 : ℝ) 1
    rw [edge_height]
    norm_num

theorem adjacent_cap_of_missing_boundary_band
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor)
    (band_missing : ∀ height ∈ Icc (9 / 10 : ℝ) 1,
      ![(2 : ℝ), height] ∉ square.dilatedInteriorRegion factor) :
    horizontalUpperCapHeight square factor 1 < factor * square.frame.cosine - 1 / 10 ∧
      horizontalUpperCapHeight square factor 1 < factor * square.frame.sine := by
  have rightmost_below : factor * square.center.y +
      factor * (square.frame.sine - square.frame.cosine) / 2 < 9 / 10 := by
    by_contra! not_below
    have crossing : ∃ height ∈ Icc (9 / 10 : ℝ) 1,
        ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor := by
      by_cases below_one : factor * square.center.y +
          factor * (square.frame.sine - square.frame.cosine) / 2 ≤ 1
      · exact boundary_band_crossing_of_rightmost_vertex_height square fits factor_gt_one
          cosine_nonnegative sine_positive corner_mem inner_corner_missing ⟨not_below, below_one⟩
      · exact boundary_band_crossing_of_high_rightmost_vertex square fits factor_gt_one factor_at_most
          cosine_nonnegative sine_positive center_below corner_mem inner_corner_missing (le_of_not_ge below_one)
    obtain ⟨height, height_mem, point_mem⟩ := crossing
    exact band_missing height height_mem point_mem
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have corner_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive corner_mem
  rw [abs_lt, abs_lt] at corner_bounds
  have horizontal_lower : -(factor / 2) < square.dilatedLocalX factor ⟨1, 1⟩ := by
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at corner_bounds ⊢
    linarith [corner_bounds.1.1]
  have vertical_upper_failure := unit_corner_localY_ge_half_factor_of_bottom_corner_and_missing_inner_corner
    square fits factor_gt_one cosine_nonnegative sine_positive corner_mem inner_corner_missing
  have identity : 1 - (factor * square.center.y +
      factor * (square.frame.cosine - square.frame.sine) / 2) =
      square.frame.sine * (square.dilatedLocalX factor ⟨1, 1⟩ + factor / 2) +
      square.frame.cosine * (square.dilatedLocalY factor ⟨1, 1⟩ - factor / 2) := by
    dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY]
    linear_combination -(1 - factor * square.center.y) * square.frame.unit
  have other_vertex_below : factor * square.center.y +
      factor * (square.frame.cosine - square.frame.sine) / 2 < 1 := by
    have positive := mul_pos sine_positive (by linarith :
      0 < square.dilatedLocalX factor ⟨1, 1⟩ + factor / 2)
    have nonnegative := mul_nonneg cosine_nonnegative (sub_nonneg.mpr vertical_upper_failure)
    linarith
  dsimp [horizontalUpperCapHeight]
  constructor <;> linarith

noncomputable def bottomLeftExitHeight (square : PlacedSquare) (factor : ℝ) : ℝ :=
  factor * square.center.y +
    (factor / 2 - (factor * square.center.x - 1) * square.frame.sine) / square.frame.cosine

noncomputable def bottomOffsetRightExitX (square : PlacedSquare) (factor : ℝ) : ℝ :=
  factor * square.center.x +
    (factor / 2 - (9 / 10 - factor * square.center.y) * square.frame.sine) / square.frame.cosine

theorem offset_right_exit_le_two_of_missing_boundary_band
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (cap_below : horizontalUpperCapHeight square factor 1 < factor * square.frame.cosine - 1 / 10)
    (band_missing : ∀ height ∈ Icc (9 / 10 : ℝ) 1,
      ![(2 : ℝ), height] ∉ square.dilatedInteriorRegion factor) :
    bottomOffsetRightExitX square factor ≤ 2 := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_positive.le, abs_of_nonneg sine_positive.le] at center_bound
  have scaled_center := mul_le_mul_of_nonneg_left center_bound factor_positive.le
  have component_sum_gt_one : 1 < square.frame.cosine + square.frame.sine := by
    nlinarith [square.frame.unit, mul_pos cosine_positive sine_positive]
  have factor_sum_gt_one : 1 < factor * (square.frame.cosine + square.frame.sine) := by
    nlinarith [mul_pos (sub_pos.mpr factor_gt_one) (add_pos cosine_positive sine_positive)]
  let localY := (9 / 10 - factor * square.center.y - factor * square.frame.sine / 2) / square.frame.cosine
  have local_lower : -(factor / 2) ≤ localY := by
    dsimp [localY]
    rw [le_div_iff₀ cosine_positive]
    dsimp [horizontalUpperCapHeight] at cap_below
    linarith
  have local_upper : localY ≤ factor / 2 := by
    dsimp [localY]
    rw [div_le_iff₀ cosine_positive]
    nlinarith
  let edgePoint := square.dilatedPoint factor (factor / 2) localY
  have edge_mem : edgePoint.toPlane ∈ closure (square.dilatedInteriorRegion factor) :=
    square.dilatedPoint_mem_closure factor_positive
      (by rw [abs_of_nonneg (by positivity)]) (abs_le.mpr ⟨local_lower, local_upper⟩)
  have edge_height : edgePoint.y = 9 / 10 := by
    dsimp [edgePoint, localY, PlacedSquare.dilatedPoint, Frame.place]
    field_simp
    ring
  have edge_horizontal : edgePoint.x = bottomOffsetRightExitX square factor := by
    dsimp [edgePoint, localY, bottomOffsetRightExitX, PlacedSquare.dilatedPoint, Frame.place]
    field_simp
    linear_combination 10 * factor * square.frame.unit
  by_contra! exit_beyond
  have crossing := vertical_band_crossing_of_open_convex_closure
    (square.convex_dilatedInteriorRegion factor) (square.isOpen_dilatedInteriorRegion factor_positive.ne')
    corner_mem edge_mem (by norm_num : ![(1 : ℝ), 9 / 10] 0 < 2)
    (by simpa only [Point.toPlane, Matrix.cons_val_zero, edge_horizontal] using exit_beyond)
    (by norm_num : ![(1 : ℝ), 9 / 10] 1 ∈ Icc (9 / 10 : ℝ) 1)
    (by change edgePoint.y ∈ Icc (9 / 10 : ℝ) 1; rw [edge_height]; norm_num)
  obtain ⟨height, height_mem, point_mem⟩ := crossing
  exact band_missing height height_mem point_mem

theorem left_exit_deficit_le_algebraic_bound
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (cap_below : horizontalUpperCapHeight square factor 1 < factor * square.frame.cosine - 1 / 10)
    (band_missing : ∀ height ∈ Icc (9 / 10 : ℝ) 1,
      ![(2 : ℝ), height] ∉ square.dilatedInteriorRegion factor) :
    1 - bottomLeftExitHeight square factor ≤
      ((1 - square.frame.cosine) * (1 - square.frame.sine) - square.frame.sine ^ 2 / 10) /
        square.frame.cosine ^ 2 := by
  have exit_bound := offset_right_exit_le_two_of_missing_boundary_band square fits factor_gt_one
    cosine_positive sine_positive corner_mem cap_below band_missing
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have center_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_positive.le, abs_of_nonneg sine_positive.le] at center_bound
  have scaled_center := mul_le_mul_of_nonneg_left center_bound factor_positive.le
  have cap_lower : square.frame.cosine + square.frame.sine - 1 ≤
      horizontalUpperCapHeight square factor 1 := by
    dsimp [horizontalUpperCapHeight]
    nlinarith [mul_nonneg (sub_nonneg.mpr factor_gt_one.le)
      (add_nonneg cosine_positive.le sine_positive.le)]
  have left_identity : square.frame.cosine * (1 - bottomLeftExitHeight square factor) =
      square.frame.cosine * (1 - factor * square.center.y) - factor / 2 +
        (factor * square.center.x - 1) * square.frame.sine := by
    dsimp [bottomLeftExitHeight]
    field_simp
    ring
  have right_identity : square.frame.cosine * bottomOffsetRightExitX square factor =
      square.frame.cosine * (factor * square.center.x) + factor / 2 -
        (9 / 10 - factor * square.center.y) * square.frame.sine := by
    dsimp [bottomOffsetRightExitX]
    field_simp
    ring
  have identity : square.frame.cosine ^ 2 * (1 - bottomLeftExitHeight square factor) +
      horizontalUpperCapHeight square factor 1 =
      square.frame.cosine * square.frame.sine - square.frame.sine ^ 2 / 10 +
        square.frame.cosine * square.frame.sine * (bottomOffsetRightExitX square factor - 2) := by
    dsimp [horizontalUpperCapHeight]
    linear_combination square.frame.cosine * left_identity - square.frame.sine * right_identity +
      (1 - factor * square.center.y) * square.frame.unit
  apply (le_div_iff₀ (sq_pos_of_pos cosine_positive)).mpr
  have remainder_nonpositive := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg cosine_positive.le sine_positive.le) (sub_nonpos.mpr exit_bound)
  nlinarith

lemma bottom_left_exit_height_bounds
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) :
    9 / 10 < bottomLeftExitHeight square factor ∧ bottomLeftExitHeight square factor ≤ 1 := by
  have corner_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square
    (zero_lt_one.trans factor_gt_one) corner_mem
  rw [abs_lt, abs_lt] at corner_bounds
  have vertical_upper_failure := unit_corner_localY_ge_half_factor_of_bottom_corner_and_missing_inner_corner
    square fits factor_gt_one cosine_positive.le sine_positive corner_mem inner_corner_missing
  dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at corner_bounds vertical_upper_failure
  constructor
  · have divided := (lt_div_iff₀ cosine_positive).2 (show
        (9 / 10 - factor * square.center.y) * square.frame.cosine <
          factor / 2 - (factor * square.center.x - 1) * square.frame.sine by
      nlinarith [corner_bounds.2.2])
    dsimp [bottomLeftExitHeight]
    linarith
  · have divided := (div_le_iff₀ cosine_positive).2 (show
        factor / 2 - (factor * square.center.x - 1) * square.frame.sine ≤
          (1 - factor * square.center.y) * square.frame.cosine by nlinarith)
    dsimp [bottomLeftExitHeight]
    linarith

theorem bottom_left_exit_chord
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) :
    NagamochiResource.HasBoundaryChord size .left (square.dilatedInteriorRegion factor)
      (bottomLeftExitHeight square factor - 9 / 10) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have exit_bounds := bottom_left_exit_height_bounds square fits factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have corner_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive corner_mem
  rw [abs_lt, abs_lt] at corner_bounds
  have horizontal_upper := unit_corner_localX_lt_half_factor square fits factor_gt_one
    cosine_positive.le sine_positive.le
  let exitPoint : Point := ⟨1, bottomLeftExitHeight square factor⟩
  have localX_lower : -(factor / 2) < square.dilatedLocalX factor exitPoint := by
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint, exitPoint] at corner_bounds ⊢
    nlinarith [corner_bounds.1.1]
  have localX_upper : square.dilatedLocalX factor exitPoint < factor / 2 := by
    dsimp [PlacedSquare.dilatedLocalX, exitPoint] at horizontal_upper ⊢
    nlinarith [exit_bounds.2]
  have localY_eq : square.dilatedLocalY factor exitPoint = factor / 2 := by
    dsimp [PlacedSquare.dilatedLocalY, exitPoint, bottomLeftExitHeight]
    field_simp
    ring
  have exit_mem : exitPoint.toPlane ∈ closure (square.dilatedInteriorRegion factor) := by
    have mem := square.dilatedPoint_mem_closure factor_positive
      (localY := square.dilatedLocalY factor exitPoint)
      (abs_le.mpr ⟨localX_lower.le, localX_upper.le⟩)
      (by rw [localY_eq, abs_of_nonneg (by positivity)])
    rwa [square.dilatedPoint_inverseCoordinates] at mem
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  refine ⟨9 / 10, bottomLeftExitHeight square factor, le_rfl, ?_, ?_⟩
  · intro height height_mem
    exact ⟨height_mem.1.le, by linarith [height_mem.2, exit_bounds.2]⟩
  · intro height height_mem
    let ratio := (height - 9 / 10) / (bottomLeftExitHeight square factor - 9 / 10)
    have denominator_positive : 0 < bottomLeftExitHeight square factor - 9 / 10 := by linarith [exit_bounds.1]
    have ratio_mem : ratio ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (sub_pos.mpr height_mem.1) denominator_positive
      · dsimp [ratio]
        rw [div_lt_one denominator_positive]
        linarith [height_mem.2]
    have segment_mem := lineMap_mem_openSegment ℝ ![(1 : ℝ), 9 / 10] exitPoint.toPlane ratio_mem
    have open_region := square.isOpen_dilatedInteriorRegion factor_positive.ne'
    have point_mem := (square.convex_dilatedInteriorRegion factor).openSegment_interior_closure_subset_interior
      (by simpa [open_region.interior_eq] using corner_mem) exit_mem segment_mem
    rw [open_region.interior_eq] at point_mem
    convert point_mem using 1
    funext coordinate
    fin_cases coordinate
    · simp [AffineMap.lineMap_apply_module, exitPoint, Point.toPlane]
    · have ratio_cancel : ratio * (bottomLeftExitHeight square factor - 9 / 10) = height - 9 / 10 := by
        dsimp [ratio]
        exact div_mul_cancel₀ _ (ne_of_gt denominator_positive)
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [exitPoint, Point.toPlane]
      nlinarith

theorem upperCap_le_innerArea_of_left_corner_and_missing_inner_corner
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (center_horizontal : 1 ≤ factor * square.center.x)
    (center_below : factor * square.center.y ≤ 1)
    (cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine)
    (cap_le_sine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.sine)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (inner_corner_missing : ![(1 : ℝ), 1] ∉ square.dilatedInteriorRegion factor) :
    volume (square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1}) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have anchor := bottom_centerline_anchor square fits factor_gt_one center_below
  have center_gt : 1 < factor * square.center.x := by
    by_contra! center_le
    have center_eq : factor * square.center.x = 1 := le_antisymm center_le center_horizontal
    exact inner_corner_missing (by simpa only [center_eq] using anchor)
  have covered : square.dilatedInteriorRegion factor ∩ {point | 1 ≤ point 1} ⊆
      square.dilatedInteriorRegion factor ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
    rintro point ⟨point_mem, above_cut⟩
    have projected := upperCap_vertical_projection_inside square factor_positive cosine_positive
      sine_positive cap_le_cosine cap_le_sine point_mem above_cut
    have horizontal_lower : 1 < point 0 := by
      by_contra! horizontal_le
      by_cases horizontal_eq : point 0 = 1
      · exact inner_corner_missing (by simpa only [horizontal_eq] using projected)
      have horizontal_lt : point 0 < 1 := lt_of_le_of_ne horizontal_le horizontal_eq
      exact inner_corner_missing (horizontal_openSegment_subset_of_convex
        (square.convex_dilatedInteriorRegion factor) (horizontal_lt.trans center_gt)
        projected anchor 1 ⟨horizontal_lt, center_gt⟩)
    have distances := dilated_square_coordinate_distance_lt_two square factor_positive factor_at_most
      point_mem corner_mem
    norm_num at distances
    rw [abs_lt, abs_lt] at distances
    refine ⟨point_mem, ?_, ?_⟩
    · intro coordinate
      fin_cases coordinate
      · exact horizontal_lower.le
      · exact above_cut
    · intro coordinate
      fin_cases coordinate <;> dsimp <;> linarith
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact measure_mono covered

lemma half_angle_quartic_negative {parameter : ℝ}
    (parameter_positive : 0 < parameter) (parameter_lt_one : parameter < 1) :
    5 * parameter ^ 4 - 20 * parameter ^ 2 + 18 * parameter - 5 < 0 := by
  have certificate : -(5 * parameter ^ 4 - 20 * parameter ^ 2 + 18 * parameter - 5) =
      5 * (1 - parameter) ^ 6 + 12 * parameter * (1 - parameter) ^ 5 +
      5 * parameter ^ 2 * (1 - parameter) ^ 4 +
      10 * parameter ^ 4 * (1 - parameter) ^ 2 +
      10 * parameter ^ 5 * (1 - parameter) + 2 * parameter ^ 6 := by ring
  have positive : 0 < -(5 * parameter ^ 4 - 20 * parameter ^ 2 + 18 * parameter - 5) := by
    rw [certificate]
    have : 0 < 1 - parameter := sub_pos.mpr parameter_lt_one
    positivity
  linarith

lemma no_crossing_exit_deficit_lt_cap_surplus {cosine sine : ℝ}
    (cosine_positive : 0 < cosine) (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) / cosine ^ 2 <
      (cosine + sine - 1) / (cosine + sine + 1) := by
  let parameter := sine / (1 + cosine)
  have denominator_positive : 0 < 1 + cosine := by positivity
  have parameter_positive : 0 < parameter := div_pos sine_positive denominator_positive
  have sine_lt_one : sine < 1 := by nlinarith [sq_pos_of_pos cosine_positive]
  have parameter_lt_one : parameter < 1 := by
    dsimp [parameter]
    rw [div_lt_one denominator_positive]
    linarith
  have parameter_unit_positive : 0 < 1 + parameter ^ 2 := by positivity
  have cosine_eq : cosine = (1 - parameter ^ 2) / (1 + parameter ^ 2) := by
    dsimp [parameter]
    field_simp
    nlinarith [unit, mul_self_nonneg cosine]
  have sine_eq : sine = 2 * parameter / (1 + parameter ^ 2) := by
    dsimp [parameter]
    field_simp
    nlinarith [unit]
  have quartic_negative := half_angle_quartic_negative parameter_positive parameter_lt_one
  have identity :
      (cosine ^ 2 * (cosine + sine - 1) -
        ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) * (cosine + sine + 1)) *
        (5 * (1 + parameter ^ 2) ^ 3) =
      (2 * parameter * (parameter + 1)) *
        -(5 * parameter ^ 4 - 20 * parameter ^ 2 + 18 * parameter - 5) := by
    rw [cosine_eq, sine_eq]
    field_simp
    ring
  have difference_positive : 0 < cosine ^ 2 * (cosine + sine - 1) -
      ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) * (cosine + sine + 1) := by
    apply (mul_pos_iff_of_pos_right (by positivity : 0 < 5 * (1 + parameter ^ 2) ^ 3)).mp
    rw [identity]
    exact mul_pos (by positivity) (neg_pos.mpr quartic_negative)
  apply (div_lt_div_iff₀ (sq_pos_of_pos cosine_positive)
    (by positivity : 0 < cosine + sine + 1)).mpr
  linarith

theorem bottom_bad_square_crosses_next_boundary_band_positive_frame
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    ∃ height ∈ Icc (9 / 10 : ℝ) 1, ![(2 : ℝ), height] ∈ square.dilatedInteriorRegion factor := by
  by_contra! band_missing
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  obtain ⟨first_missing, second_missing⟩ := bottom_bad_square_misses_horizontal_corners square
    fits size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  have inner_corner_missing := bottom_bad_square_excludes_adjacent_inner_corner square fits (by omega)
    factor_gt_one factor_at_most inside_container center_horizontal center_below first_missing second_missing corner_mem bad
  have cap_bounds := adjacent_cap_of_missing_boundary_band square fits factor_gt_one factor_at_most
    cosine_positive.le sine_positive center_below corner_mem inner_corner_missing band_missing
  have cap_le_cosine : horizontalUpperCapHeight square factor 1 ≤ factor * square.frame.cosine := by linarith [cap_bounds.1]
  have cap_le_sine := cap_bounds.2.le
  let cap := horizontalUpperCapHeight square factor 1
  have center_bound := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_positive.le, abs_of_nonneg sine_positive.le] at center_bound
  have scaled_center := mul_le_mul_of_nonneg_left center_bound factor_positive.le
  have cap_lower : square.frame.cosine + square.frame.sine - 1 ≤ cap := by
    dsimp [cap, horizontalUpperCapHeight]
    nlinarith [mul_nonneg (sub_nonneg.mpr factor_gt_one.le)
      (add_nonneg cosine_positive.le sine_positive.le)]
  have sum_gt_one : 1 < square.frame.cosine + square.frame.sine := by
    nlinarith [square.frame.unit, mul_pos cosine_positive sine_positive]
  have cap_positive : 0 < cap := by linarith
  let capScore := (cap / square.frame.sine) * (cap / square.frame.cosine) / 2 +
    cap / (square.frame.sine * square.frame.cosine) / 2
  have angle_bound := cap_score_ge_angle_bound cosine_positive sine_positive square.frame.unit cap_lower
  have deficit_bound := left_exit_deficit_le_algebraic_bound square fits factor_gt_one
    cosine_positive sine_positive corner_mem cap_bounds.1 band_missing
  have deficit_strict := deficit_bound.trans_lt
    (no_crossing_exit_deficit_lt_cap_surplus cosine_positive sine_positive square.frame.unit)
  have angle_identity : (square.frame.cosine + square.frame.sine - 1) /
      (square.frame.cosine + square.frame.sine + 1) =
      2 * ((square.frame.cosine + square.frame.sine) /
        (1 + square.frame.cosine + square.frame.sine)) - 1 := by
    field_simp
    ring
  have real_strict : 1 < capScore + (bottomLeftExitHeight square factor - 9 / 10) / 2 + 9 / 20 := by
    dsimp [capScore]
    nlinarith
  have exit_bounds := bottom_left_exit_height_bounds square fits factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have cap_budget := upperCap_area_add_half_section_lower_bound square factor_positive
    cosine_positive sine_positive cap_positive cap_le_cosine cap_le_sine
  have cap_contained := upperCap_le_innerArea_of_left_corner_and_missing_inner_corner square fits
    size_at_least_four factor_gt_one factor_at_most cosine_positive sine_positive center_horizontal.1
    center_below cap_le_cosine cap_le_sine corner_mem inner_corner_missing
  have clipped := bottom_line_clipped_of_missing_horizontal_corners square fits (by omega)
    factor_gt_one center_horizontal center_below first_missing second_missing
  have full_section_eq : volume {horizontal : ℝ | ![horizontal, 1] ∈ square.dilatedInteriorRegion factor} =
      NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) := by
    rw [NagamochiResource.boundaryLine, horizontalSegmentMeasure_apply measurable]
    congr 1
    ext horizontal
    exact ⟨fun point_mem => ⟨clipped horizontal point_mem, point_mem⟩, fun point_mem => point_mem.2⟩
  rw [full_section_eq] at cap_budget
  have cap_score_bound : ENNReal.ofReal capScore ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size .bottom (square.dilatedInteriorRegion factor) :=
    cap_budget.trans (add_le_add cap_contained le_rfl)
  have left_chord := bottom_left_exit_chord (size := size) square fits (by omega) factor_gt_one cosine_positive
    sine_positive corner_mem inner_corner_missing
  have left_bound := NagamochiResource.boundaryLine_lower_bound_of_chord measurable left_chord
  have weighted_left := mul_le_mul (a := (1 / 2 : ENNReal)) le_rfl left_bound bot_le bot_le
  have pair_subset : ({NagamochiResource.BoundarySide.bottom, .left} : Finset _) ⊆
      NagamochiResource.boundarySides := by
    intro boundary _
    exact NagamochiResource.mem_boundarySides boundary
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := square.dilatedInteriorRegion factor) pair_subset
  rw [Finset.sum_pair (by decide : NagamochiResource.BoundarySide.bottom ≠ .left), mul_add] at pair_bound
  have continuous_bound : ENNReal.ofReal capScore +
      (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        NagamochiResource.boundaryLines size (square.dilatedInteriorRegion factor) := by
    apply (add_le_add cap_score_bound weighted_left).trans
    rw [add_assoc]
    exact add_le_add le_rfl pair_bound
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem (size := size) .leftBottom measurable corner_mem
  have encoded_strict : (1 : ENNReal) < ENNReal.ofReal capScore +
      (1 / 2 : ENNReal) * ENNReal.ofReal (bottomLeftExitHeight square factor - 9 / 10) + 9 / 20 := by
    have strict := (ENNReal.ofReal_lt_ofReal_iff (by linarith :
      0 < capScore + (bottomLeftExitHeight square factor - 9 / 10) / 2 + 9 / 20)).2 real_strict
    have cap_nonnegative : 0 ≤ capScore := by dsimp [capScore]; positivity
    have length_nonnegative : 0 ≤ bottomLeftExitHeight square factor - 9 / 10 := by linarith [exit_bounds.1]
    rw [ENNReal.ofReal_one, ENNReal.ofReal_add
      (add_nonneg cap_nonnegative (div_nonneg length_nonnegative (by norm_num))) (by norm_num),
      ENNReal.ofReal_add cap_nonnegative (by linarith [exit_bounds.1]),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at strict
    have corner_encode : ENNReal.ofReal (9 / 20 : ℝ) = (9 / 20 : ENNReal) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    rw [corner_encode] at strict
    simpa only [ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul, mul_comm] using strict
  have score_strict := (encoded_strict.trans_le (add_le_add continuous_bound corner_bound)).trans_le
    (NagamochiResource.innerArea_add_boundaryLines_add_cornerPoints_le_measure size _)
  exact (not_lt_of_ge bad) score_strict

end SquarePackingArchive.Nagamochi
