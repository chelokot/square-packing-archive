import SquarePackingArchive.PackingPointCapacity
import SquarePackingArchive.Records.Square7

namespace SquarePackingArchive.Records.Square6

noncomputable def green (ratio : ℝ) (index : Fin 7) : Point :=
  (Square8.points index).scale ratio

noncomputable def red (ratio : ℝ) (index : Fin 7) : Point :=
  (Square8.points index).swap.scale ratio

theorem scaled_lattices_unavoidable {side : ℝ}
    (side_positive : 0 < side) (side_lt_three : side < 3) :
    InteriorUnavoidable (green (side / 3)) side ∧
      InteriorUnavoidable (red (side / 3)) side := by
  have factor_gt_one : 1 < 3 / side :=
    (lt_div_iff₀ side_positive).2 (by simpa using side_lt_three)
  have green_unavoidable := Unavoidable.interior_scaled (factor := 3 / side)
    (side := side) (by simpa [side_positive.ne'] using Square8.points_unavoidable) factor_gt_one
  have red_unavoidable := Unavoidable.interior_scaled (factor := 3 / side)
    (side := side) (by simpa [side_positive.ne'] using Square7.transposed_points_unavoidable) factor_gt_one
  constructor
  · change InteriorUnavoidable (fun index => (Square8.points index).scale (side / 3)) side
    simpa using green_unavoidable
  · change InteriorUnavoidable (fun index => (Square8.points index).swap.scale (side / 3)) side
    simpa using red_unavoidable

theorem center_free_lattice_saturation {side : ℝ}
    (packing : Packing 6 side) (side_lt_three : side < 3)
    (center_uncovered : ∀ owner,
      ¬ (packing.squares owner).InteriorContains (green (side / 3) 3)) :
    (∀ index : Fin 7, index ≠ 3 → ∃! owner,
      (packing.squares owner).InteriorContains (green (side / 3) index)) ∧
    (∀ index : Fin 7, index ≠ 3 → ∃! owner,
      (packing.squares owner).InteriorContains (red (side / 3) index)) ∧
    (∀ owner first second, first ≠ 3 → second ≠ 3 →
      (packing.squares owner).InteriorContains (green (side / 3) first) →
      (packing.squares owner).InteriorContains (green (side / 3) second) → first = second) ∧
    (∀ owner first second, first ≠ 3 → second ≠ 3 →
      (packing.squares owner).InteriorContains (red (side / 3) first) →
      (packing.squares owner).InteriorContains (red (side / 3) second) → first = second) := by
  have side_positive := packing.side_positive (by norm_num)
  obtain ⟨green_unavoidable, red_unavoidable⟩ := scaled_lattices_unavoidable side_positive side_lt_three
  have common_center : green (side / 3) 3 = red (side / 3) 3 := by
    simp [green, red, Point.swap]
  have green_saturated := packing.deleted_point_saturation_of_uncovered
    (green (side / 3)) 3 green_unavoidable center_uncovered
  have red_saturated := packing.deleted_point_saturation_of_uncovered
    (red (side / 3)) 3 red_unavoidable (by simpa [← common_center] using center_uncovered)
  exact ⟨green_saturated.1, red_saturated.1, green_saturated.2, red_saturated.2⟩

theorem center_owner_contains_neighbor {side : ℝ}
    (packing : Packing 6 side) (side_lt_three : side < 3) (owner : Fin 6)
    (center_mem : (packing.squares owner).InteriorContains (green (side / 3) 3)) :
    (packing.squares owner).InteriorContains (red (side / 3) 5) ∨
      (packing.squares owner).InteriorContains (red (side / 3) 1) ∨
      (packing.squares owner).InteriorContains (green (side / 3) 5) ∨
      (packing.squares owner).InteriorContains (green (side / 3) 1) := by
  have side_positive := packing.side_positive (by norm_num)
  have cross := (packing.squares owner).interiorContains_one_cross_point
    (radius := side / 6) (by positivity) (by linarith) center_mem
  have east_eq : Point.mk ((green (side / 3) 3).x + side / 6)
      (green (side / 3) 3).y = red (side / 3) 5 := by
    simp [green, red, Point.scale, Point.swap]
    ring
  have west_eq : Point.mk ((green (side / 3) 3).x - side / 6)
      (green (side / 3) 3).y = red (side / 3) 1 := by
    simp [green, red, Point.scale, Point.swap]
    ring
  have north_eq : Point.mk (green (side / 3) 3).x
      ((green (side / 3) 3).y + side / 6) = green (side / 3) 5 := by
    simp [green, Point.scale]
    ring
  have south_eq : Point.mk (green (side / 3) 3).x
      ((green (side / 3) 3).y - side / 6) = green (side / 3) 1 := by
    simp [green, Point.scale]
    ring
  simpa only [east_eq, west_eq, north_eq, south_eq] using cross

theorem perpendicular_midpoints_force_additional_point_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (bottom_mem : square.Contains ⟨3 / 2, 1⟩)
    (left_mem : square.Contains ⟨1, 3 / 2⟩) :
    square.Contains ⟨3 / 2, 3 / 2⟩ ∨
      square.Contains ⟨9 / 10, 1⟩ ∨ square.Contains ⟨1, 9 / 10⟩ := by
  have horizontal_gap : 3 / 5 * square.frame.cosine + 1 / 2 * square.frame.sine < 1 := by
    have square_bound : (3 / 5 * square.frame.cosine + 1 / 2 * square.frame.sine) ^ 2 ≤ 61 / 100 := by
      nlinarith [square.frame.unit, sq_nonneg (5 * square.frame.cosine - 6 * square.frame.sine)]
    nlinarith
  have vertical_gap : 1 / 2 * square.frame.cosine + 3 / 5 * square.frame.sine < 1 := by
    have square_bound : (1 / 2 * square.frame.cosine + 3 / 5 * square.frame.sine) ^ 2 ≤ 61 / 100 := by
      nlinarith [square.frame.unit, sq_nonneg (6 * square.frame.cosine - 5 * square.frame.sine)]
    nlinarith
  have bottom_bounds := (square.contains_iff_localCoordinates _).1 bottom_mem
  have left_bounds := (square.contains_iff_localCoordinates _).1 left_mem
  rw [abs_le, abs_le] at bottom_bounds left_bounds
  by_cases center_mem : square.Contains ⟨3 / 2, 3 / 2⟩
  · exact Or.inl center_mem
  apply Or.inr
  have center_vertical : |square.localY ⟨3 / 2, 3 / 2⟩| ≤ 1 / 2 := by
    rw [abs_le]
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds left_bounds ⊢
    constructor <;> linarith
  have center_horizontal_lower : -(1 / 2) ≤ square.localX ⟨3 / 2, 3 / 2⟩ := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds left_bounds ⊢
    linarith
  have center_horizontal_upper : 1 / 2 < square.localX ⟨3 / 2, 3 / 2⟩ := by
    by_contra! upper
    exact center_mem ((square.contains_iff_localCoordinates _).2
      ⟨abs_le.mpr ⟨center_horizontal_lower, upper⟩, center_vertical⟩)
  by_cases slope_bound : square.frame.sine ≤ 5 * square.frame.cosine
  · apply Or.inl
    rw [square.contains_iff_localCoordinates, abs_le, abs_le]
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds left_bounds center_horizontal_upper ⊢
    constructor <;> constructor <;> linarith
  · apply Or.inr
    have reverse_slope_bound : square.frame.cosine ≤ 5 * square.frame.sine := by linarith
    rw [square.contains_iff_localCoordinates, abs_le, abs_le]
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds left_bounds center_horizontal_upper ⊢
    constructor <;> constructor <;> linarith

theorem perpendicular_midpoints_force_additional_point {square : PlacedSquare}
    (bottom_mem : square.Contains ⟨3 / 2, 1⟩)
    (left_mem : square.Contains ⟨1, 3 / 2⟩) :
    square.Contains ⟨3 / 2, 3 / 2⟩ ∨
      square.Contains ⟨9 / 10, 1⟩ ∨ square.Contains ⟨1, 9 / 10⟩ := by
  have result := perpendicular_midpoints_force_additional_point_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    ((square.firstQuadrant_contains_iff _).2 bottom_mem)
    ((square.firstQuadrant_contains_iff _).2 left_mem)
  simpa using result

theorem corner_pair_forces_corner_nonnegative_frame
    {square : PlacedSquare} {side : ℝ} (fits : square.Fits side)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (left_mem : square.Contains ⟨9 / 10, 1⟩)
    (bottom_mem : square.Contains ⟨1, 9 / 10⟩) : square.Contains ⟨1, 1⟩ := by
  have left_bounds := (square.contains_iff_localCoordinates _).1 left_mem
  have bottom_bounds := (square.contains_iff_localCoordinates _).1 bottom_mem
  rw [abs_le, abs_le] at left_bounds bottom_bounds
  have leftmost := (fits (point := square.point (-1 / 2) (1 / 2))
    ⟨-1 / 2, 1 / 2, by norm_num, by norm_num, rfl⟩).1
  have lowest := (fits (point := square.point (-1 / 2) (-1 / 2))
    ⟨-1 / 2, -1 / 2, by norm_num, by norm_num, rfl⟩).2.2.1
  have center_x_lower : 0 ≤ square.center.x - (square.frame.cosine + square.frame.sine) / 2 := by
    dsimp [PlacedSquare.point, Frame.place] at leftmost
    linarith
  have center_y_lower : 0 ≤ square.center.y - (square.frame.cosine + square.frame.sine) / 2 := by
    dsimp [PlacedSquare.point, Frame.place] at lowest
    linarith
  have horizontal_upper : square.localX ⟨1, 1⟩ ≤ 1 / 2 := by
    dsimp [PlacedSquare.localX]
    nlinarith [mul_nonneg cosine_nonnegative center_x_lower,
      mul_nonneg sine_nonnegative center_y_lower,
      sq_nonneg (square.frame.cosine + square.frame.sine - 1)]
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at left_bounds bottom_bounds horizontal_upper ⊢
  constructor <;> constructor <;> linarith

theorem corner_pair_forces_corner {square : PlacedSquare} {side : ℝ}
    (fits : square.Fits side)
    (left_mem : square.Contains ⟨9 / 10, 1⟩)
    (bottom_mem : square.Contains ⟨1, 9 / 10⟩) : square.Contains ⟨1, 1⟩ := by
  have result := corner_pair_forces_corner_nonnegative_frame ((square.firstQuadrant_fits_iff side).2 fits)
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    ((square.firstQuadrant_contains_iff _).2 left_mem)
    ((square.firstQuadrant_contains_iff _).2 bottom_mem)
  simpa using result

theorem shallow_component_bound {frame : Frame}
    (cosine_nonnegative : 0 ≤ frame.cosine) (sine_nonnegative : 0 ≤ frame.sine)
    (projection_bound : frame.cosine / 10 + 11 * frame.sine / 10 ≤ 1) :
    frame.sine ≤ 5 * frame.cosine := by
  by_contra! slope
  have sine_upper : frame.sine ≤ 10 / 11 := by linarith
  have cosine_upper : frame.cosine ≤ 2 / 11 := by linarith
  have sine_sq := mul_self_le_mul_self sine_nonnegative sine_upper
  have cosine_sq := mul_self_le_mul_self cosine_nonnegative cosine_upper
  nlinarith [frame.unit]

theorem steep_component_bound {frame : Frame}
    (cosine_nonnegative : 0 ≤ frame.cosine) (sine_nonnegative : 0 ≤ frame.sine)
    (projection_bound : 11 * frame.cosine / 10 + frame.sine / 2 ≤ 1) :
    frame.cosine ≤ frame.sine := by
  by_contra! slope
  have projection_nonnegative : 0 ≤ 11 * frame.cosine / 10 + frame.sine / 2 := by positivity
  have projection_sq := mul_self_le_mul_self projection_nonnegative projection_bound
  have product_nonnegative := mul_nonneg sine_nonnegative (sub_nonneg.mpr slope.le)
  nlinarith [frame.unit, sq_nonneg frame.sine]

theorem corner_and_upper_left_force_left_midpoint_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : square.Contains ⟨9 / 10, 1⟩)
    (upper_mem : square.Contains ⟨1, 21 / 10⟩) :
    square.Contains ⟨1, 3 / 2⟩ := by
  have corner_bounds := (square.contains_iff_localCoordinates _).1 corner_mem
  have upper_bounds := (square.contains_iff_localCoordinates _).1 upper_mem
  rw [abs_le, abs_le] at corner_bounds upper_bounds
  have projection_bound : square.frame.cosine / 10 + 11 * square.frame.sine / 10 ≤ 1 := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds upper_bounds
    linarith
  have slope := shallow_component_bound cosine_nonnegative sine_nonnegative projection_bound
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds upper_bounds ⊢
  constructor <;> constructor <;> linarith

theorem corner_and_lower_right_force_bottom_midpoint_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : square.Contains ⟨9 / 10, 1⟩)
    (lower_mem : square.Contains ⟨2, 9 / 10⟩) :
    square.Contains ⟨3 / 2, 1⟩ := by
  have corner_bounds := (square.contains_iff_localCoordinates _).1 corner_mem
  have lower_bounds := (square.contains_iff_localCoordinates _).1 lower_mem
  rw [abs_le, abs_le] at corner_bounds lower_bounds
  have projection_bound : square.frame.cosine / 10 + 11 * square.frame.sine / 10 ≤ 1 := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds lower_bounds
    linarith
  have slope := shallow_component_bound cosine_nonnegative sine_nonnegative projection_bound
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds lower_bounds ⊢
  constructor <;> constructor <;> linarith

theorem corner_and_right_midpoint_force_bottom_midpoint_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : square.Contains ⟨9 / 10, 1⟩)
    (right_mem : square.Contains ⟨2, 3 / 2⟩) :
    square.Contains ⟨3 / 2, 1⟩ := by
  have corner_bounds := (square.contains_iff_localCoordinates _).1 corner_mem
  have right_bounds := (square.contains_iff_localCoordinates _).1 right_mem
  rw [abs_le, abs_le] at corner_bounds right_bounds
  have projection_bound : 11 * square.frame.cosine / 10 + square.frame.sine / 2 ≤ 1 := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds right_bounds
    linarith
  have slope := steep_component_bound cosine_nonnegative sine_nonnegative projection_bound
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds right_bounds ⊢
  constructor <;> constructor <;> linarith

theorem bottom_and_upper_left_force_center_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (bottom_mem : square.Contains ⟨3 / 2, 1⟩)
    (upper_mem : square.Contains ⟨1, 21 / 10⟩) :
    square.Contains ⟨3 / 2, 3 / 2⟩ := by
  have bottom_bounds := (square.contains_iff_localCoordinates _).1 bottom_mem
  have upper_bounds := (square.contains_iff_localCoordinates _).1 upper_mem
  rw [abs_le, abs_le] at bottom_bounds upper_bounds
  have projection_bound : 11 * square.frame.cosine / 10 + square.frame.sine / 2 ≤ 1 := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds upper_bounds
    linarith
  have slope := steep_component_bound cosine_nonnegative sine_nonnegative projection_bound
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at bottom_bounds upper_bounds ⊢
  constructor <;> constructor <;> linarith

theorem opposite_corner_points_incompatible_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : square.Contains ⟨9 / 10, 1⟩)
    (opposite_mem : square.Contains ⟨2, 21 / 10⟩) : False := by
  have corner_bounds := (square.contains_iff_localCoordinates _).1 corner_mem
  have opposite_bounds := (square.contains_iff_localCoordinates _).1 opposite_mem
  rw [abs_le, abs_le] at corner_bounds opposite_bounds
  have sum_lower : 1 ≤ square.frame.cosine + square.frame.sine := by
    nlinarith [square.frame.unit, mul_nonneg cosine_nonnegative sine_nonnegative]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at corner_bounds opposite_bounds
  linarith

theorem corner_singleton_pair {square : PlacedSquare} {redIndex : Fin 7}
    (corner_mem : square.Contains (Square8.points 0))
    (red_mem : square.Contains (Square8.points redIndex).swap)
    (green_unique : ∀ index, square.Contains (Square8.points index) → index = 0)
    (red_unique : ∀ index, square.Contains (Square8.points index).swap → index = redIndex) :
    redIndex = 0 ∨ redIndex = 1 := by
  let normalized := square.firstQuadrant
  have cosine_nonnegative : 0 ≤ normalized.frame.cosine := square.firstQuadrant_cosine_nonnegative
  have sine_nonnegative : 0 ≤ normalized.frame.sine := square.firstQuadrant_sine_nonnegative
  have normalized_corner : normalized.Contains ⟨9 / 10, 1⟩ :=
    (square.firstQuadrant_contains_iff _).2 corner_mem
  have normalized_red : normalized.Contains (Square8.points redIndex).swap :=
    (square.firstQuadrant_contains_iff _).2 red_mem
  have normalized_green_unique (index : Fin 7) (contained : normalized.Contains (Square8.points index)) :
      index = 0 := green_unique index ((square.firstQuadrant_contains_iff _).1 contained)
  have normalized_red_unique (index : Fin 7) (contained : normalized.Contains (Square8.points index).swap) :
      index = redIndex := red_unique index ((square.firstQuadrant_contains_iff _).1 contained)
  fin_cases redIndex
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have forced := corner_and_upper_left_force_left_midpoint_nonnegative_frame
      cosine_nonnegative sine_nonnegative normalized_corner normalized_red
    have impossible := normalized_red_unique 1 forced
    omega
  · have impossible := normalized_green_unique 3 normalized_red
    omega
  · have forced := corner_and_lower_right_force_bottom_midpoint_nonnegative_frame
      cosine_nonnegative sine_nonnegative normalized_corner normalized_red
    have impossible := normalized_green_unique 1 forced
    omega
  · have forced := corner_and_right_midpoint_force_bottom_midpoint_nonnegative_frame
      cosine_nonnegative sine_nonnegative normalized_corner normalized_red
    have impossible := normalized_green_unique 1 forced
    omega
  · exact False.elim (opposite_corner_points_incompatible_nonnegative_frame
      cosine_nonnegative sine_nonnegative normalized_corner normalized_red)

theorem bottom_and_upper_left_force_center {square : PlacedSquare}
    (bottom_mem : square.Contains ⟨3 / 2, 1⟩)
    (upper_mem : square.Contains ⟨1, 21 / 10⟩) :
    square.Contains ⟨3 / 2, 3 / 2⟩ := by
  have result := bottom_and_upper_left_force_center_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    ((square.firstQuadrant_contains_iff _).2 bottom_mem)
    ((square.firstQuadrant_contains_iff _).2 upper_mem)
  simpa using result

theorem bottom_singleton_pair {square : PlacedSquare} {redIndex : Fin 7}
    (bottom_mem : square.Contains (Square8.points 1))
    (red_mem : square.Contains (Square8.points redIndex).swap)
    (green_unique : ∀ index, square.Contains (Square8.points index) → index = 1)
    (red_unique : ∀ index, square.Contains (Square8.points index).swap → index = redIndex) :
    redIndex = 0 ∨ redIndex = 4 := by
  fin_cases redIndex
  · exact Or.inl rfl
  · rcases perpendicular_midpoints_force_additional_point bottom_mem red_mem with center_mem | corner_mem | corner_mem
    · have impossible := green_unique 3 center_mem
      omega
    · have impossible := green_unique 0 corner_mem
      omega
    · have impossible := red_unique 0 corner_mem
      omega
  · have impossible := green_unique 3 (bottom_and_upper_left_force_center bottom_mem red_mem)
    omega
  · have impossible := green_unique 3 red_mem
    omega
  · exact Or.inr rfl
  · have reflected_bottom : (square.reflectX 3).Contains ⟨3 / 2, 1⟩ := by
      have point_eq : (Point.mk (3 / 2) 1).reflectX 3 = ⟨3 / 2, 1⟩ := by norm_num [Point.reflectX]
      rw [← point_eq]
      exact (square.reflectX_contains_iff 3 _).2 bottom_mem
    have reflected_left : (square.reflectX 3).Contains ⟨1, 3 / 2⟩ := by
      have point_eq : (Point.mk 2 (3 / 2)).reflectX 3 = ⟨1, 3 / 2⟩ := by norm_num [Point.reflectX]
      rw [← point_eq]
      exact (square.reflectX_contains_iff 3 _).2 red_mem
    rcases perpendicular_midpoints_force_additional_point reflected_bottom reflected_left with center_mem | corner_mem | corner_mem
    · have original_center : square.Contains (Square8.points 3) :=
        (square.reflectX_contains_iff 3 _).1 (by norm_num [Point.reflectX]; exact center_mem)
      have impossible := green_unique 3 original_center
      omega
    · have original_corner : square.Contains (Square8.points 2) :=
        (square.reflectX_contains_iff 3 _).1 (by norm_num [Point.reflectX]; exact corner_mem)
      have impossible := green_unique 2 original_corner
      omega
    · have original_corner : square.Contains (Square8.points 4).swap :=
        (square.reflectX_contains_iff 3 _).1 (by norm_num [Point.reflectX, Point.swap]; exact corner_mem)
      have impossible := red_unique 4 original_corner
      omega
  · have reflected_bottom : (square.reflectX 3).Contains ⟨3 / 2, 1⟩ := by
      have point_eq : (Point.mk (3 / 2) 1).reflectX 3 = ⟨3 / 2, 1⟩ := by norm_num [Point.reflectX]
      rw [← point_eq]
      exact (square.reflectX_contains_iff 3 _).2 bottom_mem
    have reflected_upper : (square.reflectX 3).Contains ⟨1, 21 / 10⟩ := by
      have point_eq : (Point.mk 2 (21 / 10)).reflectX 3 = ⟨1, 21 / 10⟩ := by norm_num [Point.reflectX]
      rw [← point_eq]
      exact (square.reflectX_contains_iff 3 _).2 red_mem
    have reflected_center := bottom_and_upper_left_force_center reflected_bottom reflected_upper
    have original_center : square.Contains (Square8.points 3) :=
      (square.reflectX_contains_iff 3 _).1 (by norm_num [Point.reflectX]; exact reflected_center)
    have impossible := green_unique 3 original_center
    omega

def reflectHorizontalIndex : Fin 7 → Fin 7 := ![2, 1, 0, 3, 6, 5, 4]

def reflectVerticalIndex : Fin 7 → Fin 7 := ![4, 5, 6, 3, 0, 1, 2]

theorem reflectHorizontalIndex_involution (index : Fin 7) :
    reflectHorizontalIndex (reflectHorizontalIndex index) = index := by
  fin_cases index <;> rfl

theorem reflectVerticalIndex_involution (index : Fin 7) :
    reflectVerticalIndex (reflectVerticalIndex index) = index := by
  fin_cases index <;> rfl

theorem green_horizontal_reflection (index : Fin 7) :
    Square8.points (reflectHorizontalIndex index) = (Square8.points index).reflectX 3 := by
  fin_cases index <;> dsimp [reflectHorizontalIndex, Square8.points, Point.reflectX] <;> norm_num

theorem red_horizontal_reflection (index : Fin 7) :
    (Square8.points (reflectVerticalIndex index)).swap = (Square8.points index).swap.reflectX 3 := by
  fin_cases index <;> dsimp [reflectVerticalIndex, Square8.points, Point.reflectX, Point.swap] <;> norm_num

theorem green_vertical_reflection (index : Fin 7) :
    Square8.points (reflectVerticalIndex index) = (Square8.points index).reflectY 3 := by
  fin_cases index <;> dsimp [reflectVerticalIndex, Square8.points, Point.reflectY] <;> norm_num

theorem red_vertical_reflection (index : Fin 7) :
    (Square8.points (reflectHorizontalIndex index)).swap = (Square8.points index).swap.reflectY 3 := by
  fin_cases index <;> dsimp [reflectHorizontalIndex, Square8.points, Point.reflectY, Point.swap] <;> norm_num

structure SingletonPair (square : PlacedSquare) (greenIndex redIndex : Fin 7) : Prop where
  green_mem : square.Contains (Square8.points greenIndex)
  red_mem : square.Contains (Square8.points redIndex).swap
  green_unique : ∀ index, square.Contains (Square8.points index) → index = greenIndex
  red_unique : ∀ index, square.Contains (Square8.points index).swap → index = redIndex

theorem SingletonPair.reflectX {square : PlacedSquare} {greenIndex redIndex : Fin 7}
    (pair : SingletonPair square greenIndex redIndex) :
    SingletonPair (square.reflectX 3) (reflectHorizontalIndex greenIndex) (reflectVerticalIndex redIndex) := by
  constructor
  · rw [green_horizontal_reflection]
    exact (square.reflectX_contains_iff 3 _).2 pair.green_mem
  · rw [red_horizontal_reflection]
    exact (square.reflectX_contains_iff 3 _).2 pair.red_mem
  · intro index contained
    have reflected_mem : square.Contains (Square8.points (reflectHorizontalIndex index)) := by
      rw [green_horizontal_reflection]
      apply (square.reflectX_contains_iff 3 _).1
      simpa using contained
    have assigned := pair.green_unique (reflectHorizontalIndex index) reflected_mem
    simpa only [reflectHorizontalIndex_involution] using congrArg reflectHorizontalIndex assigned
  · intro index contained
    have reflected_mem : square.Contains (Square8.points (reflectVerticalIndex index)).swap := by
      rw [red_horizontal_reflection]
      apply (square.reflectX_contains_iff 3 _).1
      simpa using contained
    have assigned := pair.red_unique (reflectVerticalIndex index) reflected_mem
    simpa only [reflectVerticalIndex_involution] using congrArg reflectVerticalIndex assigned

theorem SingletonPair.reflectY {square : PlacedSquare} {greenIndex redIndex : Fin 7}
    (pair : SingletonPair square greenIndex redIndex) :
    SingletonPair (square.reflectY 3) (reflectVerticalIndex greenIndex) (reflectHorizontalIndex redIndex) := by
  constructor
  · rw [green_vertical_reflection]
    exact (square.reflectY_contains_iff 3 _).2 pair.green_mem
  · rw [red_vertical_reflection]
    exact (square.reflectY_contains_iff 3 _).2 pair.red_mem
  · intro index contained
    have reflected_mem : square.Contains (Square8.points (reflectVerticalIndex index)) := by
      rw [green_vertical_reflection]
      apply (square.reflectY_contains_iff 3 _).1
      simpa using contained
    have assigned := pair.green_unique (reflectVerticalIndex index) reflected_mem
    simpa only [reflectVerticalIndex_involution] using congrArg reflectVerticalIndex assigned
  · intro index contained
    have reflected_mem : square.Contains (Square8.points (reflectHorizontalIndex index)).swap := by
      rw [red_vertical_reflection]
      apply (square.reflectY_contains_iff 3 _).1
      simpa using contained
    have assigned := pair.red_unique (reflectHorizontalIndex index) reflected_mem
    simpa only [reflectHorizontalIndex_involution] using congrArg reflectHorizontalIndex assigned

def AllowedSingletonPair (greenIndex redIndex : Fin 7) : Prop :=
  match greenIndex.val with
  | 0 => redIndex = 0 ∨ redIndex = 1
  | 1 => redIndex = 0 ∨ redIndex = 4
  | 2 => redIndex = 4 ∨ redIndex = 5
  | 4 => redIndex = 1 ∨ redIndex = 2
  | 5 => redIndex = 2 ∨ redIndex = 6
  | 6 => redIndex = 5 ∨ redIndex = 6
  | _ => False

theorem SingletonPair.allowed {square : PlacedSquare} {greenIndex redIndex : Fin 7}
    (pair : SingletonPair square greenIndex redIndex) (not_center : greenIndex ≠ 3) :
    AllowedSingletonPair greenIndex redIndex := by
  fin_cases greenIndex
  · exact corner_singleton_pair pair.green_mem pair.red_mem pair.green_unique pair.red_unique
  · exact bottom_singleton_pair pair.green_mem pair.red_mem pair.green_unique pair.red_unique
  · have reflected := pair.reflectX
    have allowed := corner_singleton_pair reflected.green_mem reflected.red_mem
      reflected.green_unique reflected.red_unique
    fin_cases redIndex <;> simp_all [AllowedSingletonPair, reflectVerticalIndex]
  · exact False.elim (not_center rfl)
  · have reflected := pair.reflectY
    have allowed := corner_singleton_pair reflected.green_mem reflected.red_mem
      reflected.green_unique reflected.red_unique
    fin_cases redIndex <;> simp_all [AllowedSingletonPair, reflectHorizontalIndex]
  · have reflected := pair.reflectY
    have allowed := bottom_singleton_pair reflected.green_mem reflected.red_mem
      reflected.green_unique reflected.red_unique
    fin_cases redIndex <;> simp_all [AllowedSingletonPair, reflectHorizontalIndex]
  · have reflected := pair.reflectX.reflectY
    have allowed := corner_singleton_pair reflected.green_mem reflected.red_mem
      reflected.green_unique reflected.red_unique
    fin_cases redIndex <;> simp_all [AllowedSingletonPair, reflectHorizontalIndex, reflectVerticalIndex]

def firstMatching : Fin 7 → Fin 7 := ![0, 4, 5, 3, 1, 2, 6]

def secondMatching : Fin 7 → Fin 7 := ![1, 0, 4, 3, 2, 6, 5]

theorem singleton_matchings_exhaustive (assigned : Fin 7 → Fin 7)
    (injective : Function.Injective assigned) (center_fixed : assigned 3 = 3)
    (allowed : ∀ index, index ≠ 3 → AllowedSingletonPair index (assigned index)) :
    assigned = firstMatching ∨ assigned = secondMatching := by
  have zero_cases := allowed 0 (by decide)
  have one_cases := allowed 1 (by decide)
  have two_cases := allowed 2 (by decide)
  have four_cases := allowed 4 (by decide)
  have five_cases := allowed 5 (by decide)
  have six_cases := allowed 6 (by decide)
  change assigned 0 = 0 ∨ assigned 0 = 1 at zero_cases
  change assigned 1 = 0 ∨ assigned 1 = 4 at one_cases
  change assigned 2 = 4 ∨ assigned 2 = 5 at two_cases
  change assigned 4 = 1 ∨ assigned 4 = 2 at four_cases
  change assigned 5 = 2 ∨ assigned 5 = 6 at five_cases
  change assigned 6 = 5 ∨ assigned 6 = 6 at six_cases
  have distinct_zero_one := injective.ne (by decide : (0 : Fin 7) ≠ 1)
  have distinct_one_two := injective.ne (by decide : (1 : Fin 7) ≠ 2)
  have distinct_two_six := injective.ne (by decide : (2 : Fin 7) ≠ 6)
  have distinct_six_five := injective.ne (by decide : (6 : Fin 7) ≠ 5)
  have distinct_five_four := injective.ne (by decide : (5 : Fin 7) ≠ 4)
  have distinct_four_zero := injective.ne (by decide : (4 : Fin 7) ≠ 0)
  rcases zero_cases with zero_first | zero_second
  · left
    funext index
    fin_cases index <;> dsimp [firstMatching]
    all_goals omega
  · right
    funext index
    fin_cases index <;> dsimp [secondMatching]
    all_goals omega

theorem center_free_closed_family_has_two_matchings
    (squares : Fin 6 → PlacedSquare)
    (fits : ∀ owner, (squares owner).Fits 3)
    (disjoint : ∀ first second, first ≠ second → ∀ point,
      ¬ ((squares first).Contains point ∧ (squares second).Contains point))
    (center_uncovered : ∀ owner, ¬ (squares owner).Contains (Square8.points 3)) :
    ∃ assigned : Fin 7 → Fin 7,
      (assigned = firstMatching ∨ assigned = secondMatching) ∧
      ∀ index, index ≠ 3 → ∃ owner, SingletonPair (squares owner) index (assigned index) := by
  classical
  have green_hit (owner : Fin 6) : ∃ index : Fin 7, index ≠ 3 ∧
      (squares owner).Contains (Square8.points index) := by
    obtain ⟨index, contained⟩ := Square8.points_unavoidable (squares owner) (fits owner)
    refine ⟨index, ?_, contained⟩
    intro equality
    exact center_uncovered owner (equality ▸ contained)
  have red_center_uncovered (owner : Fin 6) :
      ¬ (squares owner).Contains (Square8.points 3).swap := center_uncovered owner
  have red_hit (owner : Fin 6) : ∃ index : Fin 7, index ≠ 3 ∧
      (squares owner).Contains (Square8.points index).swap := by
    obtain ⟨index, contained⟩ := Square7.transposed_points_unavoidable (squares owner) (fits owner)
    refine ⟨index, ?_, contained⟩
    intro equality
    exact red_center_uncovered owner (equality ▸ contained)
  have green_saturation := deleted_incidence_saturation
    (fun owner index => (squares owner).Contains (Square8.points index))
    (fun first second different index => disjoint first second different (Square8.points index)) 3 green_hit
  have red_saturation := deleted_incidence_saturation
    (fun owner index => (squares owner).Contains (Square8.points index).swap)
    (fun first second different index => disjoint first second different (Square8.points index).swap) 3 red_hit
  let ownerOf (index : Fin 7) (different : index ≠ 3) : Fin 6 :=
    (green_saturation.1 index different).choose
  have owner_mem (index : Fin 7) (different : index ≠ 3) :
      (squares (ownerOf index different)).Contains (Square8.points index) :=
    (green_saturation.1 index different).choose_spec.1
  let assigned (index : Fin 7) : Fin 7 :=
    if different : index = 3 then 3 else (red_hit (ownerOf index different)).choose
  have assigned_not_center (index : Fin 7) (different : index ≠ 3) : assigned index ≠ 3 := by
    simp only [assigned, dif_neg different]
    exact (red_hit (ownerOf index different)).choose_spec.1
  have pairs (index : Fin 7) (different : index ≠ 3) :
      SingletonPair (squares (ownerOf index different)) index (assigned index) := by
    have assigned_mem : (squares (ownerOf index different)).Contains (Square8.points (assigned index)).swap := by
      simp only [assigned, dif_neg different]
      exact (red_hit (ownerOf index different)).choose_spec.2
    refine ⟨owner_mem index different, assigned_mem, ?_, ?_⟩
    · intro other other_mem
      have other_ne : other ≠ 3 := by
        intro equality
        exact center_uncovered (ownerOf index different) (equality ▸ other_mem)
      exact green_saturation.2 _ other index other_ne different other_mem (owner_mem index different)
    · intro other other_mem
      have other_ne : other ≠ 3 := by
        intro equality
        exact red_center_uncovered (ownerOf index different) (equality ▸ other_mem)
      exact red_saturation.2 _ other (assigned index) other_ne
        (assigned_not_center index different) other_mem assigned_mem
  have center_fixed : assigned 3 = 3 := by simp [assigned]
  have injective : Function.Injective assigned := by
    intro first second same
    by_cases first_center : first = 3
    · by_cases second_center : second = 3
      · exact first_center.trans second_center.symm
      · have impossible := assigned_not_center second second_center
        rw [first_center, center_fixed] at same
        exact False.elim (impossible same.symm)
    by_cases second_center : second = 3
    · have impossible := assigned_not_center first first_center
      rw [second_center, center_fixed] at same
      exact False.elim (impossible same)
    have first_pair := pairs first first_center
    have second_pair := pairs second second_center
    have owner_eq : ownerOf first first_center = ownerOf second second_center := by
      by_contra different
      exact disjoint _ _ different (Square8.points (assigned first)).swap
        ⟨first_pair.red_mem, by rw [same]; exact second_pair.red_mem⟩
    rw [owner_eq] at first_pair
    exact (first_pair.green_unique second second_pair.green_mem).symm
  refine ⟨assigned, singleton_matchings_exhaustive assigned injective center_fixed ?_, ?_⟩
  · intro index different
    exact (pairs index different).allowed different
  · intro index different
    exact ⟨ownerOf index different, pairs index different⟩

noncomputable def horizontalIntercept (parameter : ℝ) : ℝ := (1 + parameter ^ 2) / (1 + parameter)

noncomputable def verticalIntercept (parameter : ℝ) : ℝ := (1 + 2 * parameter - parameter ^ 2) / 2

theorem horizontalIntercept_lower_bound {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) :
    2 * Real.sqrt 2 - 2 ≤ horizontalIntercept parameter := by
  have denominator_positive : 0 < 1 + parameter := by linarith
  rw [horizontalIntercept, le_div_iff₀ denominator_positive]
  have root_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [sq_nonneg (parameter - (Real.sqrt 2 - 1))]

theorem verticalIntercept_lower_bound {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most_one : parameter ≤ 1) :
    1 / 2 ≤ verticalIntercept parameter := by
  dsimp [verticalIntercept]
  nlinarith [mul_nonneg parameter_nonnegative (sub_nonneg.mpr parameter_at_most_one)]

theorem intercept_sum_lower_bound {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most_one : parameter ≤ 1) :
    3 / 2 ≤ horizontalIntercept parameter + verticalIntercept parameter := by
  have denominator_positive : 0 < 1 + parameter := by linarith
  have numerator_nonnegative : 0 ≤ parameter ^ 2 * (3 - parameter) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have identity : horizontalIntercept parameter + verticalIntercept parameter - 3 / 2 =
      parameter ^ 2 * (3 - parameter) / (2 * (1 + parameter)) := by
    dsimp [horizontalIntercept, verticalIntercept]
    field_simp
    ring
  have nonnegative := div_nonneg numerator_nonnegative (by positivity : 0 ≤ 2 * (1 + parameter))
  linarith

theorem final_intercept_gap : 5 / 3 - (9 / 10 : ℝ) < 2 * Real.sqrt 2 - 2 := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

noncomputable def contactFrame (parameter : ℝ) : Frame where
  cosine := (1 - parameter ^ 2) / (1 + parameter ^ 2)
  sine := 2 * parameter / (1 + parameter ^ 2)
  unit := by
    have denominator_positive : 0 < 1 + parameter ^ 2 := by positivity
    field_simp
    ring

noncomputable def contactSquare (parameter : ℝ) : PlacedSquare where
  center := ⟨(2 * parameter ^ 3 - parameter ^ 2 + 1) / (2 * (1 + parameter ^ 2)),
    (1 + 2 * parameter - parameter ^ 2) / (2 * (1 + parameter ^ 2))⟩
  frame := contactFrame parameter

theorem contactSquare_bottom_vertex (parameter : ℝ) :
    ((contactSquare parameter).point (-1 / 2) (-1 / 2)).y = 0 := by
  have denominator_positive : 0 < 1 + parameter ^ 2 := by positivity
  dsimp [contactSquare, contactFrame, PlacedSquare.point, Frame.place]
  field_simp
  ring

theorem contactSquare_anchor_coordinates (parameter : ℝ) :
    (contactSquare parameter).localX ⟨0, 1⟩ = (2 * parameter - 1) / 2 ∧
      (contactSquare parameter).localY ⟨0, 1⟩ = 1 / 2 := by
  have denominator_positive : 0 < 1 + parameter ^ 2 := by positivity
  constructor <;>
    dsimp [contactSquare, contactFrame, PlacedSquare.localX, PlacedSquare.localY] <;>
    field_simp <;> ring

theorem contactSquare_horizontal_intercept_coordinates {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) :
    (contactSquare parameter).localX ⟨horizontalIntercept parameter, 1⟩ = 1 / 2 ∧
      (contactSquare parameter).localY ⟨horizontalIntercept parameter, 1⟩ =
        (1 - 3 * parameter) / (2 * (1 + parameter)) := by
  have denominator_positive : 0 < 1 + parameter ^ 2 := by positivity
  have linear_denominator_positive : 0 < 1 + parameter := by linarith
  constructor <;>
    dsimp [contactSquare, contactFrame, horizontalIntercept,
      PlacedSquare.localX, PlacedSquare.localY] <;>
    field_simp <;> ring

theorem contactSquare_vertical_intercept_coordinates (parameter : ℝ) :
    (contactSquare parameter).localX ⟨1, verticalIntercept parameter⟩ = 1 / 2 ∧
      (contactSquare parameter).localY ⟨1, verticalIntercept parameter⟩ =
        parameter * (parameter - 2) / 2 := by
  have denominator_positive : 0 < 1 + parameter ^ 2 := by positivity
  constructor <;>
    dsimp [contactSquare, contactFrame, verticalIntercept,
      PlacedSquare.localX, PlacedSquare.localY] <;>
    field_simp <;> ring

theorem contactSquare_contains_anchor {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most_one : parameter ≤ 1) :
    (contactSquare parameter).Contains ⟨0, 1⟩ := by
  rw [PlacedSquare.contains_iff_localCoordinates,
    (contactSquare_anchor_coordinates parameter).1,
    (contactSquare_anchor_coordinates parameter).2]
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem contactSquare_contains_horizontal_intercept {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most_one : parameter ≤ 1) :
    (contactSquare parameter).Contains ⟨horizontalIntercept parameter, 1⟩ := by
  rw [PlacedSquare.contains_iff_localCoordinates,
    (contactSquare_horizontal_intercept_coordinates parameter_nonnegative).1,
    (contactSquare_horizontal_intercept_coordinates parameter_nonnegative).2]
  have denominator_positive : 0 < 2 * (1 + parameter) := by linarith
  constructor
  · norm_num
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ denominator_positive]
      linarith
    · rw [div_le_iff₀ denominator_positive]
      linarith

theorem contactSquare_contains_vertical_intercept {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most_one : parameter ≤ 1) :
    (contactSquare parameter).Contains ⟨1, verticalIntercept parameter⟩ := by
  rw [PlacedSquare.contains_iff_localCoordinates,
    (contactSquare_vertical_intercept_coordinates parameter).1,
    (contactSquare_vertical_intercept_coordinates parameter).2]
  constructor
  · norm_num
  · rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (parameter - 1)]
    · nlinarith [mul_nonneg parameter_nonnegative (sub_nonneg.mpr parameter_at_most_one)]

theorem three_contacts_determine_frame {square : PlacedSquare}
    (cosine_positive : 0 < square.frame.cosine)
    (upper_left : square.localY ⟨1, 2⟩ = 1 / 2)
    (lower_right : square.localY ⟨2, 3 / 2⟩ = -1 / 2) :
    square.frame.cosine = 4 / 5 ∧ square.frame.sine = 3 / 5 := by
  have component_relation : square.frame.sine + square.frame.cosine / 2 = 1 := by
    dsimp [PlacedSquare.localY] at upper_left lower_right
    linarith
  have factored : square.frame.cosine * (5 * square.frame.cosine - 4) = 0 := by
    nlinarith [square.frame.unit]
  have cosine_eq : square.frame.cosine = 4 / 5 := by
    have := (mul_eq_zero.mp factored).resolve_left cosine_positive.ne'
    linarith
  exact ⟨cosine_eq, by linarith⟩

theorem three_contacts_left_intercept {square : PlacedSquare}
    (cosine_positive : 0 < square.frame.cosine)
    (upper_left : square.localY ⟨1, 2⟩ = 1 / 2)
    (upper_right : square.localX ⟨2, 2⟩ = 1 / 2)
    (lower_right : square.localY ⟨2, 3 / 2⟩ = -1 / 2) :
    square.localX ⟨1, 5 / 3⟩ = -1 / 2 ∧ square.Contains ⟨1, 5 / 3⟩ := by
  obtain ⟨cosine_eq, sine_eq⟩ := three_contacts_determine_frame cosine_positive upper_left lower_right
  have center_eq : square.center.x = 77 / 50 ∧ square.center.y = 89 / 50 := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at upper_left upper_right
    rw [cosine_eq, sine_eq] at upper_left upper_right
    constructor <;> linarith
  constructor
  · norm_num [PlacedSquare.localX, cosine_eq, sine_eq, center_eq.1, center_eq.2]
  · rw [PlacedSquare.contains_iff_localCoordinates]
    norm_num [PlacedSquare.localX, PlacedSquare.localY, cosine_eq, sine_eq, center_eq.1, center_eq.2]

end SquarePackingArchive.Records.Square6
