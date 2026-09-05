import SquarePackingArchive.BentzRectangleChords

namespace SquarePackingArchive.Bentz

theorem below_left_point_forces_bottom_corner_nonnegative_frame
    (square : PlacedSquare) {left bottom vertical : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine) (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_above : bottom ≤ square.center.y) (point_below : vertical ≤ bottom)
    (inside : square.Contains ⟨left, vertical⟩) :
    square.Contains ⟨left, bottom⟩ ∨ square.Contains ⟨left + 1, bottom⟩ := by
  have cosine_upper : square.frame.cosine ≤ 1 := by nlinarith [square.frame.unit]
  have sine_upper : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit]
  have inside_bounds := (square.contains_iff_localCoordinates _).1 inside
  rw [abs_le, abs_le] at inside_bounds
  have cosine_vertical := mul_nonneg cosine_nonnegative (sub_nonneg.mpr point_below)
  have sine_vertical := mul_nonneg sine_nonnegative (sub_nonneg.mpr point_below)
  have cosine_horizontal := mul_nonneg cosine_nonnegative (sub_nonneg.mpr center_left)
  have sine_center := mul_nonneg sine_nonnegative (sub_nonneg.mpr center_above)
  have left_horizontal : |square.localX ⟨left, bottom⟩| ≤ 1 / 2 := by
    rw [abs_le]
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at inside_bounds ⊢
    constructor <;> nlinarith
  have left_vertical_lower : -(1 / 2) ≤ square.localY ⟨left, bottom⟩ := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY] at inside_bounds ⊢
    nlinarith
  by_cases left_inside : square.Contains ⟨left, bottom⟩
  · exact Or.inl left_inside
  have left_vertical_upper : 1 / 2 < square.localY ⟨left, bottom⟩ := by
    by_contra! upper
    exact left_inside ((square.contains_iff_localCoordinates _).2
      ⟨left_horizontal, abs_le.mpr ⟨left_vertical_lower, upper⟩⟩)
  have cosine_center := mul_nonneg cosine_nonnegative (sub_nonneg.mpr center_above)
  have sine_horizontal_upper := mul_nonneg (sub_nonneg.mpr sine_upper) (sub_nonneg.mpr center_left)
  have center_right_half : left + 1 / 2 < square.center.x := by
    dsimp [PlacedSquare.localY] at left_vertical_upper
    nlinarith
  have right_horizontal_upper := mul_nonneg cosine_nonnegative
    (show 0 ≤ square.center.x - left - 1 / 2 by linarith)
  have right_vertical_upper := mul_nonneg sine_nonnegative (sub_nonneg.mpr center_right)
  apply Or.inr
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  rw [abs_le] at left_horizontal
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at left_horizontal left_vertical_upper ⊢
  constructor <;> constructor <;> nlinarith

theorem below_left_point_forces_bottom_corner
    (square : PlacedSquare) {left bottom vertical : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_above : bottom ≤ square.center.y) (point_below : vertical ≤ bottom)
    (inside : square.Contains ⟨left, vertical⟩) :
    square.Contains ⟨left, bottom⟩ ∨ square.Contains ⟨left + 1, bottom⟩ := by
  have result := below_left_point_forces_bottom_corner_nonnegative_frame square.firstQuadrant
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    (by simpa only [PlacedSquare.firstQuadrant_center] using center_left)
    (by simpa only [PlacedSquare.firstQuadrant_center] using center_right)
    (by simpa only [PlacedSquare.firstQuadrant_center] using center_above)
    point_below ((square.firstQuadrant_contains_iff _).2 inside)
  simpa only [PlacedSquare.firstQuadrant_contains_iff] using result

theorem left_section_inside_rectangle
    (square : PlacedSquare) {left bottom height vertical : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩)
    (inside : square.Contains ⟨left, vertical⟩) : bottom < vertical ∧ vertical < bottom + height := by
  constructor
  · by_contra! below
    rcases below_left_point_forces_bottom_corner square center_left center_right center_bottom below inside with
      left_inside | right_inside
    · exact corners_missing 0 0 (by simpa using left_inside)
    · exact corners_missing 1 0 (by simpa using right_inside)
  · by_contra! above
    have reflected := below_left_point_forces_bottom_corner (square.reflectY (2 * bottom + height))
      (left := left) (bottom := bottom) (vertical := 2 * bottom + height - vertical)
      center_left center_right (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      (by linarith) ((square.reflectY_contains_iff (2 * bottom + height) _).2 inside)
    rcases reflected with left_inside | right_inside
    · apply corners_missing 0 1
      apply (square.reflectY_contains_iff (2 * bottom + height) _).1
      convert left_inside using 1
      norm_num [Point.reflectY]
      ring
    · apply corners_missing 1 1
      apply (square.reflectY_contains_iff (2 * bottom + height) _).1
      convert right_inside using 1
      norm_num [Point.reflectY]
      ring

theorem right_section_inside_rectangle
    (square : PlacedSquare) {left bottom height vertical : ℝ}
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩)
    (inside : square.Contains ⟨left + 1, vertical⟩) : bottom < vertical ∧ vertical < bottom + height := by
  apply left_section_inside_rectangle (square.reflectX (2 * left + 1))
    (left := left) (bottom := bottom) (height := height)
    (by dsimp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by dsimp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    center_bottom center_top
  · intro column row reflected_inside
    apply corners_missing column.rev row
    apply (square.reflectX_contains_iff (2 * left + 1) _).1
    convert reflected_inside using 1
    fin_cases column <;> norm_num [Point.reflectX] <;> ring
  · apply (square.reflectX_contains_iff (2 * left + 1) ⟨left + 1, vertical⟩).2 at inside
    convert inside using 1
    dsimp [Point.reflectX]
    congr 1
    ring

theorem vertical_chord_closed_of_open
    (square : PlacedSquare) {line lower upper : ℝ} (positive : lower < upper)
    (inside : ∀ vertical ∈ Set.Ioo lower upper, square.Contains ⟨line, vertical⟩) :
    ∀ vertical ∈ Set.Icc lower upper, square.Contains ⟨line, vertical⟩ := by
  have section_closed : IsClosed {vertical : ℝ | square.Contains ⟨line, vertical⟩} := by
    simp only [PlacedSquare.contains_iff_localCoordinates]
    have horizontal_closed : IsClosed {vertical : ℝ | |square.localX ⟨line, vertical⟩| ≤ 1 / 2} :=
      isClosed_le (by dsimp [PlacedSquare.localX]; fun_prop) continuous_const
    have vertical_closed : IsClosed {vertical : ℝ | |square.localY ⟨line, vertical⟩| ≤ 1 / 2} :=
      isClosed_le (by dsimp [PlacedSquare.localY]; fun_prop) continuous_const
    exact horizontal_closed.inter vertical_closed
  have closure_inside := section_closed.closure_subset_iff.mpr inside
  rwa [closure_Ioo positive.ne] at closure_inside

theorem rectangle_vertical_chords
    (square : PlacedSquare) {left bottom height : ℝ}
    (height_positive : 0 < height) (height_upper : height < 2 * Real.sqrt 2 - 2)
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩) :
    ∃ firstLower firstUpper secondLower secondUpper : ℝ,
      bottom < firstLower ∧ firstLower < firstUpper ∧ firstUpper < bottom + height ∧
      bottom < secondLower ∧ secondLower < secondUpper ∧ secondUpper < bottom + height ∧
      2 * Real.sqrt 2 - 2 ≤ (firstUpper - firstLower) + (secondUpper - secondLower) ∧
      2 * Real.sqrt 2 - 2 - height < firstUpper - firstLower ∧
      2 * Real.sqrt 2 - 2 - height < secondUpper - secondLower ∧
      (∀ vertical ∈ Set.Icc firstLower firstUpper, square.Contains ⟨left, vertical⟩) ∧
      (∀ vertical ∈ Set.Icc secondLower secondUpper, square.Contains ⟨left + 1, vertical⟩) := by
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_nonnegative, second_nonnegative,
      total_bound, first_inside, second_inside⟩ := vertical_two_line_chords square
    center_left center_right (show left + 1 - left ≤ 1 by linarith)
  have root_upper : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have total_bound' : 2 * Real.sqrt 2 - 2 ≤ (firstUpper - firstLower) + (secondUpper - secondLower) := by
    convert total_bound using 1
    rw [show left + 1 - left = (1 : ℝ) by ring, min_eq_right (by linarith)]
    ring
  have first_within : Set.Ioo firstLower firstUpper ⊆ Set.Ioo bottom (bottom + height) :=
    fun _ member => left_section_inside_rectangle square center_left center_right center_bottom center_top
      corners_missing (first_inside _ member)
  have second_within : Set.Ioo secondLower secondUpper ⊆ Set.Ioo bottom (bottom + height) :=
    fun _ member => right_section_inside_rectangle square center_left center_right center_bottom center_top
      corners_missing (second_inside _ member)
  have interval_length_bound {lower upper : ℝ} (nonnegative : 0 ≤ upper - lower)
      (within : Set.Ioo lower upper ⊆ Set.Ioo bottom (bottom + height)) : upper - lower ≤ height := by
    by_cases positive : lower < upper
    · have bounds := (Set.Ioo_subset_Ioo_iff positive).1 within
      linarith
    · linarith
  have first_length_upper := interval_length_bound first_nonnegative first_within
  have second_length_upper := interval_length_bound second_nonnegative second_within
  have first_positive : firstLower < firstUpper := by linarith
  have second_positive : secondLower < secondUpper := by linarith
  have first_closed := vertical_chord_closed_of_open square first_positive first_inside
  have second_closed := vertical_chord_closed_of_open square second_positive second_inside
  have first_lower_bounds := left_section_inside_rectangle square center_left center_right center_bottom center_top
    corners_missing (first_closed firstLower ⟨le_rfl, first_positive.le⟩)
  have first_upper_bounds := left_section_inside_rectangle square center_left center_right center_bottom center_top
    corners_missing (first_closed firstUpper ⟨first_positive.le, le_rfl⟩)
  have second_lower_bounds := right_section_inside_rectangle square center_left center_right center_bottom center_top
    corners_missing (second_closed secondLower ⟨le_rfl, second_positive.le⟩)
  have second_upper_bounds := right_section_inside_rectangle square center_left center_right center_bottom center_top
    corners_missing (second_closed secondUpper ⟨second_positive.le, le_rfl⟩)
  exact ⟨firstLower, firstUpper, secondLower, secondUpper,
    first_lower_bounds.1, first_positive, first_upper_bounds.2,
    second_lower_bounds.1, second_positive, second_upper_bounds.2,
    total_bound', by linarith, by linarith, first_closed, second_closed⟩

end SquarePackingArchive.Bentz
