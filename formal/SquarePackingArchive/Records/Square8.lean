import SquarePackingArchive.Friedman
import SquarePackingArchive.Records.NearSquare

namespace SquarePackingArchive.Records.Square8

noncomputable def points : Fin 7 → Point := ![
  ⟨9 / 10, 1⟩,
  ⟨3 / 2, 1⟩,
  ⟨21 / 10, 1⟩,
  ⟨3 / 2, 3 / 2⟩,
  ⟨9 / 10, 2⟩,
  ⟨3 / 2, 2⟩,
  ⟨21 / 10, 2⟩
]

@[simp] lemma points_zero : points 0 = ⟨9 / 10, 1⟩ := by rfl

@[simp] lemma points_one : points 1 = ⟨3 / 2, 1⟩ := by rfl

@[simp] lemma points_two : points 2 = ⟨21 / 10, 1⟩ := by rfl

@[simp] lemma points_three : points 3 = ⟨3 / 2, 3 / 2⟩ := by rfl

@[simp] lemma points_four : points 4 = ⟨9 / 10, 2⟩ := by rfl

@[simp] lemma points_five : points 5 = ⟨3 / 2, 2⟩ := by rfl

@[simp] lemma points_six : points 6 = ⟨21 / 10, 2⟩ := by rfl

lemma bottom_row_weight_bound
    (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    1 + 3 / 5 * (frame.cosine * frame.sine) ≤
      frame.cosine + frame.sine := by
  exact frame.height_add_gap_product_le_sum_of_gap_le_three_quarters
    cosine_nonnegative sine_nonnegative (by norm_num) (by norm_num)

lemma side_row_weight_bound
    (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    9 / 10 + 1 * (frame.cosine * frame.sine) ≤
      frame.cosine + frame.sine := by
  have component_sum_nonnegative :
      0 ≤ frame.cosine + frame.sine := by linarith
  have component_sum_at_least_one :
      1 ≤ frame.cosine + frame.sine := by
    nlinarith [frame.unit]
  have component_sum_sq_upper :
      (frame.cosine + frame.sine) ^ 2 ≤ 2 := by
    nlinarith [frame.unit, sq_nonneg (frame.cosine - frame.sine)]
  have component_sum_upper :
      frame.cosine + frame.sine ≤ 10 / 7 := by
    nlinarith
  let delta := frame.cosine + frame.sine - 1
  have delta_nonnegative : 0 ≤ delta := by
    dsimp [delta]
    linarith
  have delta_upper : delta ≤ 3 / 7 := by
    dsimp [delta]
    linarith
  have delta_product_nonnegative : 0 ≤ delta * (3 / 7 - delta) :=
    mul_nonneg delta_nonnegative (sub_nonneg.mpr delta_upper)
  have delta_sq_upper : delta ^ 2 ≤ 1 / 5 := by
    dsimp [delta] at *
    nlinarith
  nlinarith [frame.unit]

lemma contains_bottomLeftCorner
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_upper : square.center.x ≤ 9 / 10)
    (center_y_upper : square.center.y ≤ 1) :
    square.Contains (points 0) := by
  simpa using square.contains_cornerPoint fits (by norm_num) (by norm_num)
    center_x_upper center_y_upper

lemma contains_bottomRightCorner
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 21 / 10 ≤ square.center.x)
    (center_y_upper : square.center.y ≤ 1) :
    square.Contains (points 2) := by
  have reflected_mem :
      (square.reflectX 3).Contains ⟨9 / 10, 1⟩ :=
    (square.reflectX 3).contains_cornerPoint
    (targetX := 9 / 10) (targetY := 1)
    ((square.reflectX_fits_iff 3).2 fits) (by norm_num) (by norm_num)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
  exact (square.reflectX_contains_iff 3 (points 2)).1 (by
    have point_identity : (points 2).reflectX 3 = ⟨9 / 10, 1⟩ := by
      rw [points_two]
      norm_num [Point.reflectX]
    rw [point_identity]
    exact reflected_mem)

lemma contains_topLeftCorner
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_upper : square.center.x ≤ 9 / 10)
    (center_y_lower : 2 ≤ square.center.y) :
    square.Contains (points 4) := by
  have reflected_mem :
      (square.reflectY 3).Contains ⟨9 / 10, 1⟩ :=
    (square.reflectY 3).contains_cornerPoint
    (targetX := 9 / 10) (targetY := 1)
    ((square.reflectY_fits_iff 3).2 fits) (by norm_num) (by norm_num)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  exact (square.reflectY_contains_iff 3 (points 4)).1 (by
    have point_identity : (points 4).reflectY 3 = ⟨9 / 10, 1⟩ := by
      rw [points_four]
      norm_num [Point.reflectY]
    rw [point_identity]
    exact reflected_mem)

lemma contains_topRightCorner
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 21 / 10 ≤ square.center.x)
    (center_y_lower : 2 ≤ square.center.y) :
    square.Contains (points 6) := by
  have reflected_mem := contains_topLeftCorner
    (square := square.reflectX 3) ((square.reflectX_fits_iff 3).2 fits)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
  exact (square.reflectX_contains_iff 3 (points 6)).1 (by
    have point_identity : (points 6).reflectX 3 = points 4 := by
      rw [points_six, points_four]
      norm_num [Point.reflectX]
    rw [point_identity]
    exact reflected_mem)

lemma contains_bottomLeftPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 9 / 10 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 3 / 2)
    (center_y_upper : square.center.y ≤ 1) :
    square.Contains (points 0) ∨ square.Contains (points 1) := by
  have result := square.contains_bottomPairWith fits (by norm_num) (by norm_num)
    (by norm_num) bottom_row_weight_bound center_x_lower (by norm_num at *; assumption)
    center_y_upper
  rcases result with left_mem | right_mem
  · exact Or.inl (by simpa only [points_zero] using left_mem)
  · exact Or.inr (by
      rw [points_one]
      convert right_mem using 1; norm_num)

lemma contains_bottomRightPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 3 / 2 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 21 / 10)
    (center_y_upper : square.center.y ≤ 1) :
    square.Contains (points 1) ∨ square.Contains (points 2) := by
  have result := square.contains_bottomPairWith fits (by norm_num) (by norm_num)
    (by norm_num) bottom_row_weight_bound center_x_lower (by norm_num at *; assumption)
    center_y_upper
  rcases result with left_mem | right_mem
  · exact Or.inl (by simpa only [points_one] using left_mem)
  · exact Or.inr (by
      rw [points_two]
      convert right_mem using 1; norm_num)

lemma contains_leftPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_upper : square.center.x ≤ 9 / 10)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 2) :
    square.Contains (points 0) ∨ square.Contains (points 4) := by
  have swapped_result := square.swap.contains_bottomPairWith
    (left := 1) (targetHeight := 9 / 10) (gap := 1)
    ((square.swap_fits_iff 3).2 fits) (by norm_num) (by norm_num)
    (by norm_num) side_row_weight_bound
    (by simpa [PlacedSquare.swap, Point.swap] using center_y_lower)
    (by norm_num; exact center_y_upper)
    (by simpa [PlacedSquare.swap, Point.swap] using center_x_upper)
  rcases swapped_result with bottom_mem | top_mem
  · exact Or.inl ((square.swap_contains_iff (points 0)).1 (by
      simpa only [points_zero, Point.swap] using bottom_mem))
  · exact Or.inr ((square.swap_contains_iff (points 4)).1 (by
      have point_identity : (points 4).swap = ⟨2, 9 / 10⟩ := by
        rw [points_four]
        rfl
      rw [point_identity]
      convert top_mem using 1; norm_num))

lemma contains_topLeftPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 9 / 10 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 3 / 2)
    (center_y_lower : 2 ≤ square.center.y) :
    square.Contains (points 4) ∨ square.Contains (points 5) := by
  have reflected_result := contains_bottomLeftPair
    (square := square.reflectY 3) ((square.reflectY_fits_iff 3).2 fits)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_lower)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  rcases reflected_result with left_mem | right_mem
  · exact Or.inl ((square.reflectY_contains_iff 3 (points 4)).1 (by
      have point_identity : (points 4).reflectY 3 = points 0 := by
        rw [points_four, points_zero]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact left_mem))
  · exact Or.inr ((square.reflectY_contains_iff 3 (points 5)).1 (by
      have point_identity : (points 5).reflectY 3 = points 1 := by
        rw [points_five, points_one]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact right_mem))

lemma contains_topRightPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 3 / 2 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 21 / 10)
    (center_y_lower : 2 ≤ square.center.y) :
    square.Contains (points 5) ∨ square.Contains (points 6) := by
  have reflected_result := contains_bottomRightPair
    (square := square.reflectY 3) ((square.reflectY_fits_iff 3).2 fits)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_lower)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  rcases reflected_result with left_mem | right_mem
  · exact Or.inl ((square.reflectY_contains_iff 3 (points 5)).1 (by
      have point_identity : (points 5).reflectY 3 = points 1 := by
        rw [points_five, points_one]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact left_mem))
  · exact Or.inr ((square.reflectY_contains_iff 3 (points 6)).1 (by
      have point_identity : (points 6).reflectY 3 = points 2 := by
        rw [points_six, points_two]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact right_mem))

lemma contains_rightPair
    {square : PlacedSquare} (fits : square.Fits 3)
    (center_x_lower : 21 / 10 ≤ square.center.x)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 2) :
    square.Contains (points 2) ∨ square.Contains (points 6) := by
  have reflected_result := contains_leftPair
    (square := square.reflectX 3) ((square.reflectX_fits_iff 3).2 fits)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
  rcases reflected_result with bottom_mem | top_mem
  · exact Or.inl ((square.reflectX_contains_iff 3 (points 2)).1 (by
      have point_identity : (points 2).reflectX 3 = points 0 := by
        rw [points_two, points_zero]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact bottom_mem))
  · exact Or.inr ((square.reflectX_contains_iff 3 (points 6)).1 (by
      have point_identity : (points 6).reflectX 3 = points 4 := by
        rw [points_six, points_four]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact top_mem))

lemma contains_bottomLeftTriangle
    {square : PlacedSquare}
    (center_x_upper : square.center.x ≤ 3 / 2)
    (center_y_lower : 1 ≤ square.center.y)
    (center_below_diagonal :
      12 * square.center.y ≤ 10 * square.center.x + 3) :
    square.Contains (points 0) ∨ square.Contains (points 1) ∨
      square.Contains (points 3) := by
  let firstWeight := 5 / 3 * (3 / 2 - square.center.x)
  let thirdWeight := 2 * (square.center.y - 1)
  let secondWeight := 1 - firstWeight - thirdWeight
  have first_weight_nonnegative : 0 ≤ firstWeight := by
    dsimp [firstWeight]
    positivity
  have third_weight_nonnegative : 0 ≤ thirdWeight := by
    dsimp [thirdWeight]
    linarith
  have second_weight_nonnegative : 0 ≤ secondWeight := by
    dsimp [secondWeight, firstWeight, thirdWeight]
    linarith
  apply square.contains_triangleVertex (points 0) (points 1) (points 3)
    firstWeight secondWeight thirdWeight first_weight_nonnegative
    second_weight_nonnegative third_weight_nonnegative
  · dsimp [secondWeight]
    ring
  · rw [points_zero, points_one, points_three]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_zero, points_one, points_three]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_zero, points_one]
    norm_num
  · rw [points_zero, points_three]
    norm_num
  · rw [points_one, points_three]
    norm_num

lemma contains_leftTriangle
    {square : PlacedSquare}
    (_center_x_lower : 9 / 10 ≤ square.center.x)
    (center_below_upper_diagonal :
      12 * square.center.y + 10 * square.center.x ≤ 33)
    (center_above_lower_diagonal :
      10 * square.center.x + 3 ≤ 12 * square.center.y) :
    square.Contains (points 0) ∨ square.Contains (points 4) ∨
      square.Contains (points 3) := by
  let thirdWeight := 5 / 3 * (square.center.x - 9 / 10)
  let secondWeight := square.center.y - 1 - thirdWeight / 2
  let firstWeight := 1 - secondWeight - thirdWeight
  have first_weight_nonnegative : 0 ≤ firstWeight := by
    dsimp [firstWeight, secondWeight, thirdWeight]
    linarith
  have second_weight_nonnegative : 0 ≤ secondWeight := by
    dsimp [secondWeight, thirdWeight]
    linarith
  have third_weight_nonnegative : 0 ≤ thirdWeight := by
    dsimp [thirdWeight]
    nlinarith [_center_x_lower]
  apply square.contains_triangleVertex (points 0) (points 4) (points 3)
    firstWeight secondWeight thirdWeight first_weight_nonnegative
    second_weight_nonnegative third_weight_nonnegative
  · dsimp [firstWeight]
    ring
  · rw [points_zero, points_four, points_three]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_zero, points_four, points_three]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_zero, points_four]
    norm_num
  · rw [points_zero, points_three]
    norm_num
  · rw [points_four, points_three]
    norm_num

lemma contains_bottomRightTriangle
    {square : PlacedSquare}
    (center_x_lower : 3 / 2 ≤ square.center.x)
    (center_y_lower : 1 ≤ square.center.y)
    (center_below_diagonal :
      12 * square.center.y + 10 * square.center.x ≤ 33) :
    square.Contains (points 2) ∨ square.Contains (points 1) ∨
      square.Contains (points 3) := by
  have reflected_result := contains_bottomLeftTriangle
    (square := square.reflectX 3)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
  rcases reflected_result with left_mem | middle_mem | center_mem
  · exact Or.inl ((square.reflectX_contains_iff 3 (points 2)).1 (by
      have point_identity : (points 2).reflectX 3 = points 0 := by
        rw [points_two, points_zero]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact left_mem))
  · exact Or.inr (Or.inl ((square.reflectX_contains_iff 3 (points 1)).1 (by
      have point_identity : (points 1).reflectX 3 = points 1 := by
        rw [points_one]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact middle_mem)))
  · exact Or.inr (Or.inr ((square.reflectX_contains_iff 3 (points 3)).1 (by
      have point_identity : (points 3).reflectX 3 = points 3 := by
        rw [points_three]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact center_mem)))

lemma contains_topLeftTriangle
    {square : PlacedSquare}
    (center_x_upper : square.center.x ≤ 3 / 2)
    (center_y_upper : square.center.y ≤ 2)
    (center_above_diagonal :
      33 ≤ 12 * square.center.y + 10 * square.center.x) :
    square.Contains (points 4) ∨ square.Contains (points 5) ∨
      square.Contains (points 3) := by
  have reflected_result := contains_bottomLeftTriangle
    (square := square.reflectY 3)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  rcases reflected_result with left_mem | middle_mem | center_mem
  · exact Or.inl ((square.reflectY_contains_iff 3 (points 4)).1 (by
      have point_identity : (points 4).reflectY 3 = points 0 := by
        rw [points_four, points_zero]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact left_mem))
  · exact Or.inr (Or.inl ((square.reflectY_contains_iff 3 (points 5)).1 (by
      have point_identity : (points 5).reflectY 3 = points 1 := by
        rw [points_five, points_one]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact middle_mem)))
  · exact Or.inr (Or.inr ((square.reflectY_contains_iff 3 (points 3)).1 (by
      have point_identity : (points 3).reflectY 3 = points 3 := by
        rw [points_three]
        norm_num [Point.reflectY]
      rw [point_identity]
      exact center_mem)))

lemma contains_topRightTriangle
    {square : PlacedSquare}
    (center_x_lower : 3 / 2 ≤ square.center.x)
    (center_y_upper : square.center.y ≤ 2)
    (center_above_diagonal :
      10 * square.center.x + 3 ≤ 12 * square.center.y) :
    square.Contains (points 6) ∨ square.Contains (points 5) ∨
      square.Contains (points 3) := by
  have reflected_result := contains_topLeftTriangle
    (square := square.reflectX 3)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
  rcases reflected_result with left_mem | middle_mem | center_mem
  · exact Or.inl ((square.reflectX_contains_iff 3 (points 6)).1 (by
      have point_identity : (points 6).reflectX 3 = points 4 := by
        rw [points_six, points_four]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact left_mem))
  · exact Or.inr (Or.inl ((square.reflectX_contains_iff 3 (points 5)).1 (by
      have point_identity : (points 5).reflectX 3 = points 5 := by
        rw [points_five]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact middle_mem)))
  · exact Or.inr (Or.inr ((square.reflectX_contains_iff 3 (points 3)).1 (by
      have point_identity : (points 3).reflectX 3 = points 3 := by
        rw [points_three]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact center_mem)))

lemma contains_rightTriangle
    {square : PlacedSquare}
    (center_x_upper : square.center.x ≤ 21 / 10)
    (center_below_upper_diagonal :
      12 * square.center.y ≤ 10 * square.center.x + 3)
    (center_above_lower_diagonal :
      33 ≤ 12 * square.center.y + 10 * square.center.x) :
    square.Contains (points 2) ∨ square.Contains (points 6) ∨
      square.Contains (points 3) := by
  have reflected_result := contains_leftTriangle
    (square := square.reflectX 3)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
  rcases reflected_result with bottom_mem | top_mem | center_mem
  · exact Or.inl ((square.reflectX_contains_iff 3 (points 2)).1 (by
      have point_identity : (points 2).reflectX 3 = points 0 := by
        rw [points_two, points_zero]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact bottom_mem))
  · exact Or.inr (Or.inl ((square.reflectX_contains_iff 3 (points 6)).1 (by
      have point_identity : (points 6).reflectX 3 = points 4 := by
        rw [points_six, points_four]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact top_mem)))
  · exact Or.inr (Or.inr ((square.reflectX_contains_iff 3 (points 3)).1 (by
      have point_identity : (points 3).reflectX 3 = points 3 := by
        rw [points_three]
        norm_num [Point.reflectX]
      rw [point_identity]
      exact center_mem)))

theorem points_unavoidable : Unavoidable points 3 := by
  intro square fits
  have center_mem : square.Contains square.center := by
    rw [square.contains_iff_localCoordinates]
    simp [PlacedSquare.localX, PlacedSquare.localY]
  have center_bounds := fits center_mem
  rcases center_bounds with ⟨center_x_nonnegative, center_x_upper,
    center_y_nonnegative, center_y_upper⟩
  by_cases center_x_left : square.center.x ≤ 9 / 10
  · by_cases center_y_bottom : square.center.y ≤ 1
    · exact ⟨0, contains_bottomLeftCorner fits center_x_left center_y_bottom⟩
    · by_cases center_y_top : 2 ≤ square.center.y
      · exact ⟨4, contains_topLeftCorner fits center_x_left center_y_top⟩
      · rcases contains_leftPair fits center_x_left (by linarith) (by linarith) with
          bottom_mem | top_mem
        · exact ⟨0, bottom_mem⟩
        · exact ⟨4, top_mem⟩
  · by_cases center_x_right : 21 / 10 ≤ square.center.x
    · by_cases center_y_bottom : square.center.y ≤ 1
      · exact ⟨2, contains_bottomRightCorner fits center_x_right center_y_bottom⟩
      · by_cases center_y_top : 2 ≤ square.center.y
        · exact ⟨6, contains_topRightCorner fits center_x_right center_y_top⟩
        · rcases contains_rightPair fits center_x_right (by linarith) (by linarith) with
            bottom_mem | top_mem
          · exact ⟨2, bottom_mem⟩
          · exact ⟨6, top_mem⟩
    · by_cases center_y_bottom : square.center.y ≤ 1
      · by_cases center_x_middle : square.center.x ≤ 3 / 2
        · rcases contains_bottomLeftPair fits (by linarith) center_x_middle
            center_y_bottom with left_mem | right_mem
          · exact ⟨0, left_mem⟩
          · exact ⟨1, right_mem⟩
        · rcases contains_bottomRightPair fits (by linarith) (by linarith)
            center_y_bottom with left_mem | right_mem
          · exact ⟨1, left_mem⟩
          · exact ⟨2, right_mem⟩
      · by_cases center_y_top : 2 ≤ square.center.y
        · by_cases center_x_middle : square.center.x ≤ 3 / 2
          · rcases contains_topLeftPair fits (by linarith) center_x_middle
              center_y_top with left_mem | right_mem
            · exact ⟨4, left_mem⟩
            · exact ⟨5, right_mem⟩
          · rcases contains_topRightPair fits (by linarith) (by linarith)
              center_y_top with left_mem | right_mem
            · exact ⟨5, left_mem⟩
            · exact ⟨6, right_mem⟩
        · by_cases center_x_middle : square.center.x ≤ 3 / 2
          · by_cases center_below_diagonal :
                12 * square.center.y ≤ 10 * square.center.x + 3
            · rcases contains_bottomLeftTriangle center_x_middle
                (by linarith) center_below_diagonal with
                left_mem | right_mem | center_mem
              · exact ⟨0, left_mem⟩
              · exact ⟨1, right_mem⟩
              · exact ⟨3, center_mem⟩
            · by_cases center_above_diagonal :
                  33 ≤ 12 * square.center.y + 10 * square.center.x
              · rcases contains_topLeftTriangle center_x_middle
                  (by linarith) center_above_diagonal with
                  left_mem | right_mem | center_mem
                · exact ⟨4, left_mem⟩
                · exact ⟨5, right_mem⟩
                · exact ⟨3, center_mem⟩
              · rcases contains_leftTriangle (square := square) (by linarith) (by linarith)
                  (by linarith) with bottom_mem | top_mem | center_mem
                · exact ⟨0, bottom_mem⟩
                · exact ⟨4, top_mem⟩
                · exact ⟨3, center_mem⟩
          · by_cases center_below_diagonal :
                12 * square.center.y + 10 * square.center.x ≤ 33
            · rcases contains_bottomRightTriangle (by linarith)
                (by linarith) center_below_diagonal with
                right_mem | left_mem | center_mem
              · exact ⟨2, right_mem⟩
              · exact ⟨1, left_mem⟩
              · exact ⟨3, center_mem⟩
            · by_cases center_above_diagonal :
                  10 * square.center.x + 3 ≤ 12 * square.center.y
              · rcases contains_topRightTriangle (by linarith)
                  (by linarith) center_above_diagonal with
                  right_mem | left_mem | center_mem
                · exact ⟨6, right_mem⟩
                · exact ⟨5, left_mem⟩
                · exact ⟨3, center_mem⟩
              · rcases contains_rightTriangle (square := square) (by linarith) (by linarith)
                  (by linarith) with bottom_mem | top_mem | center_mem
                · exact ⟨2, bottom_mem⟩
                · exact ⟨6, top_mem⟩
                · exact ⟨3, center_mem⟩

theorem s8_lower_bound : IsLowerBound 8 3 := by
  simpa using lowerBound_succ_of_unavoidable points_unavoidable

theorem s8_eq_three : IsMinimumSide 8 3 := by
  exact ⟨by simpa using NearSquare.squareMinusOne_hasPacking 3, s8_lower_bound⟩

end SquarePackingArchive.Records.Square8
