import SquarePackingArchive.Friedman
import SquarePackingArchive.Rectangle
import SquarePackingArchive.Records.NearSquare

namespace SquarePackingArchive.Records.Square15

noncomputable def points : Fin 14 → Point := ![
  ⟨1, 1⟩,
  ⟨8 / 5, 1⟩,
  ⟨12 / 5, 1⟩,
  ⟨3, 1⟩,
  ⟨1, 9 / 5⟩,
  ⟨2, 9 / 5⟩,
  ⟨3, 9 / 5⟩,
  ⟨1, 11 / 5⟩,
  ⟨2, 11 / 5⟩,
  ⟨3, 11 / 5⟩,
  ⟨1, 3⟩,
  ⟨8 / 5, 3⟩,
  ⟨12 / 5, 3⟩,
  ⟨3, 3⟩
]

@[simp] lemma points_zero : points 0 = ⟨1, 1⟩ := by rfl
@[simp] lemma points_one : points 1 = ⟨8 / 5, 1⟩ := by rfl
@[simp] lemma points_two : points 2 = ⟨12 / 5, 1⟩ := by rfl
@[simp] lemma points_three : points 3 = ⟨3, 1⟩ := by rfl
@[simp] lemma points_four : points 4 = ⟨1, 9 / 5⟩ := by rfl
@[simp] lemma points_five : points 5 = ⟨2, 9 / 5⟩ := by rfl
@[simp] lemma points_six : points 6 = ⟨3, 9 / 5⟩ := by rfl
@[simp] lemma points_seven : points 7 = ⟨1, 11 / 5⟩ := by rfl
@[simp] lemma points_eight : points 8 = ⟨2, 11 / 5⟩ := by rfl
@[simp] lemma points_nine : points 9 = ⟨3, 11 / 5⟩ := by rfl
@[simp] lemma points_ten : points 10 = ⟨1, 3⟩ := by rfl
@[simp] lemma points_eleven : points 11 = ⟨8 / 5, 3⟩ := by rfl
@[simp] lemma points_twelve : points 12 = ⟨12 / 5, 3⟩ := by rfl
@[simp] lemma points_thirteen : points 13 = ⟨3, 3⟩ := by rfl

lemma contains_bottomFirstTriangle
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_y_lower : 1 ≤ square.center.y)
    (center_below_diagonal :
      20 * square.center.x + 15 * square.center.y ≤ 47) :
    square.Contains (points 0) ∨ square.Contains (points 1) ∨
      square.Contains (points 4) := by
  let secondWeight := 5 / 3 * (square.center.x - 1)
  let thirdWeight := 5 / 4 * (square.center.y - 1)
  let firstWeight := 1 - secondWeight - thirdWeight
  have first_weight_nonnegative : 0 ≤ firstWeight := by
    dsimp [firstWeight, secondWeight, thirdWeight]
    linarith
  have second_weight_nonnegative : 0 ≤ secondWeight := by
    dsimp [secondWeight]
    nlinarith [center_x_lower]
  have third_weight_nonnegative : 0 ≤ thirdWeight := by
    dsimp [thirdWeight]
    nlinarith [center_y_lower]
  apply square.contains_triangleVertex (points 0) (points 1) (points 4)
    firstWeight secondWeight thirdWeight first_weight_nonnegative
    second_weight_nonnegative third_weight_nonnegative
  · dsimp [firstWeight]
    ring
  · rw [points_zero, points_one, points_four]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_zero, points_one, points_four]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  all_goals norm_num

lemma contains_bottomSecondTriangle
    {square : PlacedSquare}
    (center_y_upper : square.center.y ≤ 9 / 5)
    (center_above_left_diagonal :
      47 ≤ 20 * square.center.x + 15 * square.center.y)
    (center_above_right_diagonal :
      10 * square.center.x - 11 ≤ 5 * square.center.y) :
    square.Contains (points 1) ∨ square.Contains (points 4) ∨
      square.Contains (points 5) := by
  let firstWeight := 5 / 4 * (9 / 5 - square.center.y)
  let thirdWeight := square.center.x - 1 - 3 / 5 * firstWeight
  let secondWeight := 1 - firstWeight - thirdWeight
  have first_weight_nonnegative : 0 ≤ firstWeight := by
    dsimp [firstWeight]
    nlinarith [center_y_upper]
  have second_weight_nonnegative : 0 ≤ secondWeight := by
    dsimp [secondWeight, firstWeight, thirdWeight]
    linarith
  have third_weight_nonnegative : 0 ≤ thirdWeight := by
    dsimp [thirdWeight, firstWeight]
    linarith
  apply square.contains_triangleVertex (points 1) (points 4) (points 5)
    firstWeight secondWeight thirdWeight first_weight_nonnegative
    second_weight_nonnegative third_weight_nonnegative
  · dsimp [secondWeight]
    ring
  · rw [points_one, points_four, points_five]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_one, points_four, points_five]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  all_goals norm_num

lemma contains_bottomMiddleTriangle
    {square : PlacedSquare}
    (center_y_lower : 1 ≤ square.center.y)
    (center_below_left_diagonal :
      5 * square.center.y ≤ 10 * square.center.x - 11)
    (center_below_right_diagonal :
      5 * square.center.y + 10 * square.center.x ≤ 29) :
    square.Contains (points 1) ∨ square.Contains (points 2) ∨
      square.Contains (points 5) := by
  let thirdWeight := 5 / 4 * (square.center.y - 1)
  let secondWeight := (1 - thirdWeight) / 2 + 5 / 4 * (square.center.x - 2)
  let firstWeight := 1 - secondWeight - thirdWeight
  have first_weight_nonnegative : 0 ≤ firstWeight := by
    dsimp [firstWeight, secondWeight, thirdWeight]
    linarith
  have second_weight_nonnegative : 0 ≤ secondWeight := by
    dsimp [secondWeight, thirdWeight]
    linarith
  have third_weight_nonnegative : 0 ≤ thirdWeight := by
    dsimp [thirdWeight]
    nlinarith [center_y_lower]
  apply square.contains_triangleVertex (points 1) (points 2) (points 5)
    firstWeight secondWeight thirdWeight first_weight_nonnegative
    second_weight_nonnegative third_weight_nonnegative
  · dsimp [firstWeight]
    ring
  · rw [points_one, points_two, points_five]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  · rw [points_one, points_two, points_five]
    dsimp [firstWeight, secondWeight, thirdWeight]
    ring
  all_goals norm_num

lemma contains_bottomLeftHalf
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 2)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 9 / 5) :
    square.Contains (points 0) ∨ square.Contains (points 1) ∨
      square.Contains (points 2) ∨ square.Contains (points 4) ∨
        square.Contains (points 5) := by
  by_cases center_x_first : square.center.x ≤ 8 / 5
  · by_cases center_below_diagonal :
        20 * square.center.x + 15 * square.center.y ≤ 47
    · rcases contains_bottomFirstTriangle center_x_lower center_y_lower
          center_below_diagonal with first_mem | second_mem | third_mem
      · exact Or.inl first_mem
      · exact Or.inr (Or.inl second_mem)
      · exact Or.inr (Or.inr (Or.inr (Or.inl third_mem)))
    · rcases contains_bottomSecondTriangle center_y_upper (by linarith)
          (by linarith) with first_mem | second_mem | third_mem
      · exact Or.inr (Or.inl first_mem)
      · exact Or.inr (Or.inr (Or.inr (Or.inl second_mem)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr third_mem)))
  · by_cases center_above_diagonal :
        10 * square.center.x - 11 ≤ 5 * square.center.y
    · rcases contains_bottomSecondTriangle center_y_upper (by linarith)
          center_above_diagonal with first_mem | second_mem | third_mem
      · exact Or.inr (Or.inl first_mem)
      · exact Or.inr (Or.inr (Or.inr (Or.inl second_mem)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr third_mem)))
    · rcases contains_bottomMiddleTriangle center_y_lower (by linarith)
          (by linarith) with first_mem | second_mem | third_mem
      · exact Or.inr (Or.inl first_mem)
      · exact Or.inr (Or.inr (Or.inl second_mem))
      · exact Or.inr (Or.inr (Or.inr (Or.inr third_mem)))

lemma contains_bottomBand
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 3)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 9 / 5) :
    ∃ index, square.Contains (points index) := by
  by_cases center_x_left : square.center.x ≤ 2
  · rcases contains_bottomLeftHalf center_x_lower center_x_left center_y_lower
        center_y_upper with first_mem | second_mem | third_mem | fourth_mem | fifth_mem
    · exact ⟨0, first_mem⟩
    · exact ⟨1, second_mem⟩
    · exact ⟨2, third_mem⟩
    · exact ⟨4, fourth_mem⟩
    · exact ⟨5, fifth_mem⟩
  · have reflected_result := contains_bottomLeftHalf
        (square := square.reflectX 4)
        (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
        (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
        (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
        (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    rcases reflected_result with first_mem | second_mem | third_mem | fourth_mem | fifth_mem
    · exact ⟨3, (square.reflectX_contains_iff 4 (points 3)).1 (by
        have point_identity : (points 3).reflectX 4 = points 0 := by
          rw [points_three, points_zero]
          norm_num [Point.reflectX]
        rw [point_identity]
        exact first_mem)⟩
    · exact ⟨2, (square.reflectX_contains_iff 4 (points 2)).1 (by
        have point_identity : (points 2).reflectX 4 = points 1 := by
          rw [points_two, points_one]
          norm_num [Point.reflectX]
        rw [point_identity]
        exact second_mem)⟩
    · exact ⟨1, (square.reflectX_contains_iff 4 (points 1)).1 (by
        have point_identity : (points 1).reflectX 4 = points 2 := by
          rw [points_one, points_two]
          norm_num [Point.reflectX]
        rw [point_identity]
        exact third_mem)⟩
    · exact ⟨6, (square.reflectX_contains_iff 4 (points 6)).1 (by
        have point_identity : (points 6).reflectX 4 = points 4 := by
          rw [points_six, points_four]
          norm_num [Point.reflectX]
        rw [point_identity]
        exact fourth_mem)⟩
    · exact ⟨5, (square.reflectX_contains_iff 4 (points 5)).1 (by
        have point_identity : (points 5).reflectX 4 = points 5 := by
          rw [points_five]
          norm_num [Point.reflectX]
        rw [point_identity]
        exact fifth_mem)⟩

def reflectYIndex : Fin 14 → Fin 14 :=
  ![10, 11, 12, 13, 7, 8, 9, 4, 5, 6, 0, 1, 2, 3]

lemma reflected_point (index : Fin 14) :
    (points (reflectYIndex index)).reflectY 4 = points index := by
  fin_cases index <;> simp [reflectYIndex, points, Point.reflectY] <;> norm_num

lemma contains_topBand
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 3)
    (center_y_lower : 11 / 5 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 3) :
    ∃ index, square.Contains (points index) := by
  obtain ⟨index, reflected_mem⟩ := contains_bottomBand
    (square := square.reflectY 4)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_lower)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  exact ⟨reflectYIndex index,
    (square.reflectY_contains_iff 4 (points (reflectYIndex index))).1 (by
      rw [reflected_point]
      exact reflected_mem)⟩

lemma contains_middleBand
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 3)
    (center_y_lower : 9 / 5 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 11 / 5) :
    ∃ index, square.Contains (points index) := by
  by_cases center_x_left : square.center.x ≤ 2
  · have rectangle_result := square.contains_translatedShortRectangleVertex
        (left := 1) (bottom := 9 / 5) center_x_lower (by norm_num; exact center_x_left)
        center_y_lower (by norm_num at *; assumption)
    rcases rectangle_result with bottom_left_mem | top_left_mem |
        bottom_right_mem | top_right_mem
    · exact ⟨4, by simpa only [points_four] using bottom_left_mem⟩
    · exact ⟨7, by
        rw [points_seven]
        convert top_left_mem using 1; norm_num⟩
    · exact ⟨5, by
        rw [points_five]
        convert bottom_right_mem using 1; norm_num⟩
    · exact ⟨8, by
        rw [points_eight]
        convert top_right_mem using 1; norm_num⟩
  · have rectangle_result := square.contains_translatedShortRectangleVertex
        (left := 2) (bottom := 9 / 5) (by linarith) (by norm_num; exact center_x_upper)
        center_y_lower (by norm_num at *; assumption)
    rcases rectangle_result with bottom_left_mem | top_left_mem |
        bottom_right_mem | top_right_mem
    · exact ⟨5, by simpa only [points_five] using bottom_left_mem⟩
    · exact ⟨8, by
        rw [points_eight]
        convert top_left_mem using 1; norm_num⟩
    · exact ⟨6, by
        rw [points_six]
        convert bottom_right_mem using 1; norm_num⟩
    · exact ⟨9, by
        rw [points_nine]
        convert top_right_mem using 1; norm_num⟩

end SquarePackingArchive.Records.Square15
