import SquarePackingArchive.Friedman
import SquarePackingArchive.Records.NearSquare

namespace SquarePackingArchive.Records.Square24

noncomputable def points : Fin 23 → Point := ![
  ⟨1, 1⟩, ⟨17 / 10, 1⟩, ⟨5 / 2, 1⟩, ⟨33 / 10, 1⟩, ⟨4, 1⟩,
  ⟨1, 17 / 10⟩, ⟨2, 17 / 10⟩, ⟨3, 17 / 10⟩, ⟨4, 17 / 10⟩,
  ⟨1, 5 / 2⟩, ⟨3 / 2, 5 / 2⟩, ⟨5 / 2, 5 / 2⟩,
  ⟨7 / 2, 5 / 2⟩, ⟨4, 5 / 2⟩,
  ⟨1, 33 / 10⟩, ⟨2, 33 / 10⟩, ⟨3, 33 / 10⟩, ⟨4, 33 / 10⟩,
  ⟨1, 4⟩, ⟨17 / 10, 4⟩, ⟨5 / 2, 4⟩, ⟨33 / 10, 4⟩, ⟨4, 4⟩
]

def reflectXIndex : Fin 23 → Fin 23 :=
  ![4, 3, 2, 1, 0, 8, 7, 6, 5, 13, 12, 11, 10, 9, 17, 16, 15, 14,
    22, 21, 20, 19, 18]

def reflectYIndex : Fin 23 → Fin 23 :=
  ![18, 19, 20, 21, 22, 14, 15, 16, 17, 9, 10, 11, 12, 13, 5, 6, 7, 8,
    0, 1, 2, 3, 4]

lemma reflected_x_point (index : Fin 23) :
    (points (reflectXIndex index)).reflectX 5 = points index := by
  fin_cases index <;> simp [reflectXIndex, points, Point.reflectX] <;> norm_num

lemma reflected_y_point (index : Fin 23) :
    (points (reflectYIndex index)).reflectY 5 = points index := by
  fin_cases index <;> simp [reflectYIndex, points, Point.reflectY] <;> norm_num

private lemma contains_triangle
    {square : PlacedSquare} (first second third : Fin 23)
    (firstWeight secondWeight : ℝ)
    (first_nonnegative : 0 ≤ firstWeight)
    (second_nonnegative : 0 ≤ secondWeight)
    (weights_upper : firstWeight + secondWeight ≤ 1)
    (center_x_eq : square.center.x = firstWeight * (points first).x +
      secondWeight * (points second).x +
      (1 - firstWeight - secondWeight) * (points third).x)
    (center_y_eq : square.center.y = firstWeight * (points first).y +
      secondWeight * (points second).y +
      (1 - firstWeight - secondWeight) * (points third).y)
    (first_second_distance :
      ((points first).x - (points second).x) ^ 2 +
      ((points first).y - (points second).y) ^ 2 ≤ 1)
    (first_third_distance :
      ((points first).x - (points third).x) ^ 2 +
      ((points first).y - (points third).y) ^ 2 ≤ 1)
    (second_third_distance :
      ((points second).x - (points third).x) ^ 2 +
      ((points second).y - (points third).y) ^ 2 ≤ 1) :
    ∃ index, square.Contains (points index) := by
  rcases square.contains_triangleVertex (points first) (points second) (points third)
      firstWeight secondWeight (1 - firstWeight - secondWeight)
      first_nonnegative second_nonnegative (by linarith) (by ring)
      center_x_eq center_y_eq first_second_distance first_third_distance
      second_third_distance with first_mem | second_mem | third_mem
  · exact ⟨first, first_mem⟩
  · exact ⟨second, second_mem⟩
  · exact ⟨third, third_mem⟩

lemma contains_lowerLeftBand
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 5 / 2)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 17 / 10) :
    ∃ index, square.Contains (points index) := by
  by_cases first_diagonal : square.center.x + square.center.y ≤ 27 / 10
  · apply contains_triangle 0 1 5
      (1 - 10 / 7 * (square.center.x - 1) - 10 / 7 * (square.center.y - 1))
      (10 / 7 * (square.center.x - 1))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  by_cases second_diagonal : 7 * square.center.x - 3 * square.center.y ≤ 89 / 10
  · apply contains_triangle 1 5 6
      (10 / 7 * (17 / 10 - square.center.y))
      (2 - square.center.x - 3 / 7 * (17 / 10 - square.center.y))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  by_cases third_diagonal : 7 * square.center.x + 5 * square.center.y ≤ 45 / 2
  · apply contains_triangle 1 2 6
      (1 - 10 / 7 * (square.center.y - 1) -
        5 / 4 * (square.center.x - 17 / 10 - 3 / 7 * (square.center.y - 1)))
      (5 / 4 * (square.center.x - 17 / 10 - 3 / 7 * (square.center.y - 1)))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  · apply contains_triangle 2 6 7
      (10 / 7 * (17 / 10 - square.center.y))
      (3 - square.center.x - 5 / 7 * (17 / 10 - square.center.y))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith

lemma contains_middleLeftBand
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 5 / 2)
    (center_y_lower : 17 / 10 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 5 / 2) :
    ∃ index, square.Contains (points index) := by
  by_cases first_diagonal : 8 * square.center.x - 5 * square.center.y ≤ -(1 / 2)
  · apply contains_triangle 5 9 10
      (5 / 4 * (5 / 2 - square.center.y))
      (1 - 5 / 4 * (5 / 2 - square.center.y) - 2 * (square.center.x - 1))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  by_cases second_diagonal : 8 * square.center.x + 5 * square.center.y ≤ 49 / 2
  · apply contains_triangle 5 6 10
      (2 - square.center.x - 5 / 8 * (square.center.y - 17 / 10))
      (square.center.x - 1 - 5 / 8 * (square.center.y - 17 / 10))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  by_cases third_diagonal : 8 * square.center.x - 5 * square.center.y ≤ 15 / 2
  · apply contains_triangle 6 10 11
      (5 / 4 * (5 / 2 - square.center.y))
      (5 / 2 - square.center.x - 5 / 8 * (5 / 2 - square.center.y))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith
  · apply contains_triangle 6 7 11
      (3 - square.center.x - 5 / 8 * (square.center.y - 17 / 10))
      (square.center.x - 2 - 5 / 8 * (square.center.y - 17 / 10))
    all_goals
      try dsimp [points]
      norm_num at * <;> linarith

lemma contains_lowerLeftInterior
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 5 / 2)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 5 / 2) :
    ∃ index, square.Contains (points index) := by
  by_cases lower_band : square.center.y ≤ 17 / 10
  · exact contains_lowerLeftBand center_x_lower center_x_upper center_y_lower lower_band
  · exact contains_middleLeftBand center_x_lower center_x_upper (by linarith) center_y_upper

lemma contains_lowerInterior
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 4)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 5 / 2) :
    ∃ index, square.Contains (points index) := by
  by_cases center_left : square.center.x ≤ 5 / 2
  · exact contains_lowerLeftInterior center_x_lower center_left center_y_lower center_y_upper
  · obtain ⟨index, reflected_mem⟩ := contains_lowerLeftInterior
      (square := square.reflectX 5)
      (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    exact ⟨reflectXIndex index,
      (square.reflectX_contains_iff 5 (points (reflectXIndex index))).1
        (by rw [reflected_x_point]; exact reflected_mem)⟩

lemma contains_interior
    {square : PlacedSquare}
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 4)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 4) :
    ∃ index, square.Contains (points index) := by
  by_cases center_lower : square.center.y ≤ 5 / 2
  · exact contains_lowerInterior center_x_lower center_x_upper center_y_lower center_lower
  · obtain ⟨index, reflected_mem⟩ := contains_lowerInterior
      (square := square.reflectY 5)
      (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_lower)
      (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    exact ⟨reflectYIndex index,
      (square.reflectY_contains_iff 5 (points (reflectYIndex index))).1
        (by rw [reflected_y_point]; exact reflected_mem)⟩

lemma contains_bottomLeftPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_x_upper : square.center.x ≤ 5 / 2)
    (center_y_upper : square.center.y ≤ 1) :
    ∃ index, square.Contains (points index) := by
  by_cases center_corner : square.center.x ≤ 1
  · exact ⟨0, square.contains_cornerPoint fits (by norm_num) (by norm_num)
      center_corner center_y_upper⟩
  by_cases center_first : square.center.x ≤ 17 / 10
  · rcases square.contains_bottomBoundaryPair (left := 1) (gap := 7 / 10)
        fits (by norm_num) (by norm_num) (by linarith) (by linarith)
        center_y_upper with left_mem | right_mem
    · exact ⟨0, left_mem⟩
    · exact ⟨1, by convert right_mem using 1; norm_num [points]⟩
  · rcases square.contains_bottomBoundaryPair (left := 17 / 10) (gap := 4 / 5)
        fits (by norm_num) (by norm_num) (by linarith) (by linarith)
        center_y_upper with left_mem | right_mem
    · exact ⟨1, left_mem⟩
    · exact ⟨2, by convert right_mem using 1; simp [points]; norm_num⟩

lemma contains_bottomPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_y_upper : square.center.y ≤ 1) :
    ∃ index, square.Contains (points index) := by
  by_cases center_left : square.center.x ≤ 5 / 2
  · exact contains_bottomLeftPerimeter fits center_left center_y_upper
  · obtain ⟨index, reflected_mem⟩ := contains_bottomLeftPerimeter
      ((square.reflectX_fits_iff 5).2 fits)
      (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    exact ⟨reflectXIndex index,
      (square.reflectX_contains_iff 5 (points (reflectXIndex index))).1
        (by rw [reflected_x_point]; exact reflected_mem)⟩

lemma contains_topPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_y_lower : 4 ≤ square.center.y) :
    ∃ index, square.Contains (points index) := by
  obtain ⟨index, reflected_mem⟩ := contains_bottomPerimeter
    ((square.reflectY_fits_iff 5).2 fits)
    (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
  exact ⟨reflectYIndex index,
    (square.reflectY_contains_iff 5 (points (reflectYIndex index))).1
      (by rw [reflected_y_point]; exact reflected_mem)⟩

lemma contains_leftLowerPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_x_upper : square.center.x ≤ 1)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 5 / 2) :
    ∃ index, square.Contains (points index) := by
  have swapped_fits := (square.swap_fits_iff 5).2 fits
  have swapped_height : square.swap.center.y ≤ 1 := center_x_upper
  by_cases center_first : square.center.y ≤ 17 / 10
  · rcases square.swap.contains_bottomBoundaryPair (left := 1) (gap := 7 / 10)
        swapped_fits (by norm_num) (by norm_num) center_y_lower
        (by change square.center.y ≤ 1 + 7 / 10; linarith)
        swapped_height with bottom_mem | top_mem
    · exact ⟨0, (square.swap_contains_iff (points 0)).1 bottom_mem⟩
    · exact ⟨5, (square.swap_contains_iff (points 5)).1 (by
        convert top_mem using 1; simp [points, Point.swap]; norm_num)⟩
  · rcases square.swap.contains_bottomBoundaryPair (left := 17 / 10) (gap := 4 / 5)
        swapped_fits (by norm_num) (by norm_num)
        (by change 17 / 10 ≤ square.center.y; linarith)
        (by change square.center.y ≤ 17 / 10 + 4 / 5; linarith)
        swapped_height with bottom_mem | top_mem
    · exact ⟨5, (square.swap_contains_iff (points 5)).1 bottom_mem⟩
    · exact ⟨9, (square.swap_contains_iff (points 9)).1 (by
        convert top_mem using 1; simp [points, Point.swap]; norm_num)⟩

lemma contains_leftPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_x_upper : square.center.x ≤ 1)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 4) :
    ∃ index, square.Contains (points index) := by
  by_cases center_lower : square.center.y ≤ 5 / 2
  · exact contains_leftLowerPerimeter fits center_x_upper center_y_lower center_lower
  · obtain ⟨index, reflected_mem⟩ := contains_leftLowerPerimeter
      ((square.reflectY_fits_iff 5).2 fits)
      (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_x_upper)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    exact ⟨reflectYIndex index,
      (square.reflectY_contains_iff 5 (points (reflectYIndex index))).1
        (by rw [reflected_y_point]; exact reflected_mem)⟩

lemma contains_rightPerimeter
    {square : PlacedSquare} (fits : square.Fits 5)
    (center_x_lower : 4 ≤ square.center.x)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 4) :
    ∃ index, square.Contains (points index) := by
  obtain ⟨index, reflected_mem⟩ := contains_leftPerimeter
    ((square.reflectX_fits_iff 5).2 fits)
    (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_lower)
    (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
  exact ⟨reflectXIndex index,
    (square.reflectX_contains_iff 5 (points (reflectXIndex index))).1
      (by rw [reflected_x_point]; exact reflected_mem)⟩

theorem points_unavoidable : Unavoidable points 5 := by
  intro square fits
  by_cases bottom : square.center.y ≤ 1
  · exact contains_bottomPerimeter fits bottom
  by_cases top : 4 ≤ square.center.y
  · exact contains_topPerimeter fits top
  by_cases left : square.center.x ≤ 1
  · exact contains_leftPerimeter fits left (by linarith) (by linarith)
  by_cases right : 4 ≤ square.center.x
  · exact contains_rightPerimeter fits right (by linarith) (by linarith)
  · exact contains_interior (by linarith) (by linarith) (by linarith) (by linarith)

theorem s24_lower_bound : IsLowerBound 24 5 := by
  simpa using lowerBound_succ_of_unavoidable points_unavoidable

theorem s24_eq_five : IsMinimumSide 24 5 := by
  exact ⟨by simpa using NearSquare.squareMinusOne_hasPacking 5, s24_lower_bound⟩

end SquarePackingArchive.Records.Square24
