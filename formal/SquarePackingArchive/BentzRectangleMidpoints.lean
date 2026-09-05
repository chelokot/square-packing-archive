import SquarePackingArchive.TriangleRegions

namespace SquarePackingArchive.Bentz

theorem bottom_offset_point_of_missed_rectangle_corners
    (square : PlacedSquare) {left bottom height offset : ℝ}
    (height_positive : 0 < height) (offset_positive : 0 < offset) (offset_lt_one : offset < 1)
    (left_diagonal_bound : offset ^ 2 + height ^ 2 ≤ 1)
    (right_diagonal_bound : (1 - offset) ^ 2 + height ^ 2 ≤ 1)
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩) :
    square.Contains ⟨left + offset, bottom⟩ := by
  have bottom_left_missing : ¬ square.Contains ⟨left, bottom⟩ := by
    simpa using corners_missing 0 0
  have bottom_right_missing : ¬ square.Contains ⟨left + 1, bottom⟩ := by
    simpa using corners_missing 1 0
  have top_left_missing : ¬ square.Contains ⟨left, bottom + height⟩ := by
    simpa using corners_missing 0 1
  have top_right_missing : ¬ square.Contains ⟨left + 1, bottom + height⟩ := by
    simpa using corners_missing 1 1
  have horizontal_lower := mul_nonneg height_positive.le (sub_nonneg.mpr center_left)
  have horizontal_upper := mul_nonneg height_positive.le (sub_nonneg.mpr center_right)
  by_cases first_diagonal :
      height * (square.center.x - left) + offset * (square.center.y - bottom) ≤ height * offset
  · obtain first | middle | last := square.contains_triangleVertex_of_cross_nonnegative
      ⟨left, bottom⟩ ⟨left + offset, bottom⟩ ⟨left, bottom + height⟩
      (by dsimp [Point.orientedArea]; nlinarith [mul_pos height_positive offset_positive])
      (by dsimp [Point.orientedArea]; nlinarith [mul_nonneg offset_positive.le (sub_nonneg.mpr center_bottom)])
      (by dsimp [Point.orientedArea]; nlinarith)
      (by dsimp [Point.orientedArea]; nlinarith)
      (by nlinarith [sq_nonneg height]) (by nlinarith [sq_nonneg offset]) (by nlinarith)
    · exact (bottom_left_missing first).elim
    · exact middle
    · exact (top_left_missing last).elim
  by_cases second_diagonal :
      height * offset ≤ height * (square.center.x - left) - (1 - offset) * (square.center.y - bottom)
  · obtain first | middle | last := square.contains_triangleVertex_of_cross_nonnegative
      ⟨left + offset, bottom⟩ ⟨left + 1, bottom⟩ ⟨left + 1, bottom + height⟩
      (by dsimp [Point.orientedArea]; nlinarith [mul_pos height_positive (sub_pos.mpr offset_lt_one)])
      (by dsimp [Point.orientedArea]; nlinarith [mul_nonneg (sub_nonneg.mpr offset_lt_one.le) (sub_nonneg.mpr center_bottom)])
      (by dsimp [Point.orientedArea]; nlinarith)
      (by dsimp [Point.orientedArea]; nlinarith)
      (by nlinarith [sq_nonneg height]) (by nlinarith) (by nlinarith [sq_nonneg offset])
    · exact first
    · exact (bottom_right_missing middle).elim
    · exact (top_right_missing last).elim
  · obtain first | middle | last := square.contains_triangleVertex_of_cross_nonnegative
      ⟨left, bottom + height⟩ ⟨left + offset, bottom⟩ ⟨left + 1, bottom + height⟩
      (by dsimp [Point.orientedArea]; nlinarith)
      (by dsimp [Point.orientedArea]; nlinarith)
      (by dsimp [Point.orientedArea]; nlinarith)
      (by dsimp [Point.orientedArea]; linarith)
      (by nlinarith) (by norm_num) (by nlinarith)
    · exact (top_left_missing first).elim
    · exact middle
    · exact (top_right_missing last).elim

theorem both_offset_points_of_missed_rectangle_corners
    (square : PlacedSquare) {left bottom height offset : ℝ}
    (height_positive : 0 < height) (offset_positive : 0 < offset) (offset_lt_one : offset < 1)
    (left_diagonal_bound : offset ^ 2 + height ^ 2 ≤ 1)
    (right_diagonal_bound : (1 - offset) ^ 2 + height ^ 2 ≤ 1)
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩) :
    square.Contains ⟨left + offset, bottom⟩ ∧
      square.Contains ⟨left + offset, bottom + height⟩ := by
  refine ⟨bottom_offset_point_of_missed_rectangle_corners square height_positive offset_positive offset_lt_one
    left_diagonal_bound right_diagonal_bound
    center_left center_right center_bottom center_top corners_missing, ?_⟩
  have reflected := bottom_offset_point_of_missed_rectangle_corners
    (square.reflectY (2 * bottom + height)) (left := left) (bottom := bottom) (height := height)
    (offset := offset) height_positive offset_positive offset_lt_one left_diagonal_bound right_diagonal_bound
    center_left center_right
    (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    (by
      intro column row inside
      apply corners_missing column row.rev
      apply (square.reflectY_contains_iff (2 * bottom + height) _).1
      convert inside using 1
      fin_cases row <;> norm_num [Point.reflectY] <;> ring)
  apply (square.reflectY_contains_iff (2 * bottom + height) _).1
  convert reflected using 1
  dsimp [Point.reflectY]
  congr 1
  ring

theorem both_midpoints_of_missed_rectangle_corners
    (square : PlacedSquare) {left bottom height : ℝ}
    (height_positive : 0 < height) (diagonal_bound : 1 / 4 + height ^ 2 ≤ 1)
    (center_left : left ≤ square.center.x) (center_right : square.center.x ≤ left + 1)
    (center_bottom : bottom ≤ square.center.y) (center_top : square.center.y ≤ bottom + height)
    (corners_missing : ∀ column row : Fin 2,
      ¬ square.Contains ⟨left + column, bottom + height * row⟩) :
    square.Contains ⟨left + 1 / 2, bottom⟩ ∧
      square.Contains ⟨left + 1 / 2, bottom + height⟩ :=
  both_offset_points_of_missed_rectangle_corners square height_positive (by norm_num) (by norm_num)
    (by norm_num; exact diagonal_bound) (by norm_num; exact diagonal_bound)
    center_left center_right center_bottom center_top corners_missing

end SquarePackingArchive.Bentz
