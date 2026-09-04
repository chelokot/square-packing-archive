import SquarePackingArchive.Geometry

namespace SquarePackingArchive

set_option maxHeartbeats 4000000 in
lemma PlacedSquare.contains_shortRectangleVertex_of_nonnegative_frame
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_x_lower : 0 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 1)
    (center_y_lower : 0 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 2 / 5) :
    square.Contains ⟨0, 0⟩ ∨ square.Contains ⟨0, 2 / 5⟩ ∨
      square.Contains ⟨1, 0⟩ ∨ square.Contains ⟨1, 2 / 5⟩ := by
  let bottomLeftX :=
    -square.center.x * square.frame.cosine - square.center.y * square.frame.sine
  let bottomLeftY :=
    square.center.x * square.frame.sine - square.center.y * square.frame.cosine
  let topLeftX :=
    -square.center.x * square.frame.cosine +
      (2 / 5 - square.center.y) * square.frame.sine
  let topLeftY :=
    square.center.x * square.frame.sine +
      (2 / 5 - square.center.y) * square.frame.cosine
  let bottomRightX :=
    (1 - square.center.x) * square.frame.cosine -
      square.center.y * square.frame.sine
  let bottomRightY :=
    -(1 - square.center.x) * square.frame.sine -
      square.center.y * square.frame.cosine
  let topRightX :=
    (1 - square.center.x) * square.frame.cosine +
      (2 / 5 - square.center.y) * square.frame.sine
  let topRightY :=
    -(1 - square.center.x) * square.frame.sine +
      (2 / 5 - square.center.y) * square.frame.cosine
  have bottom_left_x_nonpositive : bottomLeftX ≤ 0 := by
    dsimp [bottomLeftX]
    have horizontal_product_nonnegative :
        0 ≤ square.center.x * square.frame.cosine :=
      mul_nonneg center_x_lower cosine_nonnegative
    have vertical_product_nonnegative :
        0 ≤ square.center.y * square.frame.sine :=
      mul_nonneg center_y_lower sine_nonnegative
    linarith
  have top_left_y_nonnegative : 0 ≤ topLeftY := by
    dsimp [topLeftY]
    positivity
  have bottom_right_y_nonpositive : bottomRightY ≤ 0 := by
    dsimp [bottomRightY]
    have remaining_nonnegative : 0 ≤ 1 - square.center.x := by linarith
    have horizontal_product_nonnegative :
        0 ≤ (1 - square.center.x) * square.frame.sine :=
      mul_nonneg remaining_nonnegative sine_nonnegative
    have vertical_product_nonnegative :
        0 ≤ square.center.y * square.frame.cosine :=
      mul_nonneg center_y_lower cosine_nonnegative
    linarith
  have top_right_x_nonnegative : 0 ≤ topRightX := by
    dsimp [topRightX]
    have horizontal_remaining_nonnegative : 0 ≤ 1 - square.center.x := by linarith
    have vertical_remaining_nonnegative : 0 ≤ 2 / 5 - square.center.y := by linarith
    positivity
  have component_sum_nonnegative :
      0 ≤ square.frame.cosine + square.frame.sine := by linarith
  have component_sum_sq_upper :
      (square.frame.cosine + square.frame.sine) ^ 2 ≤ 2 := by
    nlinarith [square.frame.unit, sq_nonneg (square.frame.cosine - square.frame.sine)]
  have component_sum_upper :
      square.frame.cosine + square.frame.sine ≤ 10 / 7 := by
    nlinarith
  have bottom_left_coordinates :
      square.localX ⟨0, 0⟩ = bottomLeftX ∧ square.localY ⟨0, 0⟩ = bottomLeftY := by
    constructor <;> dsimp [PlacedSquare.localX, PlacedSquare.localY,
      bottomLeftX, bottomLeftY] <;> ring
  have top_left_coordinates :
      square.localX ⟨0, 2 / 5⟩ = topLeftX ∧
        square.localY ⟨0, 2 / 5⟩ = topLeftY := by
    constructor <;> dsimp [PlacedSquare.localX, PlacedSquare.localY,
      topLeftX, topLeftY] <;> ring
  have bottom_right_coordinates :
      square.localX ⟨1, 0⟩ = bottomRightX ∧
        square.localY ⟨1, 0⟩ = bottomRightY := by
    constructor <;> dsimp [PlacedSquare.localX, PlacedSquare.localY,
      bottomRightX, bottomRightY] <;> ring
  have top_right_coordinates :
      square.localX ⟨1, 2 / 5⟩ = topRightX ∧
        square.localY ⟨1, 2 / 5⟩ = topRightY := by
    constructor <;> rfl
  by_contra no_vertex
  push Not at no_vertex
  have bottom_left_miss :
      bottomLeftX < -1 / 2 ∨ bottomLeftY < -1 / 2 ∨ 1 / 2 < bottomLeftY := by
    by_contra inside
    push Not at inside
    apply no_vertex.1
    rw [square.contains_iff_localCoordinates, bottom_left_coordinates.1,
      bottom_left_coordinates.2]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have top_left_miss :
      topLeftX < -1 / 2 ∨ 1 / 2 < topLeftX ∨ 1 / 2 < topLeftY := by
    by_contra inside
    push Not at inside
    apply no_vertex.2.1
    rw [square.contains_iff_localCoordinates, top_left_coordinates.1,
      top_left_coordinates.2]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have bottom_right_miss :
      bottomRightX < -1 / 2 ∨ 1 / 2 < bottomRightX ∨
        bottomRightY < -1 / 2 := by
    by_contra inside
    push Not at inside
    apply no_vertex.2.2.1
    rw [square.contains_iff_localCoordinates, bottom_right_coordinates.1,
      bottom_right_coordinates.2]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have top_right_miss :
      1 / 2 < topRightX ∨ topRightY < -1 / 2 ∨ 1 / 2 < topRightY := by
    by_contra inside
    push Not at inside
    apply no_vertex.2.2.2
    rw [square.contains_iff_localCoordinates, top_right_coordinates.1,
      top_right_coordinates.2]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  rcases bottom_left_miss with bottom_left_x_low | bottom_left_y_low |
      bottom_left_y_high <;>
    rcases top_left_miss with top_left_x_low | top_left_x_high |
      top_left_y_high <;>
    rcases bottom_right_miss with bottom_right_x_low | bottom_right_x_high |
      bottom_right_y_low <;>
    rcases top_right_miss with top_right_x_high | top_right_y_low |
      top_right_y_high
  all_goals
    dsimp [bottomLeftX, bottomLeftY, topLeftX, topLeftY, bottomRightX,
      bottomRightY, topRightX, topRightY] at *
    nlinarith [square.frame.unit]

lemma PlacedSquare.contains_shortRectangleVertex
    {square : PlacedSquare}
    (center_x_lower : 0 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 1)
    (center_y_lower : 0 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 2 / 5) :
    square.Contains ⟨0, 0⟩ ∨ square.Contains ⟨0, 2 / 5⟩ ∨
      square.Contains ⟨1, 0⟩ ∨ square.Contains ⟨1, 2 / 5⟩ := by
  have normalized_result :=
    square.firstQuadrant.contains_shortRectangleVertex_of_nonnegative_frame
      square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
      (by simpa using center_x_lower) (by simpa using center_x_upper)
      (by simpa using center_y_lower) (by simpa using center_y_upper)
  simpa using normalized_result

lemma PlacedSquare.contains_translatedShortRectangleVertex
    {square : PlacedSquare} {left bottom : ℝ}
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 1)
    (center_y_lower : bottom ≤ square.center.y)
    (center_y_upper : square.center.y ≤ bottom + 2 / 5) :
    square.Contains ⟨left, bottom⟩ ∨
      square.Contains ⟨left, bottom + 2 / 5⟩ ∨
        square.Contains ⟨left + 1, bottom⟩ ∨
          square.Contains ⟨left + 1, bottom + 2 / 5⟩ := by
  let shifted := square.translate (-left) (-bottom)
  have shifted_result := shifted.contains_shortRectangleVertex
    (by dsimp [shifted, PlacedSquare.translate, Point.translate]; linarith)
    (by dsimp [shifted, PlacedSquare.translate, Point.translate]; linarith)
    (by dsimp [shifted, PlacedSquare.translate, Point.translate]; linarith)
    (by dsimp [shifted, PlacedSquare.translate, Point.translate]; linarith)
  rcases shifted_result with bottom_left_mem | top_left_mem |
      bottom_right_mem | top_right_mem
  · exact Or.inl ((square.translate_contains_iff (-left) (-bottom)
      ⟨left, bottom⟩).1 (by
        convert bottom_left_mem using 1; simp [Point.translate]))
  · exact Or.inr (Or.inl ((square.translate_contains_iff (-left) (-bottom)
      ⟨left, bottom + 2 / 5⟩).1 (by
        convert top_left_mem using 1; simp [Point.translate])))
  · exact Or.inr (Or.inr (Or.inl ((square.translate_contains_iff (-left) (-bottom)
      ⟨left + 1, bottom⟩).1 (by
        convert bottom_right_mem using 1; simp [Point.translate]))))
  · exact Or.inr (Or.inr (Or.inr ((square.translate_contains_iff (-left) (-bottom)
      ⟨left + 1, bottom + 2 / 5⟩).1 (by
        convert top_right_mem using 1; simp [Point.translate]))))

end SquarePackingArchive
