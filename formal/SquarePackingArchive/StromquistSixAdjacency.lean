import SquarePackingArchive.StromquistSixPoints
import SquarePackingArchive.StromquistSixIncidence

namespace SquarePackingArchive.StromquistSix

theorem rectangle_cross_point_nonnegative_frame {square : PlacedSquare}
    {left bottom width height : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine) (sine_nonnegative : 0 ≤ square.frame.sine)
    (width_nonnegative : 0 ≤ width) (height_nonnegative : 0 ≤ height)
    (span_bound : width * square.frame.sine + height * square.frame.cosine ≤ 1)
    (southwest_mem : square.Contains ⟨left, bottom⟩)
    (northeast_mem : square.Contains ⟨left + width, bottom + height⟩) :
    square.Contains ⟨left + width, bottom⟩ ∨ square.Contains ⟨left, bottom + height⟩ := by
  have southwest := (square.contains_iff_localCoordinates _).1 southwest_mem
  have northeast := (square.contains_iff_localCoordinates _).1 northeast_mem
  simp only [abs_le] at southwest northeast
  have horizontal_sine := mul_nonneg width_nonnegative sine_nonnegative
  have horizontal_cosine := mul_nonneg width_nonnegative cosine_nonnegative
  have vertical_sine := mul_nonneg height_nonnegative sine_nonnegative
  have vertical_cosine := mul_nonneg height_nonnegative cosine_nonnegative
  rw [square.contains_iff_localCoordinates, square.contains_iff_localCoordinates, abs_le, abs_le, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at southwest northeast ⊢
  by_cases lower_bound : -(1 / 2) ≤ square.localY ⟨left + width, bottom⟩
  · dsimp [PlacedSquare.localY] at lower_bound
    left
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by linarith, by nlinarith⟩⟩
  · dsimp [PlacedSquare.localY] at lower_bound
    right
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem rectangle_cross_point {square : PlacedSquare} {left bottom width height : ℝ}
    (width_nonnegative : 0 ≤ width) (height_nonnegative : 0 ≤ height) (span_bound : width + height ≤ 1)
    (southwest_mem : square.Contains ⟨left, bottom⟩)
    (northeast_mem : square.Contains ⟨left + width, bottom + height⟩) :
    square.Contains ⟨left + width, bottom⟩ ∨ square.Contains ⟨left, bottom + height⟩ := by
  have result := rectangle_cross_point_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    width_nonnegative height_nonnegative
    (by nlinarith [square.firstQuadrant.frame.cosine_le_one square.firstQuadrant_cosine_nonnegative,
      square.firstQuadrant.frame.sine_le_one square.firstQuadrant_sine_nonnegative])
    ((square.firstQuadrant_contains_iff _).2 southwest_mem)
    ((square.firstQuadrant_contains_iff _).2 northeast_mem)
  simpa only [PlacedSquare.firstQuadrant_contains_iff] using result

theorem rectangle_midline_point_nonnegative_frame {square : PlacedSquare}
    {left bottom width height : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine) (sine_nonnegative : 0 ≤ square.frame.sine)
    (width_nonnegative : 0 ≤ width) (height_nonnegative : 0 ≤ height)
    (height_bound : height * square.frame.cosine ≤ 1)
    (southwest_mem : square.Contains ⟨left, bottom⟩)
    (northeast_mem : square.Contains ⟨left + width, bottom + height⟩) :
    square.Contains ⟨left + width / 2, bottom⟩ ∨
      square.Contains ⟨left + width / 2, bottom + height⟩ := by
  have southwest := (square.contains_iff_localCoordinates _).1 southwest_mem
  have northeast := (square.contains_iff_localCoordinates _).1 northeast_mem
  simp only [abs_le] at southwest northeast
  have horizontal_sine := mul_nonneg width_nonnegative sine_nonnegative
  have horizontal_cosine := mul_nonneg width_nonnegative cosine_nonnegative
  have vertical_sine := mul_nonneg height_nonnegative sine_nonnegative
  have vertical_cosine := mul_nonneg height_nonnegative cosine_nonnegative
  rw [square.contains_iff_localCoordinates, square.contains_iff_localCoordinates, abs_le, abs_le, abs_le, abs_le]
  dsimp [PlacedSquare.localX, PlacedSquare.localY] at southwest northeast ⊢
  by_cases lower_bound : -(1 / 2) ≤ square.localY ⟨left + width / 2, bottom⟩
  · dsimp [PlacedSquare.localY] at lower_bound
    left
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by linarith, by nlinarith⟩⟩
  · dsimp [PlacedSquare.localY] at lower_bound
    right
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

theorem rectangle_midline_point {square : PlacedSquare} {left bottom width height : ℝ}
    (width_nonnegative : 0 ≤ width) (height_nonnegative : 0 ≤ height) (height_bound : height ≤ 1)
    (southwest_mem : square.Contains ⟨left, bottom⟩)
    (northeast_mem : square.Contains ⟨left + width, bottom + height⟩) :
    square.Contains ⟨left + width / 2, bottom⟩ ∨
      square.Contains ⟨left + width / 2, bottom + height⟩ := by
  have result := rectangle_midline_point_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    width_nonnegative height_nonnegative
    (by nlinarith [square.firstQuadrant.frame.cosine_le_one square.firstQuadrant_cosine_nonnegative])
    ((square.firstQuadrant_contains_iff _).2 southwest_mem)
    ((square.firstQuadrant_contains_iff _).2 northeast_mem)
  simpa only [PlacedSquare.firstQuadrant_contains_iff] using result

def HasAdjacentKeyPoints (square : PlacedSquare) : Prop :=
  ∃ first second : Fin 9, square.Contains (keyPoints first) ∧
    square.Contains (keyPoints second) ∧ GridAdjacent first second

theorem contains_adjacent_keyPoints_increasing {square : PlacedSquare} {first second : Fin 9}
    (horizontal_order : first.val % 3 < second.val % 3)
    (vertical_order : first.val / 3 ≤ second.val / 3)
    (first_mem : square.Contains (keyPoints first)) (second_mem : square.Contains (keyPoints second)) :
    HasAdjacentKeyPoints square := by
  fin_cases first <;> fin_cases second
  all_goals try norm_num at horizontal_order
  all_goals try norm_num at vertical_order
  · exact ⟨0, 1, first_mem, second_mem, by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 1)
      (width := 1) (height := 0) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨0, 1, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨2, 1, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_cross_point (left := 1) (bottom := 1)
      (width := 1 / 2) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨0, 1, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨4, 3, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 1)
      (width := 1) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨0, 1, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨5, 4, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_midline_point (square := square.swap)
      (left := 1) (bottom := 1) (width := 1) (height := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints, Point.swap] using (square.swap_contains_iff (keyPoints 0)).2 first_mem)
      (by convert (square.swap_contains_iff (keyPoints 7)).2 second_mem using 1; norm_num [keyPoints, Point.swap])
    · exact ⟨0, 3, first_mem, (square.swap_contains_iff _).1 (by convert left using 1; norm_num [keyPoints, Point.swap]), by decide⟩
    · exact ⟨7, 4, second_mem, (square.swap_contains_iff _).1 (by convert right using 1; norm_num [keyPoints, Point.swap]), by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 1)
      (width := 1) (height := 1) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨0, 1, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨8, 7, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · exact ⟨1, 2, first_mem, second_mem, by decide⟩
  · obtain left | right := rectangle_cross_point (left := 3 / 2) (bottom := 1)
      (width := 1 / 2) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨1, 2, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨5, 4, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_midline_point (square := square.swap)
      (left := 1) (bottom := 3 / 2) (width := 1) (height := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints, Point.swap] using (square.swap_contains_iff (keyPoints 1)).2 first_mem)
      (by convert (square.swap_contains_iff (keyPoints 8)).2 second_mem using 1; norm_num [keyPoints, Point.swap])
    · exact ⟨1, 4, first_mem, (square.swap_contains_iff _).1 (by convert left using 1; norm_num [keyPoints, Point.swap]), by decide⟩
    · exact ⟨8, 5, second_mem, (square.swap_contains_iff _).1 (by convert right using 1; norm_num [keyPoints, Point.swap]), by decide⟩
  · exact ⟨3, 4, first_mem, second_mem, by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 3 / 2)
      (width := 1) (height := 0) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨3, 4, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨5, 4, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_cross_point (left := 1) (bottom := 3 / 2)
      (width := 1 / 2) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨3, 4, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨7, 6, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 3 / 2)
      (width := 1) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨3, 4, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨8, 7, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · exact ⟨4, 5, first_mem, second_mem, by decide⟩
  · obtain left | right := rectangle_cross_point (left := 3 / 2) (bottom := 3 / 2)
      (width := 1 / 2) (height := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨4, 5, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨8, 7, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · exact ⟨6, 7, first_mem, second_mem, by decide⟩
  · obtain left | right := rectangle_midline_point (left := 1) (bottom := 2)
      (width := 1) (height := 0) (by norm_num) (by norm_num) (by norm_num)
      (by simpa [keyPoints] using first_mem)
      (by convert second_mem using 1; norm_num [keyPoints])
    · exact ⟨6, 7, first_mem, by convert left using 1; norm_num [keyPoints], by decide⟩
    · exact ⟨8, 7, second_mem, by convert right using 1; norm_num [keyPoints], by decide⟩
  · exact ⟨7, 8, first_mem, second_mem, by decide⟩

def keySwap : Fin 9 → Fin 9 := ![0, 3, 6, 1, 4, 7, 2, 5, 8]

theorem keyPoints_swap (index : Fin 9) : keyPoints (keySwap index) = (keyPoints index).swap := by
  fin_cases index <;> rfl

theorem keyReflectX_column (index : Fin 9) : (keyReflectX index).val % 3 = 2 - index.val % 3 := by
  fin_cases index <;> rfl

theorem keyReflectX_row (index : Fin 9) : (keyReflectX index).val / 3 = index.val / 3 := by
  fin_cases index <;> rfl

theorem keySwap_column (index : Fin 9) : (keySwap index).val % 3 = index.val / 3 := by
  fin_cases index <;> rfl

theorem keySwap_row (index : Fin 9) : (keySwap index).val / 3 = index.val % 3 := by
  fin_cases index <;> rfl

theorem gridAdjacent_keyReflectX : ∀ first second : Fin 9,
    GridAdjacent (keyReflectX first) (keyReflectX second) ↔ GridAdjacent first second := by decide

theorem gridAdjacent_keySwap : ∀ first second : Fin 9,
    GridAdjacent (keySwap first) (keySwap second) ↔ GridAdjacent first second := by decide

theorem HasAdjacentKeyPoints.of_reflectX {square : PlacedSquare}
    (reflected : HasAdjacentKeyPoints (square.reflectX 3)) : HasAdjacentKeyPoints square := by
  obtain ⟨first, second, first_mem, second_mem, adjacent⟩ := reflected
  refine ⟨keyReflectX first, keyReflectX second, ?_, ?_, (gridAdjacent_keyReflectX first second).2 adjacent⟩
  · rw [keyPoints_reflectX]
    exact (square.reflectX_contains_iff 3 _).1 (by simpa using first_mem)
  · rw [keyPoints_reflectX]
    exact (square.reflectX_contains_iff 3 _).1 (by simpa using second_mem)

theorem HasAdjacentKeyPoints.of_swap {square : PlacedSquare}
    (swapped : HasAdjacentKeyPoints square.swap) : HasAdjacentKeyPoints square := by
  obtain ⟨first, second, first_mem, second_mem, adjacent⟩ := swapped
  refine ⟨keySwap first, keySwap second, ?_, ?_, (gridAdjacent_keySwap first second).2 adjacent⟩
  · rw [keyPoints_swap]
    exact (square.swap_contains_iff _).1 (by simpa using first_mem)
  · rw [keyPoints_swap]
    exact (square.swap_contains_iff _).1 (by simpa using second_mem)

theorem contains_adjacent_keyPoints_nondecreasing {square : PlacedSquare} {first second : Fin 9}
    (distinct : first ≠ second) (vertical_order : first.val / 3 ≤ second.val / 3)
    (first_mem : square.Contains (keyPoints first)) (second_mem : square.Contains (keyPoints second)) :
    HasAdjacentKeyPoints square := by
  by_cases horizontal_order : first.val % 3 < second.val % 3
  · exact contains_adjacent_keyPoints_increasing horizontal_order vertical_order first_mem second_mem
  by_cases same_column : first.val % 3 = second.val % 3
  · have vertical_strict : first.val / 3 < second.val / 3 := by
      by_contra! not_strict
      apply distinct
      apply Fin.ext
      omega
    apply HasAdjacentKeyPoints.of_swap
    apply contains_adjacent_keyPoints_increasing (first := keySwap first) (second := keySwap second)
    · simpa only [keySwap_column] using vertical_strict
    · simp only [keySwap_row]
      omega
    · rw [keyPoints_swap]
      exact (square.swap_contains_iff _).2 first_mem
    · rw [keyPoints_swap]
      exact (square.swap_contains_iff _).2 second_mem
  · apply HasAdjacentKeyPoints.of_reflectX
    apply contains_adjacent_keyPoints_increasing (first := keyReflectX first) (second := keyReflectX second)
    · simp only [keyReflectX_column]
      omega
    · simpa only [keyReflectX_row] using vertical_order
    · rw [keyPoints_reflectX]
      exact (square.reflectX_contains_iff 3 _).2 first_mem
    · rw [keyPoints_reflectX]
      exact (square.reflectX_contains_iff 3 _).2 second_mem

theorem contains_adjacent_keyPoints {square : PlacedSquare} {first second : Fin 9}
    (distinct : first ≠ second)
    (first_mem : square.Contains (keyPoints first)) (second_mem : square.Contains (keyPoints second)) :
    ∃ left right : Fin 9, square.Contains (keyPoints left) ∧
      square.Contains (keyPoints right) ∧ GridAdjacent left right := by
  by_cases vertical_order : first.val / 3 ≤ second.val / 3
  · exact contains_adjacent_keyPoints_nondecreasing distinct vertical_order first_mem second_mem
  · exact contains_adjacent_keyPoints_nondecreasing distinct.symm (le_of_not_ge vertical_order) second_mem first_mem

end SquarePackingArchive.StromquistSix
