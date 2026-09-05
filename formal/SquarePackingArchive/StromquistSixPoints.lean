import SquarePackingArchive.StromquistSixCenter
import SquarePackingArchive.TriangleRegions
import SquarePackingArchive.FriedmanStrip

namespace SquarePackingArchive.StromquistSix

noncomputable def keyPoints (index : Fin 9) : Point :=
  match index.val with
  | 0 => ⟨1, 1⟩
  | 1 => ⟨3 / 2, 1⟩
  | 2 => ⟨2, 1⟩
  | 3 => ⟨1, 3 / 2⟩
  | 4 => ⟨3 / 2, 3 / 2⟩
  | 5 => ⟨2, 3 / 2⟩
  | 6 => ⟨1, 2⟩
  | 7 => ⟨3 / 2, 2⟩
  | _ => ⟨2, 2⟩

def keyReflectX : Fin 9 → Fin 9 := ![2, 1, 0, 5, 4, 3, 8, 7, 6]
def keyReflectY : Fin 9 → Fin 9 := ![6, 7, 8, 3, 4, 5, 0, 1, 2]

theorem keyPoints_reflectX (index : Fin 9) :
    keyPoints (keyReflectX index) = (keyPoints index).reflectX 3 := by
  fin_cases index <;> dsimp [keyPoints, keyReflectX, Point.reflectX] <;> norm_num

theorem keyPoints_reflectY (index : Fin 9) :
    keyPoints (keyReflectY index) = (keyPoints index).reflectY 3 := by
  fin_cases index <;> dsimp [keyPoints, keyReflectY, Point.reflectY] <;> norm_num

theorem keyReflectX_ne_center {index : Fin 9} (not_center : index ≠ 4) : keyReflectX index ≠ 4 := by
  fin_cases index <;> dsimp [keyReflectX]
  all_goals first | exact not_center | decide

theorem keyReflectY_ne_center {index : Fin 9} (not_center : index ≠ 4) : keyReflectY index ≠ 4 := by
  fin_cases index <;> dsimp [keyReflectY]
  all_goals first | exact not_center | decide

theorem perimeter_unavoidable_lower_left {square : PlacedSquare}
    (fits : square.Fits 3) (left_half : square.center.x ≤ 3 / 2)
    (bottom_half : square.center.y ≤ 3 / 2) :
    ∃ index : Fin 9, index ≠ 4 ∧ square.Contains (keyPoints index) := by
  have weight : ∀ frame : Frame, 0 ≤ frame.cosine → 0 ≤ frame.sine →
      1 + 1 / 2 * (frame.cosine * frame.sine) ≤ frame.cosine + frame.sine := by
    intro frame cosine_nonnegative sine_nonnegative
    exact frame.height_add_gap_product_le_sum_of_gap_le_four_fifths
      cosine_nonnegative sine_nonnegative (by norm_num) (by norm_num)
  by_cases left_strip : square.center.x ≤ 1
  · by_cases bottom_strip : square.center.y ≤ 1
    · exact ⟨0, by decide, by simpa [keyPoints] using square.contains_unitCorner fits left_strip bottom_strip⟩
    · obtain left | right := square.swap.contains_bottomPairWith (left := 1) (targetHeight := 1) (gap := 1 / 2)
        ((square.swap_fits_iff 3).2 fits) (by norm_num) (by norm_num) (by norm_num) weight
        (by dsimp [PlacedSquare.swap, Point.swap]; linarith)
        (by dsimp [PlacedSquare.swap, Point.swap]; linarith)
        (by simpa [PlacedSquare.swap, Point.swap] using left_strip)
      · exact ⟨0, by decide, (square.swap_contains_iff (keyPoints 0)).1 (by simpa [keyPoints, Point.swap] using left)⟩
      · exact ⟨3, by decide, (square.swap_contains_iff (keyPoints 3)).1 (by convert right using 1; norm_num [keyPoints, Point.swap])⟩
  by_cases bottom_strip : square.center.y ≤ 1
  · obtain left | right := square.contains_bottomPairWith (left := 1) (targetHeight := 1) (gap := 1 / 2)
      fits (by norm_num) (by norm_num) (by norm_num) weight
      (le_of_not_ge left_strip) (by linarith) bottom_strip
    · exact ⟨0, by decide, by simpa [keyPoints] using left⟩
    · exact ⟨1, by decide, by convert right using 1; norm_num [keyPoints]⟩
  have center_x_lower : 1 ≤ square.center.x := le_of_not_ge left_strip
  have center_y_lower : 1 ≤ square.center.y := le_of_not_ge bottom_strip
  by_cases below_diagonal : square.center.x + square.center.y ≤ 5 / 2
  · obtain first | second | third := square.contains_triangleVertex_of_cross_nonnegative
      (keyPoints 0) (keyPoints 1) (keyPoints 3)
      (by norm_num [keyPoints, Point.orientedArea])
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints]) (by norm_num [keyPoints]) (by norm_num [keyPoints])
    · exact ⟨0, by decide, first⟩
    · exact ⟨1, by decide, second⟩
    · exact ⟨3, by decide, third⟩
  · obtain first | second | third := square.contains_triangleVertex_of_cross_nonnegative
      (keyPoints 3) (keyPoints 1) (keyPoints 7)
      (by norm_num [keyPoints, Point.orientedArea])
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints, Point.orientedArea]; linarith)
      (by norm_num [keyPoints]) (by norm_num [keyPoints]) (by norm_num [keyPoints])
    · exact ⟨3, by decide, first⟩
    · exact ⟨1, by decide, second⟩
    · exact ⟨7, by decide, third⟩

theorem perimeter_unavoidable_bottom {square : PlacedSquare}
    (fits : square.Fits 3) (bottom_half : square.center.y ≤ 3 / 2) :
    ∃ index : Fin 9, index ≠ 4 ∧ square.Contains (keyPoints index) := by
  by_cases left_half : square.center.x ≤ 3 / 2
  · exact perimeter_unavoidable_lower_left fits left_half bottom_half
  · obtain ⟨index, not_center, inside⟩ := perimeter_unavoidable_lower_left
      ((square.reflectX_fits_iff 3).2 fits)
      (by dsimp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using bottom_half)
    refine ⟨keyReflectX index, keyReflectX_ne_center not_center, ?_⟩
    rw [keyPoints_reflectX]
    exact (square.reflectX_contains_iff 3 _).1 (by simpa using inside)

theorem perimeter_unavoidable {square : PlacedSquare} (fits : square.Fits 3) :
    ∃ index : Fin 9, index ≠ 4 ∧ square.Contains (keyPoints index) := by
  by_cases bottom_half : square.center.y ≤ 3 / 2
  · exact perimeter_unavoidable_bottom fits bottom_half
  · obtain ⟨index, not_center, inside⟩ := perimeter_unavoidable_bottom
      ((square.reflectY_fits_iff 3).2 fits)
      (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    refine ⟨keyReflectY index, keyReflectY_ne_center not_center, ?_⟩
    rw [keyPoints_reflectY]
    exact (square.reflectY_contains_iff 3 _).1 (by simpa using inside)

noncomputable def extraPoints (index : Fin 8) : Point :=
  match index.val with
  | 0 => ⟨1, 2⟩
  | 1 => ⟨3 / 2, 2⟩
  | 2 => ⟨2, 2⟩
  | 3 => ⟨1, 17 / 10⟩
  | 4 => ⟨2, 17 / 10⟩
  | 5 => ⟨3 / 2, 3 / 2⟩
  | 6 => ⟨1, 9 / 10⟩
  | _ => ⟨2, 9 / 10⟩

def extraReflectX : Fin 8 → Fin 8 := ![2, 1, 0, 4, 3, 5, 7, 6]

theorem extraPoints_reflectX (index : Fin 8) :
    extraPoints (extraReflectX index) = (extraPoints index).reflectX 3 := by
  fin_cases index <;> dsimp [extraPoints, extraReflectX, Point.reflectX] <;> norm_num

theorem extraPoints_triangle {square : PlacedSquare} (first second third : Fin 8)
    (positive : 0 < Point.orientedArea (extraPoints first) (extraPoints second) (extraPoints third))
    (first_side : 0 ≤ Point.orientedArea (extraPoints first) (extraPoints second) square.center)
    (second_side : 0 ≤ Point.orientedArea (extraPoints second) (extraPoints third) square.center)
    (third_side : 0 ≤ Point.orientedArea (extraPoints third) (extraPoints first) square.center)
    (first_second : ((extraPoints first).x - (extraPoints second).x)^2 +
      ((extraPoints first).y - (extraPoints second).y)^2 ≤ 1)
    (first_third : ((extraPoints first).x - (extraPoints third).x)^2 +
      ((extraPoints first).y - (extraPoints third).y)^2 ≤ 1)
    (second_third : ((extraPoints second).x - (extraPoints third).x)^2 +
      ((extraPoints second).y - (extraPoints third).y)^2 ≤ 1) :
    ∃ index : Fin 8, square.Contains (extraPoints index) := by
  obtain first_mem | second_mem | third_mem := square.contains_triangleVertex_of_cross_nonnegative
    (extraPoints first) (extraPoints second) (extraPoints third)
    positive first_side second_side third_side first_second first_third second_third
  · exact ⟨first, first_mem⟩
  · exact ⟨second, second_mem⟩
  · exact ⟨third, third_mem⟩

theorem extraPoints_unavoidable_left {square : PlacedSquare} (fits : square.Fits 3)
    (left_half : square.center.x ≤ 3 / 2) :
    ∃ index : Fin 8, square.Contains (extraPoints index) := by
  by_cases bottom_strip : square.center.y ≤ 9 / 10
  · obtain ⟨column, inside⟩ := square.contains_bottomSpacedRow 1 fits
      (left := 1) (targetHeight := 9 / 10) (by norm_num) (by norm_num)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]) bottom_strip
    fin_cases column
    · exact ⟨6, by simpa [extraPoints] using inside⟩
    · exact ⟨7, by convert inside using 1; norm_num [extraPoints]⟩
  have above_bottom : 9 / 10 ≤ square.center.y := le_of_not_ge bottom_strip
  by_cases top_strip : 2 ≤ square.center.y
  · by_cases left_strip : square.center.x ≤ 1
    · have inside := (square.reflectY 3).contains_unitCorner ((square.reflectY_fits_iff 3).2 fits)
        (by simpa [PlacedSquare.reflectY, Point.reflectY] using left_strip)
        (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      exact ⟨0, (square.reflectY_contains_iff 3 (extraPoints 0)).1 (by convert inside using 1; norm_num [extraPoints, Point.reflectY])⟩
    · obtain left | right := (square.reflectY 3).contains_bottomPairWith (left := 1) (targetHeight := 1) (gap := 1 / 2)
        ((square.reflectY_fits_iff 3).2 fits) (by norm_num) (by norm_num) (by norm_num)
        (fun frame cosine_nonnegative sine_nonnegative => frame.height_add_gap_product_le_sum_of_gap_le_four_fifths
          cosine_nonnegative sine_nonnegative (by norm_num) (by norm_num))
        (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
        (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
        (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      · exact ⟨0, (square.reflectY_contains_iff 3 (extraPoints 0)).1 (by convert left using 1; norm_num [extraPoints, Point.reflectY])⟩
      · exact ⟨1, (square.reflectY_contains_iff 3 (extraPoints 1)).1 (by convert right using 1; norm_num [extraPoints, Point.reflectY])⟩
  have below_top : square.center.y ≤ 2 := le_of_not_ge top_strip
  by_cases left_strip : square.center.x ≤ 1
  · by_cases below_joint : square.center.y ≤ 17 / 10
    · obtain bottom | top := square.swap.contains_bottomPairWith (left := 9 / 10) (targetHeight := 1) (gap := 4 / 5)
        ((square.swap_fits_iff 3).2 fits) (by norm_num) (by norm_num) (by norm_num)
        (fun frame cosine_nonnegative sine_nonnegative => frame.height_add_gap_product_le_sum_of_gap_le_four_fifths
          cosine_nonnegative sine_nonnegative (by norm_num) (by norm_num))
        (by simpa [PlacedSquare.swap, Point.swap] using above_bottom)
        (by dsimp [PlacedSquare.swap, Point.swap]; linarith)
        (by simpa [PlacedSquare.swap, Point.swap] using left_strip)
      · exact ⟨6, (square.swap_contains_iff (extraPoints 6)).1 (by simpa [extraPoints, Point.swap] using bottom)⟩
      · exact ⟨3, (square.swap_contains_iff (extraPoints 3)).1 (by convert top using 1; norm_num [extraPoints, Point.swap])⟩
    · obtain bottom | top := square.swap.contains_bottomPairWith (left := 17 / 10) (targetHeight := 1) (gap := 3 / 10)
        ((square.swap_fits_iff 3).2 fits) (by norm_num) (by norm_num) (by norm_num)
        (fun frame cosine_nonnegative sine_nonnegative => frame.height_add_gap_product_le_sum_of_gap_le_four_fifths
          cosine_nonnegative sine_nonnegative (by norm_num) (by norm_num))
        (by dsimp [PlacedSquare.swap, Point.swap]; linarith)
        (by dsimp [PlacedSquare.swap, Point.swap]; linarith)
        (by simpa [PlacedSquare.swap, Point.swap] using left_strip)
      · exact ⟨3, (square.swap_contains_iff (extraPoints 3)).1 (by simpa [extraPoints, Point.swap] using bottom)⟩
      · exact ⟨0, (square.swap_contains_iff (extraPoints 0)).1 (by convert top using 1; norm_num [extraPoints, Point.swap])⟩
  have horizontal_lower : 1 ≤ square.center.x := le_of_not_ge left_strip
  by_cases first_diagonal : square.center.y ≤ 6 / 5 * square.center.x - 3 / 10
  · apply extraPoints_triangle 6 7 5 <;> norm_num [extraPoints, Point.orientedArea] <;> linarith
  by_cases second_diagonal : square.center.y ≤ 21 / 10 - 2 / 5 * square.center.x
  · apply extraPoints_triangle 6 5 3 <;> norm_num [extraPoints, Point.orientedArea] <;> linarith
  by_cases third_diagonal : square.center.y ≤ 11 / 10 + 3 / 5 * square.center.x
  · apply extraPoints_triangle 3 5 1 <;> norm_num [extraPoints, Point.orientedArea] <;> linarith
  · apply extraPoints_triangle 3 1 0 <;> norm_num [extraPoints, Point.orientedArea] <;> linarith

theorem extraPoints_unavoidable : Unavoidable extraPoints 3 := by
  intro square fits
  by_cases left_half : square.center.x ≤ 3 / 2
  · exact extraPoints_unavoidable_left fits left_half
  · obtain ⟨index, inside⟩ := extraPoints_unavoidable_left ((square.reflectX_fits_iff 3).2 fits)
      (by dsimp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    refine ⟨extraReflectX index, ?_⟩
    rw [extraPoints_reflectX]
    exact (square.reflectX_contains_iff 3 _).1 (by simpa using inside)

end SquarePackingArchive.StromquistSix
