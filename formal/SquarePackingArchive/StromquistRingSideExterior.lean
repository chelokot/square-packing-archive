import SquarePackingArchive.StromquistRingCover
import SquarePackingArchive.StromquistRingOwnership

namespace SquarePackingArchive.Stromquist.TenPoints

set_option maxHeartbeats 1000000 in
lemma contains_bottom_sector
    (square : PlacedSquare) (fits : square.Fits side) (first second : Point)
    (first_x_lower : 1 < first.x) (first_x_upper : first.x < ringCenter.x)
    (second_x_lower : ringCenter.x < second.x) (second_x_upper : second.x < side - 1)
    (first_y_lower : 1 / 2 ≤ first.y) (first_y_upper : first.y ≤ 1)
    (second_y_lower : 1 / 2 ≤ second.y) (second_y_upper : second.y ≤ 1)
    (left_width : first.x - 1 ≤ 4 / 5)
    (middle_width : second.x - first.x ≤ 4 / 5)
    (right_width : side - 1 - second.x ≤ 4 / 5)
    (first_cone : 0 ≤ Point.orientedArea ringCenter first square.center)
    (second_cone : 0 ≤ Point.orientedArea second ringCenter square.center)
    (outside : Point.orientedArea first second square.center ≤ 0) :
    square.Contains ⟨1, 1⟩ ∨ square.Contains first ∨
      square.Contains second ∨ square.Contains ⟨side - 1, 1⟩ := by
  have center_above : 1 < ringCenter.y := by dsimp [ringCenter]; linarith [gap_bounds.1]
  by_cases left_of_first : square.center.x ≤ first.x
  · have center_below_first : square.center.y ≤ first.y := by
      by_contra above
      have vertical_product := mul_neg_of_neg_of_pos
        (show first.x - ringCenter.x < 0 by linarith)
        (show 0 < square.center.y - first.y by linarith)
      have horizontal_product := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ ringCenter.y - first.y by linarith)
        (show square.center.x - first.x ≤ 0 by linarith)
      dsimp [Point.orientedArea] at first_cone
      nlinarith only [vertical_product, horizontal_product, first_cone]
    by_cases left_of_corner : square.center.x ≤ 1
    · exact Or.inl (square.contains_unitCorner fits left_of_corner (by linarith))
    · have below := add_nonneg
        (mul_nonneg (show 0 ≤ first.x - 1 by linarith) (show 0 ≤ first.y - square.center.y by linarith))
        (mul_nonneg (show 0 ≤ 1 - first.y by linarith) (show 0 ≤ first.x - square.center.x by linarith))
      have pair := contains_short_pair (left := 1) (width := first.x - 1)
        (firstHeight := 1) (secondHeight := first.y) fits
        (by linarith) left_width (by norm_num) (by norm_num) first_y_lower first_y_upper
        (by linarith) (by linarith) (by nlinarith only [below])
      rcases pair with corner_inside | first_inside
      · exact Or.inl corner_inside
      · apply Or.inr; apply Or.inl
        convert first_inside using 1; simp
  · by_cases right_of_second : second.x ≤ square.center.x
    · have center_below_second : square.center.y ≤ second.y := by
        by_contra above
        have vertical_product := mul_neg_of_neg_of_pos
          (show ringCenter.x - second.x < 0 by linarith)
          (show 0 < square.center.y - second.y by linarith)
        have horizontal_product := mul_nonneg
          (show 0 ≤ ringCenter.y - second.y by linarith)
          (show 0 ≤ square.center.x - second.x by linarith)
        dsimp [Point.orientedArea] at second_cone
        nlinarith only [vertical_product, horizontal_product, second_cone]
      by_cases right_of_corner : side - 1 ≤ square.center.x
      · apply Or.inr; apply Or.inr; apply Or.inr
        apply (square.reflectX_contains_iff side ⟨side - 1, 1⟩).1
        have corner := (square.reflectX side).contains_unitCorner
          ((square.reflectX_fits_iff side).2 fits)
          (by change side - square.center.x ≤ 1; linarith)
          (by change square.center.y ≤ 1; linarith)
        simpa [Point.reflectX] using corner
      · have below := add_nonneg
          (mul_nonneg (show 0 ≤ side - 1 - second.x by linarith)
            (show 0 ≤ second.y - square.center.y by linarith))
          (mul_nonneg (show 0 ≤ 1 - second.y by linarith)
            (show 0 ≤ square.center.x - second.x by linarith))
        have pair := contains_short_pair (left := second.x) (width := side - 1 - second.x)
          (firstHeight := second.y) (secondHeight := 1) fits
          (by linarith) right_width second_y_lower second_y_upper (by norm_num) (by norm_num)
          right_of_second (by linarith) (by nlinarith only [below])
        rcases pair with second_inside | corner_inside
        · exact Or.inr (Or.inr (Or.inl (by simpa using second_inside)))
        · apply Or.inr; apply Or.inr; apply Or.inr
          convert corner_inside using 1; simp
    · have pair := contains_short_pair (left := first.x) (width := second.x - first.x)
        (firstHeight := first.y) (secondHeight := second.y) fits
        (by linarith) middle_width first_y_lower first_y_upper second_y_lower second_y_upper
        (by linarith) (by linarith)
        (by dsimp [Point.orientedArea] at outside; nlinarith only [outside])
      rcases pair with first_inside | second_inside
      · exact Or.inr (Or.inl (by simpa using first_inside))
      · apply Or.inr; apply Or.inr; apply Or.inl
        convert second_inside using 1; simp

end SquarePackingArchive.Stromquist.TenPoints
