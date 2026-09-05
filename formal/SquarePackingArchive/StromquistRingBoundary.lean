import SquarePackingArchive.StromquistTenBoundary

namespace SquarePackingArchive

lemma PlacedSquare.translate_up_fits
    {square : PlacedSquare} {side offset : ℝ}
    (fits : square.Fits side) (offset_nonnegative : 0 ≤ offset) :
    (square.translate 0 offset).Fits (side + offset) := by
  intro point inside
  have original_inside : square.Contains (point.translate 0 (-offset)) := by
    apply (square.translate_contains_iff 0 offset (point.translate 0 (-offset))).1
    simpa [Point.translate] using inside
  have bounds := fits original_inside
  dsimp [Container.Contains, Point.translate] at bounds ⊢
  exact ⟨by linarith [bounds.1], by linarith [bounds.2.1],
    by linarith [bounds.2.2.1], by linarith [bounds.2.2.2]⟩

namespace Stromquist.TenPoints

lemma contains_short_descending_pair
    {square : PlacedSquare} {containerSide left width firstHeight secondHeight : ℝ}
    (fits : square.Fits containerSide)
    (width_positive : 0 < width) (width_upper : width ≤ 4 / 5)
    (second_height_lower : 1 / 2 ≤ secondHeight)
    (height_order : secondHeight ≤ firstHeight) (first_height_upper : firstHeight ≤ 1)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below : width * square.center.y ≤
      width * firstHeight + (secondHeight - firstHeight) * (square.center.x - left)) :
    square.Contains ⟨left, firstHeight⟩ ∨ square.Contains ⟨left + width, secondHeight⟩ := by
  have pair := contains_short_boundary_pair (left := left) (width := width)
    (height := secondHeight + (1 - firstHeight))
    (square.translate_up_fits fits (show 0 ≤ 1 - firstHeight by linarith))
    width_positive width_upper (by linarith) (by linarith)
    (by simpa [PlacedSquare.translate, Point.translate] using center_x_lower)
    (by simpa [PlacedSquare.translate, Point.translate] using center_x_upper)
    (by dsimp [PlacedSquare.translate, Point.translate]; nlinarith only [center_below])
  rcases pair with first | second
  · apply Or.inl
    apply (square.translate_contains_iff 0 (1 - firstHeight) ⟨left, firstHeight⟩).1
    simpa [Point.translate] using first
  · apply Or.inr
    apply (square.translate_contains_iff 0 (1 - firstHeight) ⟨left + width, secondHeight⟩).1
    simpa [Point.translate] using second

theorem contains_short_pair
    {square : PlacedSquare} {containerSide left width firstHeight secondHeight : ℝ}
    (fits : square.Fits containerSide)
    (width_positive : 0 < width) (width_upper : width ≤ 4 / 5)
    (first_height_lower : 1 / 2 ≤ firstHeight) (first_height_upper : firstHeight ≤ 1)
    (second_height_lower : 1 / 2 ≤ secondHeight) (second_height_upper : secondHeight ≤ 1)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below : width * square.center.y ≤
      width * firstHeight + (secondHeight - firstHeight) * (square.center.x - left)) :
    square.Contains ⟨left, firstHeight⟩ ∨ square.Contains ⟨left + width, secondHeight⟩ := by
  by_cases height_order : secondHeight ≤ firstHeight
  · exact contains_short_descending_pair fits width_positive width_upper second_height_lower
      height_order first_height_upper center_x_lower center_x_upper center_below
  · have pair := contains_short_descending_pair
      (left := containerSide - left - width) (width := width)
      (firstHeight := secondHeight) (secondHeight := firstHeight)
      ((square.reflectX_fits_iff containerSide).2 fits)
      width_positive width_upper first_height_lower (by linarith) second_height_upper
      (by change containerSide - left - width ≤ containerSide - square.center.x; linarith)
      (by change containerSide - square.center.x ≤ _; linarith)
      (by dsimp [PlacedSquare.reflectX, Point.reflectX]; nlinarith only [center_below])
    rcases pair with first | second
    · apply Or.inr
      apply (square.reflectX_contains_iff containerSide ⟨left + width, secondHeight⟩).1
      convert first using 1
      simp [Point.reflectX]
      ring
    · apply Or.inl
      apply (square.reflectX_contains_iff containerSide ⟨left, firstHeight⟩).1
      convert second using 1
      simp [Point.reflectX]

end Stromquist.TenPoints

end SquarePackingArchive
