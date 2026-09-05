import SquarePackingArchive.StromquistOwnership

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def leftReplacement (height : ℝ) : Point := ⟨3 / 4, height⟩

lemma quadrilateral_three_quarters
    {square : PlacedSquare} {containerSide left width : ℝ}
    (fits : square.Fits containerSide)
    (width_positive : 0 < width) (width_upper : width ≤ 24 / 25)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below : width * square.center.y ≤ width - (1 / 4) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, 3 / 4⟩ := by
  refine contains_quadrilateral_pair (height := 3 / 4) fits width_positive
    (by norm_num) (by norm_num) (by norm_num; nlinarith) ?_ center_x_lower center_x_upper ?_
  · intro frame cosine_nonnegative sine_nonnegative
    have upper_clearance := weighted_boundary_clearance_second frame cosine_nonnegative sine_nonnegative
    have product := mul_nonneg (show 0 ≤ 24 / 25 - width by linarith)
      (mul_nonneg cosine_nonnegative sine_nonnegative)
    nlinarith only [upper_clearance, product]
  · nlinarith only [center_below]

set_option maxHeartbeats 1000000 in
lemma left_patch_replacement
    {square : PlacedSquare} {height : ℝ}
    (fits : square.Fits side)
    (height_lower : side - 49 / 25 ≤ height)
    (height_upper : height ≤ 49 / 25)
    (center_y_lower : 1 ≤ square.center.y)
    (center_y_upper : square.center.y ≤ 1 + gap)
    (left_of_corner_inner :
      0 ≤ (2 / 5) * (square.center.y - 1) - gap * (square.center.x - 1)) :
    square.Contains (leftReplacement height) ∨
      square.Contains (points 0) ∨ square.Contains (points 8) ∨ square.Contains (points 2) := by
  have gap_lower := gap_bounds.1
  have gap_upper := gap_bounds.2
  have replacement_y_lower : 1 < height := by dsimp [side] at height_lower; linarith
  have replacement_y_upper : height < 1 + 2 * gap := by linarith
  have center_x_upper : square.center.x ≤ 7 / 5 := by nlinarith
  have lower_width_upper : height - 1 ≤ 24 / 25 := by linarith
  have upper_width_upper : 1 + 2 * gap - height ≤ 24 / 25 := by dsimp [side] at height_lower; linarith
  have first_inner_distance :
      ((points 0).x - (points 8).x) ^ 2 + ((points 0).y - (points 8).y) ^ 2 ≤ 1 := by
    norm_num [points]
    nlinarith [gap_square]
  have first_replacement_distance :
      ((points 0).x - (leftReplacement height).x) ^ 2 +
        ((points 0).y - (leftReplacement height).y) ^ 2 ≤ 1 := by
    norm_num [points, leftReplacement]
    nlinarith
  have inner_replacement_distance :
      ((points 8).x - (leftReplacement height).x) ^ 2 +
        ((points 8).y - (leftReplacement height).y) ^ 2 ≤ 1 := by
    norm_num [points, leftReplacement]
    nlinarith [gap_square]
  have upper_replacement_distance :
      ((points 2).x - (leftReplacement height).x) ^ 2 +
        ((points 2).y - (leftReplacement height).y) ^ 2 ≤ 1 := by
    norm_num [points, leftReplacement]
    nlinarith
  have triangle_lower (inner_half_plane :
      0 ≤ Point.orientedArea (points 8) (leftReplacement height) square.center)
      (outer_half_plane :
        0 ≤ Point.orientedArea (leftReplacement height) (points 0) square.center) :
      square.Contains (leftReplacement height) ∨
        square.Contains (points 0) ∨ square.Contains (points 8) ∨ square.Contains (points 2) := by
    have triangle := square.contains_triangleVertex_of_cross_nonnegative
      (points 0) (points 8) (leftReplacement height)
      (by norm_num [points, leftReplacement, Point.orientedArea]; nlinarith)
      (by norm_num [points, Point.orientedArea]; nlinarith)
      inner_half_plane outer_half_plane first_inner_distance
      first_replacement_distance inner_replacement_distance
    rcases triangle with first_inside | inner_inside | replacement_inside
    · exact Or.inr (Or.inl first_inside)
    · exact Or.inr (Or.inr (Or.inl inner_inside))
    · exact Or.inl replacement_inside
  by_cases below_replacement : square.center.y ≤ height
  · by_cases lower_boundary : (height - 1) * square.center.x ≤
        height - 1 - (1 / 4) * (square.center.y - 1)
    · have pair := quadrilateral_three_quarters (left := 1) (width := height - 1)
        ((square.swap_fits_iff side).2 fits)
        (by linarith) lower_width_upper
        (by simpa [PlacedSquare.swap, Point.swap] using center_y_lower)
        (by simp [PlacedSquare.swap, Point.swap]; linarith)
        (by simpa [PlacedSquare.swap, Point.swap] using lower_boundary)
      rcases pair with first_inside | replacement_inside
      · exact Or.inr (Or.inl ((square.swap_contains_iff (points 0)).1
          (by simpa [points, Point.swap] using first_inside)))
      · exact Or.inl ((square.swap_contains_iff (leftReplacement height)).1
          (by convert replacement_inside using 1; simp [leftReplacement, Point.swap]))
    · have center_x_lower : 3 / 4 ≤ square.center.x := by nlinarith
      apply triangle_lower
      · by_cases replacement_below_middle : height ≤ 1 + gap
        · have first_product := mul_nonneg (show 0 ≤ 1 + gap - height by linarith)
            (show 0 ≤ square.center.x - 3 / 4 by linarith)
          have second_product := mul_nonneg (show (0 : ℝ) ≤ 13 / 20 by norm_num)
            (show 0 ≤ height - square.center.y by linarith)
          norm_num [points, leftReplacement, Point.orientedArea]
          nlinarith only [first_product, second_product]
        · have first_product := mul_nonneg (show 0 ≤ height - (1 + gap) by linarith)
            (show 0 ≤ 7 / 5 - square.center.x by linarith)
          have second_product := mul_nonneg (show (0 : ℝ) ≤ 13 / 20 by norm_num)
            (show 0 ≤ 1 + gap - square.center.y by linarith)
          norm_num [points, leftReplacement, Point.orientedArea]
          nlinarith only [first_product, second_product]
      · norm_num [points, leftReplacement, Point.orientedArea]
        nlinarith only [lower_boundary]
  · by_cases upper_boundary : (1 + 2 * gap - height) * square.center.x ≤
        1 + 2 * gap - height - (1 / 4) * (1 + 2 * gap - square.center.y)
    · have reflected_fits := (square.reflectY_fits_iff side).2 fits
      have pair := quadrilateral_three_quarters (left := 1) (width := 1 + 2 * gap - height)
        (((square.reflectY side).swap_fits_iff side).2 reflected_fits)
        (by linarith) upper_width_upper
        (by simp [PlacedSquare.swap, PlacedSquare.reflectY, Point.swap, Point.reflectY, side]; linarith)
        (by simp [PlacedSquare.swap, PlacedSquare.reflectY, Point.swap, Point.reflectY, side]; linarith)
        (by simp [PlacedSquare.swap, PlacedSquare.reflectY, Point.swap, Point.reflectY, side]; nlinarith only [upper_boundary])
      rcases pair with upper_inside | replacement_inside
      · apply Or.inr; apply Or.inr; apply Or.inr
        apply (square.reflectY_contains_iff side (points 2)).1
        apply ((square.reflectY side).swap_contains_iff ((points 2).reflectY side)).1
        convert upper_inside using 1; norm_num [points, side, Point.reflectY, Point.swap]
      · apply Or.inl
        apply (square.reflectY_contains_iff side (leftReplacement height)).1
        apply ((square.reflectY side).swap_contains_iff ((leftReplacement height).reflectY side)).1
        convert replacement_inside using 1
        simp [leftReplacement, side, Point.reflectY, Point.swap]
        ring
    · have center_x_lower : 3 / 4 ≤ square.center.x := by nlinarith
      by_cases above_replacement_inner :
          0 ≤ Point.orientedArea (leftReplacement height) (points 8) square.center
      · have triangle := square.contains_triangleVertex_of_cross_nonnegative
          (leftReplacement height) (points 8) (points 2)
          (by norm_num [points, leftReplacement, Point.orientedArea]; nlinarith)
          above_replacement_inner
          (by
            have first_product := mul_nonneg (show 0 ≤ gap by linarith)
              (show 0 ≤ 7 / 5 - square.center.x by linarith)
            norm_num [points, Point.orientedArea]
            nlinarith)
          (by norm_num [points, leftReplacement, Point.orientedArea]; nlinarith only [upper_boundary])
          (by convert inner_replacement_distance using 1; ring)
          (by convert upper_replacement_distance using 1; ring)
          (by norm_num [points]; nlinarith [gap_square])
        rcases triangle with replacement_inside | inner_inside | upper_inside
        · exact Or.inl replacement_inside
        · exact Or.inr (Or.inr (Or.inl inner_inside))
        · exact Or.inr (Or.inr (Or.inr upper_inside))
      · apply triangle_lower
        · norm_num [points, leftReplacement, Point.orientedArea] at above_replacement_inner ⊢
          nlinarith only [above_replacement_inner]
        · have first_product := mul_nonneg (show 0 ≤ height - 1 by linarith)
            (show 0 ≤ square.center.x - 3 / 4 by linarith)
          have second_product := mul_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
            (show 0 ≤ square.center.y - height by linarith)
          norm_num [points, leftReplacement, Point.orientedArea]
          nlinarith only [first_product, second_product]

lemma lower_half_left_replacement
    {square : PlacedSquare} {height : ℝ}
    (fits : square.Fits side)
    (height_lower : side - 49 / 25 ≤ height)
    (height_upper : height ≤ 49 / 25)
    (center_y_upper : square.center.y ≤ 1 + gap) :
    square.Contains (leftReplacement height) ∨
      ∃ index, index ≠ 1 ∧ square.Contains (points index) := by
  by_cases center_x_upper : square.center.x ≤ 1 + gap
  · obtain ⟨index, _, inside, location⟩ :=
      lower_left_unavoidable_supported fits center_x_upper center_y_upper
    by_cases is_left : index = 1
    · obtain ⟨center_y_lower, left_of_inner⟩ := location is_left
      rcases left_patch_replacement fits height_lower height_upper
        center_y_lower center_y_upper left_of_inner with replacement | first | inner | upper
      · exact Or.inl replacement
      · exact Or.inr ⟨0, by decide, first⟩
      · exact Or.inr ⟨8, by decide, inner⟩
      · exact Or.inr ⟨2, by decide, upper⟩
    · exact Or.inr ⟨index, is_left, inside⟩
  · obtain ⟨index, supported, inside, _⟩ := lower_left_unavoidable_supported
      ((square.reflectX_fits_iff side).2 fits)
      (by simp [PlacedSquare.reflectX, Point.reflectX, side]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    refine Or.inr ⟨mirrorHorizontal index, ?_, ?_⟩
    · exact (by decide : ∀ index ∈ quarterSupport, mirrorHorizontal index ≠ 1) index supported
    · apply (square.reflectX_contains_iff side (points (mirrorHorizontal index))).1
      rw [points_mirrorHorizontal, Point.reflectX_reflectX]
      exact inside

theorem left_replacement_unavoidable
    {height : ℝ}
    (height_lower : side - 49 / 25 ≤ height)
    (height_upper : height ≤ 49 / 25)
    (square : PlacedSquare) (fits : square.Fits side) :
    square.Contains (leftReplacement height) ∨
      ∃ index, index ≠ 1 ∧ square.Contains (points index) := by
  by_cases center_y_upper : square.center.y ≤ 1 + gap
  · exact lower_half_left_replacement fits height_lower height_upper center_y_upper
  · have reflected := lower_half_left_replacement (height := side - height)
      ((square.reflectY_fits_iff side).2 fits)
      (by linarith) (by linarith)
      (by simp [PlacedSquare.reflectY, Point.reflectY, side]; linarith)
    rcases reflected with replacement | ⟨index, different, inside⟩
    · apply Or.inl
      apply (square.reflectY_contains_iff side (leftReplacement height)).1
      simpa [leftReplacement, Point.reflectY] using replacement
    · refine Or.inr ⟨mirrorVertical index, ?_, ?_⟩
      · intro equality
        exact different ((by decide : ∀ index, mirrorVertical index = 1 → index = 1) index equality)
      · apply (square.reflectY_contains_iff side (points (mirrorVertical index))).1
        rw [points_mirrorVertical, Point.reflectY_reflectY]
        exact inside

theorem NamedFamily.contains_left_replacement
    (family : NamedFamily) {height : ℝ}
    (height_lower : side - 49 / 25 ≤ height)
    (height_upper : height ≤ 49 / 25) :
    (family.squares 1).Contains (leftReplacement height) :=
  family.owns_replacement 1 (leftReplacement height)
    (left_replacement_unavoidable height_lower height_upper)

end SquarePackingArchive.Stromquist.TenPoints
