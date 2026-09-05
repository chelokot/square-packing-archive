import SquarePackingArchive.StromquistTenReplacementPoints

namespace SquarePackingArchive.Stromquist.TenPoints

def stepThreeBoundarySupport (index : Fin 13) : Finset (Fin 13) :=
  match index.val with
  | 0 => {0}
  | 1 => {7}
  | 2 => {5}
  | 3 => {3}
  | 4 => {0, 1}
  | 5 => {1, 8}
  | 6 => {8, 7}
  | 7 => {0, 2}
  | 8 => {3, 2}
  | 9 => {3, 4}
  | 10 => {5, 4}
  | 11 => {7, 6}
  | _ => {5, 6}

noncomputable def StepThreeBoundaryRegion (index : Fin 13) (center : Point) : Prop :=
  match index.val with
  | 0 => center.x ≤ 1 ∧ center.y ≤ 1
  | 1 => side - 1 ≤ center.x ∧ center.y ≤ 1
  | 2 => side - 1 ≤ center.x ∧ side - 1 ≤ center.y
  | 3 => center.x ≤ 1 ∧ side - 1 ≤ center.y
  | 4 => 1 ≤ center.x ∧ center.x ≤ 6 / 5 ∧ center.y ≤ 1
  | 5 => 6 / 5 ≤ center.x ∧ center.x ≤ 2 ∧ center.y ≤ 1
  | 6 => 2 ≤ center.x ∧ center.x ≤ side - 1 ∧ center.y ≤ 1
  | 7 => 1 ≤ center.y ∧ center.y ≤ side - 49 / 25 ∧
      (side - 74 / 25) * center.x ≤ side - 74 / 25 - (1 / 4) * (center.y - 1)
  | 8 => side - 49 / 25 ≤ center.y ∧ center.y ≤ side - 1 ∧
      (24 / 25) * center.x ≤ 24 / 25 - (1 / 4) * (side - 1 - center.y)
  | 9 => 1 ≤ center.x ∧ center.x ≤ 1 + gap ∧
      gap * (side - center.y) ≤ gap - (3 / 100) * (center.x - 1)
  | 10 => 1 + gap ≤ center.x ∧ center.x ≤ side - 1 ∧
      gap * (side - center.y) ≤ gap - (3 / 100) * (side - center.x - 1)
  | 11 => 1 ≤ center.y ∧ center.y ≤ 1 + gap ∧
      gap * (side - center.x) ≤ gap - (3 / 100) * (center.y - 1)
  | _ => 1 + gap ≤ center.y ∧ center.y ≤ side - 1 ∧
      gap * (side - center.x) ≤ gap - (3 / 100) * (side - center.y - 1)

lemma contains_short_boundary_pair
    {square : PlacedSquare} {containerSide left width height : ℝ}
    (fits : square.Fits containerSide)
    (width_positive : 0 < width) (width_upper : width ≤ 4 / 5)
    (height_lower : 1 / 2 ≤ height) (height_upper : height ≤ 1)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below : width * square.center.y ≤ width + (height - 1) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, height⟩ := by
  refine contains_quadrilateral_pair fits width_positive
    height_lower height_upper (by nlinarith) ?_
    center_x_lower center_x_upper ?_
  · intro frame cosine_nonnegative sine_nonnegative
    have clearance := boundary_chord_clearance frame cosine_nonnegative sine_nonnegative
    have product := mul_nonneg (show 0 ≤ 207 / 250 - width by linarith)
      (mul_nonneg cosine_nonnegative sine_nonnegative)
    have height_product := mul_nonneg (show 0 ≤ 1 - height by linarith) (sq_nonneg frame.sine)
    nlinarith [frame.unit]
  · exact center_below

lemma contains_bottom_pair
    {square : PlacedSquare} {containerSide left width : ℝ}
    (fits : square.Fits containerSide)
    (width_positive : 0 < width) (width_upper : width ≤ 4 / 5)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_y_upper : square.center.y ≤ 1) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, 1⟩ := by
  refine contains_short_boundary_pair fits width_positive width_upper
    (by norm_num) (by norm_num) center_x_lower center_x_upper ?_
  norm_num
  nlinarith [mul_nonneg (le_of_lt width_positive) (show 0 ≤ 1 - square.center.y by linarith)]

lemma stepThree_hit_boundary_corner (square : PlacedSquare) (fits : square.Fits side)
    (index : Fin 4) (membership : StepThreeBoundaryRegion (index.castLE (by decide)) square.center) :
    ∃ pointIndex ∈ stepThreeBoundarySupport (index.castLE (by decide)),
      square.Contains (stepThreePoints pointIndex) := by
  fin_cases index
  · refine ⟨0, by decide, ?_⟩
    exact square.contains_unitCorner fits membership.1 membership.2
  · refine ⟨7, by decide, ?_⟩
    apply (square.reflectX_contains_iff side (stepThreePoints 7)).1
    have corner := (square.reflectX side).contains_unitCorner
      ((square.reflectX_fits_iff side).2 fits)
      (by change side - square.center.x ≤ 1; change side - 1 ≤ square.center.x ∧ _ at membership; linarith [membership.1])
      membership.2
    convert corner using 1
    norm_num [stepThreePoints, points, side, Point.reflectX]
  · refine ⟨5, by decide, ?_⟩
    apply (square.reflectX_contains_iff side (stepThreePoints 5)).1
    apply ((square.reflectX side).reflectY_contains_iff side ((stepThreePoints 5).reflectX side)).1
    have corner := ((square.reflectX side).reflectY side).contains_unitCorner
      ((((square.reflectX side).reflectY_fits_iff side).2 ((square.reflectX_fits_iff side).2 fits)))
      (by change side - square.center.x ≤ 1; change side - 1 ≤ square.center.x ∧ _ at membership; linarith [membership.1])
      (by change side - square.center.y ≤ 1; change _ ∧ side - 1 ≤ square.center.y at membership; linarith [membership.2])
    convert corner using 1
    norm_num [stepThreePoints, points, side, Point.reflectX, Point.reflectY]
  · refine ⟨3, by decide, ?_⟩
    apply (square.reflectY_contains_iff side (stepThreePoints 3)).1
    have corner := (square.reflectY side).contains_unitCorner
      ((square.reflectY_fits_iff side).2 fits) membership.1
      (by change side - square.center.y ≤ 1; change _ ∧ side - 1 ≤ square.center.y at membership; linarith [membership.2])
    convert corner using 1
    norm_num [stepThreePoints, points, side, Point.reflectY]

set_option maxHeartbeats 1000000 in
theorem stepThree_hit_boundary_supported (square : PlacedSquare) (fits : square.Fits side)
    (region : Fin 13) (membership : StepThreeBoundaryRegion region square.center) :
    ∃ pointIndex ∈ stepThreeBoundarySupport region,
      square.Contains (stepThreePoints pointIndex) := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  fin_cases region
  · exact stepThree_hit_boundary_corner square fits 0 membership
  · exact stepThree_hit_boundary_corner square fits 1 membership
  · exact stepThree_hit_boundary_corner square fits 2 membership
  · exact stepThree_hit_boundary_corner square fits 3 membership
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    rcases contains_bottom_pair (left := 1) (width := 1 / 5) fits
      (by norm_num) (by norm_num) center_lower (by linarith) center_below with first | second
    · exact ⟨0, by decide, first⟩
    · exact ⟨1, by decide, by convert second using 1; norm_num [stepThreePoints]⟩
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    rcases contains_bottom_pair (left := 6 / 5) (width := 4 / 5) fits
      (by norm_num) (by norm_num) center_lower (by linarith) center_below with first | second
    · exact ⟨1, by decide, first⟩
    · exact ⟨8, by decide, by convert second using 1; norm_num [stepThreePoints]⟩
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    rcases contains_bottom_pair (left := 2) (width := side - 3) fits
      (by dsimp [side]; linarith) (by dsimp [side]; linarith)
      center_lower (by linarith) center_below with first | second
    · exact ⟨8, by decide, first⟩
    · exact ⟨7, by decide, by convert second using 1; norm_num [stepThreePoints, points, side]; ring⟩
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := quadrilateral_three_quarters (left := 1) (width := side - 74 / 25)
      ((square.swap_fits_iff side).2 fits)
      (by dsimp [side]; linarith) (by dsimp [side]; linarith)
      center_lower (by change square.center.y ≤ _; linarith) center_below
    rcases pair with first | second
    · refine ⟨0, by decide, (square.swap_contains_iff (stepThreePoints 0)).1 ?_⟩
      exact first
    · refine ⟨2, by decide, (square.swap_contains_iff (stepThreePoints 2)).1 ?_⟩
      convert second using 1; norm_num [stepThreePoints, leftReplacement, Point.swap]; ring
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := quadrilateral_three_quarters (left := 1) (width := 24 / 25)
      (((square.reflectY side).swap_fits_iff side).2 ((square.reflectY_fits_iff side).2 fits))
      (by norm_num) (by norm_num)
      (by change 1 ≤ side - square.center.y; linarith)
      (by change side - square.center.y ≤ _; linarith)
      (by change (24 / 25) * square.center.x ≤ 24 / 25 - (1 / 4) * (side - square.center.y - 1); linarith)
    rcases pair with first | second
    · refine ⟨3, by decide, (square.reflectY_contains_iff side (stepThreePoints 3)).1 ?_⟩
      apply ((square.reflectY side).swap_contains_iff _).1
      convert first using 1; norm_num [stepThreePoints, points, side, Point.swap, Point.reflectY]
    · refine ⟨2, by decide, (square.reflectY_contains_iff side (stepThreePoints 2)).1 ?_⟩
      apply ((square.reflectY side).swap_contains_iff _).1
      convert second using 1; norm_num [stepThreePoints, leftReplacement, Point.swap, Point.reflectY]
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := lemma4_first (left := 1) ((square.reflectY_fits_iff side).2 fits)
      center_lower (by simpa [PlacedSquare.reflectY, Point.reflectY, gap, Records.Square5.diagonal] using center_upper)
      (by simpa [PlacedSquare.reflectY, Point.reflectY, gap, Records.Square5.diagonal] using center_below)
    rcases pair with first | second
    · refine ⟨3, by decide, (square.reflectY_contains_iff side (stepThreePoints 3)).1 ?_⟩
      convert first using 1; norm_num [stepThreePoints, points, side, Point.reflectY]
    · refine ⟨4, by decide, (square.reflectY_contains_iff side (stepThreePoints 4)).1 ?_⟩
      convert second using 1; norm_num [stepThreePoints, points, side, Point.reflectY, gap, Records.Square5.diagonal]
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := lemma4_first (left := 1)
      (((square.reflectX side).reflectY_fits_iff side).2 ((square.reflectX_fits_iff side).2 fits))
      (by change 1 ≤ side - square.center.x; linarith)
      (by change side - square.center.x ≤ 1 + gap; dsimp [side]; linarith)
      (by simpa [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY, gap, Records.Square5.diagonal] using center_below)
    rcases pair with first | second
    · refine ⟨5, by decide, (square.reflectX_contains_iff side (stepThreePoints 5)).1 ?_⟩
      apply ((square.reflectX side).reflectY_contains_iff side _).1
      convert first using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.reflectY]
    · refine ⟨4, by decide, (square.reflectX_contains_iff side (stepThreePoints 4)).1 ?_⟩
      apply ((square.reflectX side).reflectY_contains_iff side _).1
      convert second using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.reflectY, gap, Records.Square5.diagonal]; ring
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := lemma4_first (left := 1)
      (((square.reflectX side).swap_fits_iff side).2 ((square.reflectX_fits_iff side).2 fits))
      center_lower
      (by simpa [PlacedSquare.reflectX, PlacedSquare.swap, Point.reflectX, Point.swap, gap, Records.Square5.diagonal] using center_upper)
      (by simpa [PlacedSquare.reflectX, PlacedSquare.swap, Point.reflectX, Point.swap, gap, Records.Square5.diagonal] using center_below)
    rcases pair with first | second
    · refine ⟨7, by decide, (square.reflectX_contains_iff side (stepThreePoints 7)).1 ?_⟩
      apply ((square.reflectX side).swap_contains_iff _).1
      convert first using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.swap]
    · refine ⟨6, by decide, (square.reflectX_contains_iff side (stepThreePoints 6)).1 ?_⟩
      apply ((square.reflectX side).swap_contains_iff _).1
      convert second using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.swap, gap, Records.Square5.diagonal]
  · obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := lemma4_first (left := 1)
      ((((square.reflectX side).reflectY side).swap_fits_iff side).2
        (((square.reflectX side).reflectY_fits_iff side).2 ((square.reflectX_fits_iff side).2 fits)))
      (by change 1 ≤ side - square.center.y; linarith)
      (by change side - square.center.y ≤ 1 + gap; dsimp [side]; linarith)
      (by simpa [PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap, Point.reflectX, Point.reflectY, Point.swap, gap, Records.Square5.diagonal] using center_below)
    rcases pair with first | second
    · refine ⟨5, by decide, (square.reflectX_contains_iff side (stepThreePoints 5)).1 ?_⟩
      apply ((square.reflectX side).reflectY_contains_iff side _).1
      apply (((square.reflectX side).reflectY side).swap_contains_iff _).1
      convert first using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.reflectY, Point.swap]
    · refine ⟨6, by decide, (square.reflectX_contains_iff side (stepThreePoints 6)).1 ?_⟩
      apply ((square.reflectX side).reflectY_contains_iff side _).1
      apply (((square.reflectX side).reflectY side).swap_contains_iff _).1
      convert second using 1; norm_num [stepThreePoints, points, side, Point.reflectX, Point.reflectY, Point.swap, gap, Records.Square5.diagonal]; ring

theorem stepThree_hit_boundary (square : PlacedSquare) (fits : square.Fits side)
    (region : Fin 13) (membership : StepThreeBoundaryRegion region square.center) :
    ∃ pointIndex, square.Contains (stepThreePoints pointIndex) := by
  obtain ⟨pointIndex, _, inside⟩ := stepThree_hit_boundary_supported square fits region membership
  exact ⟨pointIndex, inside⟩

end SquarePackingArchive.Stromquist.TenPoints
