import SquarePackingArchive.StromquistTenBoundary

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def stepTwoPoints (index : Fin 13) : Point :=
  match index.val with
  | 0 => ⟨1, 197 / 250⟩
  | 8 => points 7
  | _ => stepThreePoints index

noncomputable def StepTwoBoundaryRegion (index : Fin 13) (center : Point) : Prop :=
  match index.val with
  | 0 => center.x ≤ 1 ∧ center.y ≤ 197 / 250
  | 4 => 1 ≤ center.x ∧ center.x ≤ 6 / 5 ∧
      (1 / 5) * center.y ≤ 1 / 5 - (53 / 250) * (6 / 5 - center.x)
  | 5 => 6 / 5 ≤ center.x ∧ center.x ≤ 1 + gap ∧
      (gap - 1 / 5) * center.y ≤ gap - 1 / 5 - (3 / 100) * (center.x - 6 / 5)
  | 6 => 1 + gap ≤ center.x ∧ center.x ≤ side - 1 ∧
      gap * center.y ≤ gap - (3 / 100) * (side - center.x - 1)
  | 7 => 197 / 250 ≤ center.y ∧ center.y ≤ side - 49 / 25 ∧
      (side - 687 / 250) * center.x ≤ side - 687 / 250 - (1 / 4) * (center.y - 197 / 250)
  | _ => StepThreeBoundaryRegion index center

set_option maxHeartbeats 1000000 in
lemma stepTwo_triangle_valid (index : Fin 15) :
    let first := stepTwoPoints (stepThreeTriangles index 0)
    let second := stepTwoPoints (stepThreeTriangles index 1)
    let third := stepTwoPoints (stepThreeTriangles index 2)
    0 < Point.orientedArea first second third ∧
      (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2 ≤ 1 ∧
      (first.x - third.x) ^ 2 + (first.y - third.y) ^ 2 ≤ 1 ∧
      (second.x - third.x) ^ 2 + (second.y - third.y) ^ 2 ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;>
    norm_num [stepThreeTriangles, stepTwoPoints, stepThreePoints, points, leftReplacement,
      Point.swap, Point.orientedArea, side, Matrix.cons_val_two]
  all_goals repeat' apply And.intro
  all_goals first | (rw [abs_le]; constructor <;> nlinarith) | nlinarith

lemma stepTwo_hit_triangle (square : PlacedSquare) (index : Fin 15)
    (first_halfplane : 0 ≤ Point.orientedArea
      (stepTwoPoints (stepThreeTriangles index 0))
      (stepTwoPoints (stepThreeTriangles index 1)) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (stepTwoPoints (stepThreeTriangles index 1))
      (stepTwoPoints (stepThreeTriangles index 2)) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (stepTwoPoints (stepThreeTriangles index 2))
      (stepTwoPoints (stepThreeTriangles index 0)) square.center) :
    ∃ pointIndex, square.Contains (stepTwoPoints pointIndex) := by
  exact square.contains_indexed_triangleVertex stepTwoPoints (stepThreeTriangles index)
    (stepTwo_triangle_valid index) first_halfplane second_halfplane third_halfplane

lemma stepTwo_hit_unchanged_boundary (square : PlacedSquare) (fits : square.Fits side)
    (region : Fin 13) (membership : StepThreeBoundaryRegion region square.center)
    (unchanged : region ∈ ({1, 2, 3, 8, 9, 10, 11, 12} : Finset (Fin 13))) :
    ∃ pointIndex, square.Contains (stepTwoPoints pointIndex) := by
  obtain ⟨pointIndex, supported, inside⟩ := stepThree_hit_boundary_supported square fits region membership
  have different := (by decide : ∀ region ∈ ({1, 2, 3, 8, 9, 10, 11, 12} : Finset (Fin 13)),
    ∀ pointIndex ∈ stepThreeBoundarySupport region, pointIndex.val ≠ 0 ∧ pointIndex.val ≠ 8)
    region unchanged pointIndex supported
  refine ⟨pointIndex, ?_⟩
  unfold stepTwoPoints
  split <;> simp_all

set_option maxHeartbeats 1000000 in
theorem stepTwo_hit_boundary (square : PlacedSquare) (fits : square.Fits side)
    (region : Fin 13) (membership : StepTwoBoundaryRegion region square.center) :
    ∃ pointIndex, square.Contains (stepTwoPoints pointIndex) := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  by_cases unchanged : region ∈ ({1, 2, 3, 8, 9, 10, 11, 12} : Finset (Fin 13))
  · apply stepTwo_hit_unchanged_boundary square fits region ?_ unchanged
    have values := (by decide : ∀ region ∈ ({1, 2, 3, 8, 9, 10, 11, 12} : Finset (Fin 13)),
      region.val ≠ 0 ∧ region.val ≠ 4 ∧ region.val ≠ 5 ∧ region.val ≠ 6 ∧ region.val ≠ 7)
      region unchanged
    unfold StepTwoBoundaryRegion at membership
    split at membership <;> simp_all
  · have remaining := (by decide : ∀ region : Fin 13,
      region ∉ ({1, 2, 3, 8, 9, 10, 11, 12} : Finset (Fin 13)) →
      region = 0 ∨ region = 4 ∨ region = 5 ∨ region = 6 ∨ region = 7) region unchanged
    rcases remaining with rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, ?_⟩
      exact square.contains_cornerPoint fits (by norm_num) (by norm_num)
        membership.1 membership.2
    · obtain ⟨center_lower, center_upper, center_below⟩ := membership
      have pair := contains_short_boundary_pair (left := side - 6 / 5) (width := 1 / 5)
        (height := 197 / 250) ((square.reflectX_fits_iff side).2 fits)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by change side - 6 / 5 ≤ side - square.center.x; linarith)
        (by change side - square.center.x ≤ _; linarith)
        (by change (1 / 5) * square.center.y ≤ _; dsimp [PlacedSquare.reflectX, Point.reflectX]; nlinarith only [center_below])
      rcases pair with first | second
      · refine ⟨1, (square.reflectX_contains_iff side (stepTwoPoints 1)).1 ?_⟩
        exact first
      · refine ⟨0, (square.reflectX_contains_iff side (stepTwoPoints 0)).1 ?_⟩
        convert second using 1
        norm_num [stepTwoPoints, Point.reflectX]
        ring
    · obtain ⟨center_lower, center_upper, center_below⟩ := membership
      have pair := contains_short_boundary_pair (left := 6 / 5) (width := gap - 1 / 5)
        (height := 97 / 100) fits
        (by linarith) (by linarith) (by norm_num) (by norm_num)
        center_lower (by linarith) (by nlinarith only [center_below])
      rcases pair with first | second
      · exact ⟨1, first⟩
      · refine ⟨8, ?_⟩
        convert second using 1
        norm_num [stepTwoPoints, points]
        ring
    · obtain ⟨center_lower, center_upper, center_below⟩ := membership
      have pair := lemma4_first (left := 1) ((square.reflectX_fits_iff side).2 fits)
        (by change 1 ≤ side - square.center.x; linarith)
        (by change side - square.center.x ≤ 1 + gap; dsimp [side]; linarith)
        (by simpa [PlacedSquare.reflectX, Point.reflectX, gap, Records.Square5.diagonal] using center_below)
      rcases pair with first | second
      · refine ⟨7, (square.reflectX_contains_iff side (stepTwoPoints 7)).1 ?_⟩
        convert first using 1
        norm_num [stepTwoPoints, stepThreePoints, points, side, Point.reflectX]
      · refine ⟨8, (square.reflectX_contains_iff side (stepTwoPoints 8)).1 ?_⟩
        convert second using 1
        norm_num [stepTwoPoints, points, side, Point.reflectX, gap, Records.Square5.diagonal]
        ring
    · obtain ⟨center_lower, center_upper, center_below⟩ := membership
      have pair := quadrilateral_three_quarters (left := 197 / 250) (width := side - 687 / 250)
        ((square.swap_fits_iff side).2 fits)
        (by dsimp [side]; linarith)
        (by dsimp [side]; nlinarith [gap_square])
        center_lower (by change square.center.y ≤ _; linarith) center_below
      rcases pair with first | second
      · refine ⟨0, (square.swap_contains_iff (stepTwoPoints 0)).1 ?_⟩
        exact first
      · refine ⟨2, (square.swap_contains_iff (stepTwoPoints 2)).1 ?_⟩
        convert second using 1
        norm_num [stepTwoPoints, stepThreePoints, leftReplacement, Point.swap]
        ring

lemma NamedFamily.corner_contains_pair_of_stepTwo_unavoidable
    (family : NamedFamily) (coverage : Unavoidable stepTwoPoints side) :
    (family.squares 0).Contains ⟨1, 197 / 250⟩ ∨
      (family.squares 0).Contains ⟨6 / 5, 1⟩ := by
  have replacement := family.contains_left_replacement (height := side - 49 / 25)
    (by rfl) (by dsimp [side]; linarith [gap_bounds.2])
  have swapped_excluded := family.outer_excludes_swapped_inner_points (owner := 0) (by norm_num)
  obtain ⟨index, inside⟩ := coverage (family.squares 0) (family.fits 0)
  fin_cases index
  · exact Or.inl inside
  · exact Or.inr inside
  · exact False.elim (family.excludes_other (by decide : (0 : Fin 10) ≠ 1) replacement inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 2) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 3) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 4) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 5) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 6) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 7) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 8) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (0 : Fin 10) ≠ 9) inside)
  · exact False.elim (swapped_excluded.1 inside)
  · exact False.elim (swapped_excluded.2 inside)

end SquarePackingArchive.Stromquist.TenPoints
