import SquarePackingArchive.StromquistTenBoundary

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def stepFourPoints (index : Fin 13) : Point :=
  if index.val = 1 then ⟨53 / 25, 9 / 10⟩ else stepThreePoints index

def stepFourTriangles (index : Fin 15) : Fin 3 → Fin 13 :=
  match index.val with
  | 0 => ![9, 3, 2]
  | 1 => ![5, 10, 6]
  | 2 => ![10, 7, 6]
  | 3 => ![0, 9, 2]
  | 4 => ![3, 12, 4]
  | 5 => ![12, 3, 9]
  | 6 => ![12, 5, 4]
  | 7 => ![12, 10, 5]
  | 8 => ![10, 8, 7]
  | 9 => ![8, 1, 7]
  | 10 => ![0, 11, 9]
  | 11 => ![8, 11, 0]
  | 12 => ![11, 8, 10]
  | 13 => ![12, 11, 10]
  | _ => ![11, 12, 9]

def stepFourOldRegion (index : Fin 12) : Fin 13 :=
  ⟨if index.val < 4 then index.val else index.val + 1, by split <;> omega⟩

noncomputable def StepFourBoundaryRegion (index : Fin 12) (center : Point) : Prop :=
  match index.val with
  | 4 => 1 ≤ center.x ∧ center.x ≤ 53 / 25 ∧ center.y ≤ 1 ∧
      5 * center.x + 6 * center.y ≤ 16
  | 5 => 53 / 25 ≤ center.x ∧ center.x ≤ side - 1 ∧
      (side - 78 / 25) * center.y ≤ side - 78 / 25 - (1 / 10) * (side - center.x - 1)
  | _ => StepThreeBoundaryRegion (stepFourOldRegion index) center

noncomputable def LeftSegmentHit (square : PlacedSquare) : Prop :=
  ∃ height, 197 / 250 ≤ height ∧ height ≤ 1 ∧ square.Contains ⟨1, height⟩

noncomputable def RightSegmentHit (square : PlacedSquare) : Prop :=
  ∃ parameter, 0 ≤ parameter ∧ parameter ≤ 1 ∧
    square.Contains ⟨2 + (3 / 25) * parameter, 1 - parameter / 10⟩

noncomputable def StepFourHit (square : PlacedSquare) : Prop :=
  (∃ pointIndex, square.Contains (stepFourPoints pointIndex)) ∨
    LeftSegmentHit square ∨ RightSegmentHit square

set_option maxHeartbeats 1000000 in
lemma stepFour_triangle_valid (index : Fin 15) :
    let first := stepFourPoints (stepFourTriangles index 0)
    let second := stepFourPoints (stepFourTriangles index 1)
    let third := stepFourPoints (stepFourTriangles index 2)
    0 < Point.orientedArea first second third ∧
      (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2 ≤ 1 ∧
      (first.x - third.x) ^ 2 + (first.y - third.y) ^ 2 ≤ 1 ∧
      (second.x - third.x) ^ 2 + (second.y - third.y) ^ 2 ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;>
    norm_num [stepFourTriangles, stepFourPoints, stepThreePoints, points, leftReplacement,
      Point.swap, Point.orientedArea, side, Matrix.cons_val_two]
  all_goals repeat' apply And.intro
  all_goals first | (rw [abs_le]; constructor <;> nlinarith) | nlinarith

lemma stepFour_hit_triangle (square : PlacedSquare) (index : Fin 15)
    (first_halfplane : 0 ≤ Point.orientedArea
      (stepFourPoints (stepFourTriangles index 0))
      (stepFourPoints (stepFourTriangles index 1)) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (stepFourPoints (stepFourTriangles index 1))
      (stepFourPoints (stepFourTriangles index 2)) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (stepFourPoints (stepFourTriangles index 2))
      (stepFourPoints (stepFourTriangles index 0)) square.center) :
    StepFourHit square := by
  exact Or.inl (square.contains_indexed_triangleVertex stepFourPoints (stepFourTriangles index)
    (stepFour_triangle_valid index) first_halfplane second_halfplane third_halfplane)

theorem stepFour_hit_boundary (square : PlacedSquare) (fits : square.Fits side)
    (region : Fin 12) (membership : StepFourBoundaryRegion region square.center) :
    StepFourHit square := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  by_cases pentagon : region.val = 4
  · have region_value : region = 4 := Fin.ext pentagon
    subst region
    exact Or.inr (lemma5 fits membership.1 membership.2.1 membership.2.2.1 membership.2.2.2)
  by_cases bottom_right : region.val = 5
  · have region_value : region = 5 := Fin.ext bottom_right
    subst region
    obtain ⟨center_lower, center_upper, center_below⟩ := membership
    have pair := contains_short_boundary_pair (left := 1) (width := side - 78 / 25)
      (height := 9 / 10) ((square.reflectX_fits_iff side).2 fits)
      (by dsimp [side]; linarith) (by dsimp [side]; linarith)
      (by norm_num) (by norm_num)
      (by change 1 ≤ side - square.center.x; linarith)
      (by change side - square.center.x ≤ _; linarith)
      (by change (side - 78 / 25) * square.center.y ≤ _; dsimp [PlacedSquare.reflectX, Point.reflectX]; nlinarith only [center_below])
    apply Or.inl
    rcases pair with first | second
    · refine ⟨7, (square.reflectX_contains_iff side (stepFourPoints 7)).1 ?_⟩
      convert first using 1
      norm_num [stepFourPoints, stepThreePoints, points, side, Point.reflectX]
    · refine ⟨1, (square.reflectX_contains_iff side (stepFourPoints 1)).1 ?_⟩
      convert second using 1
      norm_num [stepFourPoints, Point.reflectX]
      ring
  · have unchanged_membership : StepThreeBoundaryRegion (stepFourOldRegion region) square.center := by
      unfold StepFourBoundaryRegion at membership
      split at membership <;> simp_all
    obtain ⟨pointIndex, supported, inside⟩ :=
      stepThree_hit_boundary_supported square fits (stepFourOldRegion region) unchanged_membership
    have different := (by decide : ∀ region : Fin 12, region.val ≠ 4 → region.val ≠ 5 →
      ∀ pointIndex ∈ stepThreeBoundarySupport (stepFourOldRegion region), pointIndex.val ≠ 1)
      region pentagon bottom_right pointIndex supported
    exact Or.inl ⟨pointIndex, by simpa only [stepFourPoints, different, ↓reduceIte] using inside⟩

lemma NamedFamily.corner_contains_left_segment
    (family : NamedFamily)
    (corner_low : (family.squares 0).Contains ⟨1, 197 / 250⟩)
    {height : ℝ} (height_lower : 197 / 250 ≤ height) (height_upper : height ≤ 1) :
    (family.squares 0).Contains ⟨1, height⟩ := by
  have contained := PlacedSquare.contains_convexCombination (parameter := (250 * height - 197) / 53)
    (by linarith) (by linarith) corner_low (family.contains_named_point 0)
  convert contained using 1
  norm_num [points]
  ring

lemma NamedFamily.bottom_rightSegment_of_stepFour_cover
    (family : NamedFamily)
    (coverage : ∀ square : PlacedSquare, square.Fits side → StepFourHit square)
    (corner_low : (family.squares 0).Contains ⟨1, 197 / 250⟩) :
    RightSegmentHit (family.squares 7) := by
  have replacement := family.contains_left_replacement (height := side - 49 / 25)
    (by rfl) (by dsimp [side]; linarith [gap_bounds.2])
  have swapped_excluded := family.outer_excludes_swapped_inner_points (owner := 7) (by norm_num)
  rcases coverage (family.squares 7) (family.fits 7) with
    ⟨index, inside⟩ | ⟨height, height_lower, height_upper, inside⟩ | right_inside
  · fin_cases index
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 0) inside)
    · exact ⟨1, by norm_num, by norm_num, by convert inside using 1; norm_num [stepFourPoints]⟩
    · exact False.elim (family.excludes_other (by decide : (7 : Fin 10) ≠ 1) replacement inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 2) inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 3) inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 4) inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 5) inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 6) inside)
    · exact ⟨0, by norm_num, by norm_num, by simpa [stepFourPoints, stepThreePoints] using inside⟩
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 8) inside)
    · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 9) inside)
    · exact False.elim (swapped_excluded.1 inside)
    · exact False.elim (swapped_excluded.2 inside)
  · exact False.elim (family.excludes_other (by decide : (7 : Fin 10) ≠ 0)
      (family.corner_contains_left_segment corner_low height_lower height_upper) inside)
  · exact right_inside

end SquarePackingArchive.Stromquist.TenPoints
