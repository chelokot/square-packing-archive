import SquarePackingArchive.Stromquist
import SquarePackingArchive.TriangleRegions

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def gap : ℝ := (1 + Records.Square5.diagonal) / 2

noncomputable def side : ℝ := 2 + 2 * gap

noncomputable def points (index : Fin 10) : Point :=
  match index.val with
  | 0 => ⟨1, 1⟩
  | 1 => ⟨97 / 100, 1 + gap⟩
  | 2 => ⟨1, 1 + 2 * gap⟩
  | 3 => ⟨1 + gap, 103 / 100 + 2 * gap⟩
  | 4 => ⟨1 + 2 * gap, 1 + 2 * gap⟩
  | 5 => ⟨103 / 100 + 2 * gap, 1 + gap⟩
  | 6 => ⟨1 + 2 * gap, 1⟩
  | 7 => ⟨1 + gap, 97 / 100⟩
  | 8 => ⟨7 / 5, 1 + gap⟩
  | _ => ⟨3 / 5 + 2 * gap, 1 + gap⟩

lemma gap_bounds : 17 / 20 ≤ gap ∧ gap ≤ 43 / 50 := by
  have diagonal_positive := Records.Square5.diagonal_positive
  have diagonal_square := Records.Square5.diagonal_sq
  dsimp [gap]
  constructor <;> nlinarith

lemma gap_square : (2 * gap - 1) ^ 2 = 1 / 2 := by
  dsimp [gap]
  nlinarith [Records.Square5.diagonal_sq]

def quarterSupport : Finset (Fin 10) := {0, 1, 7, 8, 9}

set_option maxHeartbeats 1000000 in
lemma lower_left_unavoidable_supported
    {square : PlacedSquare}
    (fits : square.Fits side)
    (center_x_upper : square.center.x ≤ 1 + gap)
    (center_y_upper : square.center.y ≤ 1 + gap) :
    ∃ index ∈ quarterSupport, square.Contains (points index) ∧
      (index = 1 → 1 ≤ square.center.y ∧
        0 ≤ (2 / 5) * (square.center.y - 1) - gap * (square.center.x - 1)) := by
  have gap_lower := gap_bounds.1
  have gap_upper := gap_bounds.2
  by_cases above_corner_inner :
      (2 / 5) * (square.center.y - 1) - gap * (square.center.x - 1) ≥ 0
  · by_cases center_y_low : square.center.y ≤ 1
    · have center_x_low : square.center.x ≤ 1 := by nlinarith
      exact ⟨0, by norm_num [quarterSupport], by simpa [points] using square.contains_unitCorner fits center_x_low center_y_low, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
    · have center_y_lower : 1 ≤ square.center.y := by linarith
      by_cases left_boundary : gap * square.center.x ≤
          gap - (3 / 100) * (square.center.y - 1)
      · have pair := lemma4_first (left := 1) ((square.swap_fits_iff side).2 fits)
          (by simpa [PlacedSquare.swap, Point.swap] using center_y_lower)
          (by simpa [PlacedSquare.swap, Point.swap, gap, Records.Square5.diagonal] using center_y_upper)
          (by simpa [PlacedSquare.swap, Point.swap, gap, Records.Square5.diagonal] using left_boundary)
        rcases pair with corner_inside | side_inside
        · exact ⟨0, by norm_num [quarterSupport], (square.swap_contains_iff (points 0)).1 (by simpa [points, Point.swap] using corner_inside), by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
        · exact ⟨1, by norm_num [quarterSupport], (square.swap_contains_iff (points 1)).1 (by
            simpa [points, Point.swap, gap, Records.Square5.diagonal] using side_inside), by intro _; exact ⟨center_y_lower, above_corner_inner⟩⟩
      · have triangle := square.contains_triangleVertex_of_cross_nonnegative
          (points 0) (points 8) (points 1)
          (by norm_num [points, Point.orientedArea]; nlinarith)
          (by norm_num [points, Point.orientedArea]; nlinarith)
          (by norm_num [points, Point.orientedArea]; nlinarith)
          (by norm_num [points, Point.orientedArea]; nlinarith)
          (by norm_num [points]; nlinarith [gap_square])
          (by norm_num [points]; nlinarith [gap_square])
          (by norm_num [points])
        rcases triangle with corner_inside | inner_inside | side_inside
        · exact ⟨0, by norm_num [quarterSupport], corner_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
        · exact ⟨8, by norm_num [quarterSupport], inner_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
        · exact ⟨1, by norm_num [quarterSupport], side_inside, by intro _; exact ⟨center_y_lower, above_corner_inner⟩⟩
  · by_cases center_x_low : square.center.x ≤ 1
    · have center_y_low : square.center.y ≤ 1 := by nlinarith
      exact ⟨0, by norm_num [quarterSupport], by simpa [points] using square.contains_unitCorner fits center_x_low center_y_low, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
    · have center_x_lower : 1 ≤ square.center.x := by linarith
      by_cases bottom_boundary : gap * square.center.y ≤
          gap - (3 / 100) * (square.center.x - 1)
      · have pair := lemma4_first (left := 1) fits center_x_lower
          (by simpa [gap, Records.Square5.diagonal] using center_x_upper)
          (by simpa [gap, Records.Square5.diagonal] using bottom_boundary)
        rcases pair with corner_inside | side_inside
        · exact ⟨0, by norm_num [quarterSupport], by simpa [points] using corner_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
        · exact ⟨7, by norm_num [quarterSupport], by simpa [points, gap, Records.Square5.diagonal] using side_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
      · by_cases left_of_inner_edge :
          (2 / 5 - gap) * (square.center.y - 97 / 100) -
            (gap + 3 / 100) * (square.center.x - (1 + gap)) ≥ 0
        · have triangle := square.contains_triangleVertex_of_cross_nonnegative
            (points 0) (points 7) (points 8)
            (by norm_num [points, Point.orientedArea]; nlinarith [gap_square])
            (by norm_num [points, Point.orientedArea]; nlinarith)
            (by norm_num [points, Point.orientedArea]; nlinarith)
            (by norm_num [points, Point.orientedArea]; nlinarith)
            (by norm_num [points]; nlinarith [gap_square])
            (by norm_num [points]; nlinarith [gap_square])
            (by norm_num [points]; nlinarith [gap_square])
          rcases triangle with corner_inside | side_inside | inner_inside
          · exact ⟨0, by norm_num [quarterSupport], corner_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
          · exact ⟨7, by norm_num [quarterSupport], side_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
          · exact ⟨8, by norm_num [quarterSupport], inner_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
        · have center_y_lower : 97 / 100 ≤ square.center.y := by nlinarith
          have triangle := square.contains_triangleVertex_of_cross_nonnegative
            (points 8) (points 7) (points 9)
            (by norm_num [points, Point.orientedArea]; nlinarith [gap_square])
            (by norm_num [points, Point.orientedArea]; nlinarith)
            (by
              have first_product := mul_nonneg
                (show 0 ≤ gap - 2 / 5 by linarith)
                (show 0 ≤ square.center.y - 97 / 100 by linarith)
              have second_product := mul_nonpos_of_nonneg_of_nonpos
                (show 0 ≤ gap + 3 / 100 by linarith)
                (show square.center.x - (1 + gap) ≤ 0 by linarith)
              norm_num [points, Point.orientedArea]
              nlinarith only [first_product, second_product])
            (by
              have product := mul_nonneg
                (show 0 ≤ 2 * gap - 4 / 5 by linarith)
                (show 0 ≤ 1 + gap - square.center.y by linarith)
              norm_num [points, Point.orientedArea]
              nlinarith only [product])
            (by norm_num [points]; nlinarith [gap_square])
            (by norm_num [points]; rw [abs_le]; constructor <;> linarith)
            (by norm_num [points]; nlinarith [gap_square])
          rcases triangle with left_inside | side_inside | right_inside
          · exact ⟨8, by norm_num [quarterSupport], left_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
          · exact ⟨7, by norm_num [quarterSupport], side_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩
          · exact ⟨9, by norm_num [quarterSupport], right_inside, by intro equality; have contradiction := congrArg Fin.val equality; norm_num at contradiction⟩

lemma lower_left_unavoidable
    {square : PlacedSquare}
    (fits : square.Fits side)
    (center_x_upper : square.center.x ≤ 1 + gap)
    (center_y_upper : square.center.y ≤ 1 + gap) :
    ∃ index, square.Contains (points index) := by
  obtain ⟨index, _, inside, _⟩ := lower_left_unavoidable_supported fits center_x_upper center_y_upper
  exact ⟨index, inside⟩

def mirrorHorizontal : Fin 10 → Fin 10 := ![6, 5, 4, 3, 2, 1, 0, 7, 9, 8]

def mirrorVertical : Fin 10 → Fin 10 := ![2, 1, 0, 7, 6, 5, 4, 3, 8, 9]

lemma points_mirrorHorizontal (index : Fin 10) :
    points (mirrorHorizontal index) = (points index).reflectX side := by
  fin_cases index <;>
    simp [mirrorHorizontal, points, side, Point.reflectX, Point.mk.injEq] <;>
    ring

lemma points_mirrorVertical (index : Fin 10) :
    points (mirrorVertical index) = (points index).reflectY side := by
  fin_cases index <;>
    simp [mirrorVertical, points, side, Point.reflectY, Point.mk.injEq] <;>
    ring

lemma lower_half_unavoidable
    {square : PlacedSquare} (fits : square.Fits side)
    (center_y_upper : square.center.y ≤ 1 + gap) :
    ∃ index, square.Contains (points index) := by
  by_cases center_x_upper : square.center.x ≤ 1 + gap
  · exact lower_left_unavoidable fits center_x_upper center_y_upper
  · have reflected_fits := (square.reflectX_fits_iff side).2 fits
    obtain ⟨index, inside⟩ := lower_left_unavoidable reflected_fits
      (by simp [PlacedSquare.reflectX, Point.reflectX, side]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    refine ⟨mirrorHorizontal index, ?_⟩
    apply (square.reflectX_contains_iff side (points (mirrorHorizontal index))).1
    rw [points_mirrorHorizontal, Point.reflectX_reflectX]
    exact inside

theorem unavoidable : Unavoidable points side := by
  intro square fits
  by_cases center_y_upper : square.center.y ≤ 1 + gap
  · exact lower_half_unavoidable fits center_y_upper
  · have reflected_fits := (square.reflectY_fits_iff side).2 fits
    obtain ⟨index, inside⟩ := lower_half_unavoidable reflected_fits
      (by simp [PlacedSquare.reflectY, Point.reflectY, side]; linarith)
    refine ⟨mirrorVertical index, ?_⟩
    apply (square.reflectY_contains_iff side (points (mirrorVertical index))).1
    rw [points_mirrorVertical, Point.reflectY_reflectY]
    exact inside

end SquarePackingArchive.Stromquist.TenPoints
