import SquarePackingArchive.StromquistLeftReplacement
import SquarePackingArchive.StromquistInnerOwnership
import SquarePackingArchive.StromquistPentagon

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def stepThreePoints (index : Fin 13) : Point :=
  match index.val with
  | 0 => points 0
  | 1 => ⟨6 / 5, 1⟩
  | 2 => leftReplacement (side - 49 / 25)
  | 3 => points 2
  | 4 => points 3
  | 5 => points 4
  | 6 => points 5
  | 7 => points 6
  | 8 => ⟨2, 1⟩
  | 9 => points 8
  | 10 => points 9
  | 11 => (points 8).swap
  | _ => (points 9).swap

def stepThreeTriangles (index : Fin 15) : Fin 3 → Fin 13 :=
  match index.val with
  | 0 => ![9, 3, 2]
  | 1 => ![5, 10, 6]
  | 2 => ![10, 7, 6]
  | 3 => ![3, 12, 4]
  | 4 => ![12, 3, 9]
  | 5 => ![12, 5, 4]
  | 6 => ![12, 10, 5]
  | 7 => ![10, 8, 7]
  | 8 => ![11, 8, 10]
  | 9 => ![11, 1, 8]
  | 10 => ![1, 11, 9]
  | 11 => ![1, 9, 2]
  | 12 => ![0, 1, 2]
  | 13 => ![12, 11, 10]
  | _ => ![11, 12, 9]

set_option maxHeartbeats 1000000 in
lemma stepThree_triangle_valid (index : Fin 15) :
    let first := stepThreePoints (stepThreeTriangles index 0)
    let second := stepThreePoints (stepThreeTriangles index 1)
    let third := stepThreePoints (stepThreeTriangles index 2)
    0 < Point.orientedArea first second third ∧
      (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2 ≤ 1 ∧
      (first.x - third.x) ^ 2 + (first.y - third.y) ^ 2 ≤ 1 ∧
      (second.x - third.x) ^ 2 + (second.y - third.y) ^ 2 ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;>
    norm_num [stepThreeTriangles, stepThreePoints, points, leftReplacement,
      Point.swap, Point.orientedArea, side, Matrix.cons_val_two]
  all_goals repeat' apply And.intro
  all_goals first | (rw [abs_le]; constructor <;> nlinarith) | nlinarith

lemma stepThree_hit_triangle (square : PlacedSquare) (index : Fin 15)
    (first_halfplane : 0 ≤ Point.orientedArea
      (stepThreePoints (stepThreeTriangles index 0))
      (stepThreePoints (stepThreeTriangles index 1)) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (stepThreePoints (stepThreeTriangles index 1))
      (stepThreePoints (stepThreeTriangles index 2)) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (stepThreePoints (stepThreeTriangles index 2))
      (stepThreePoints (stepThreeTriangles index 0)) square.center) :
    ∃ pointIndex, square.Contains (stepThreePoints pointIndex) := by
  exact square.contains_indexed_triangleVertex stepThreePoints (stepThreeTriangles index)
    (stepThree_triangle_valid index) first_halfplane second_halfplane third_halfplane

end SquarePackingArchive.Stromquist.TenPoints
