import SquarePackingArchive.StromquistRingCover

namespace SquarePackingArchive.Stromquist.TenPoints

private lemma exterior_coordinate_bounds (origin first second point : Point)
    (first_right : origin.x ≤ first.x) (horizontal_order : first.x ≤ second.x)
    (second_below : second.y ≤ origin.y) (vertical_order : first.y ≤ second.y)
    (orientation : 0 < Point.orientedArea origin first second)
    (first_cone : 0 ≤ Point.orientedArea origin first point)
    (second_cone : 0 ≤ Point.orientedArea second origin point)
    (outside : Point.orientedArea first second point ≤ 0) :
    first.x ≤ point.x ∧ point.y ≤ second.y := by
  have horizontal_product := add_nonneg
    (mul_nonneg (sub_nonneg.mpr horizontal_order) first_cone)
    (mul_nonneg (sub_nonneg.mpr first_right) (neg_nonneg.mpr outside))
  have vertical_product := add_nonneg
    (mul_nonneg (sub_nonneg.mpr vertical_order) second_cone)
    (mul_nonneg (sub_nonneg.mpr second_below) (neg_nonneg.mpr outside))
  have horizontal_identity :
      Point.orientedArea origin first second * (point.x - first.x) =
      (second.x - first.x) * Point.orientedArea origin first point +
      (first.x - origin.x) * -Point.orientedArea first second point := by
    dsimp [Point.orientedArea]
    ring
  have vertical_identity :
      Point.orientedArea origin first second * (second.y - point.y) =
      (second.y - first.y) * Point.orientedArea second origin point +
      (origin.y - second.y) * -Point.orientedArea first second point := by
    dsimp [Point.orientedArea]
    ring
  constructor <;> nlinarith only [orientation, horizontal_product, horizontal_identity,
    vertical_product, vertical_identity]

set_option maxHeartbeats 1000000 in
lemma contains_bottom_right_sector
    (square : PlacedSquare) (fits : square.Fits side) (first second : Point)
    (first_x_lower : ringCenter.x < first.x) (first_x_upper : first.x < side - 1)
    (first_y_lower : 1 / 2 ≤ first.y) (first_y_upper : first.y ≤ 1)
    (second_x_lower : side - 1 ≤ second.x) (second_x_upper : second.x ≤ side - 1 / 2)
    (second_y_lower : 1 < second.y) (second_y_upper : second.y < ringCenter.y)
    (bottom_width : side - 1 - first.x ≤ 4 / 5)
    (right_width : second.y - 1 ≤ 4 / 5)
    (fan_orientation : 0 < Point.orientedArea ringCenter first second)
    (corner_orientation : 0 < Point.orientedArea ⟨side - 1, 1⟩ second first)
    (corner_first_distance : (⟨side - 1, 1⟩ : Point).squaredDistance first ≤ 1)
    (corner_second_distance : (⟨side - 1, 1⟩ : Point).squaredDistance second ≤ 1)
    (pair_distance : first.squaredDistance second ≤ 1)
    (first_cone : 0 ≤ Point.orientedArea ringCenter first square.center)
    (second_cone : 0 ≤ Point.orientedArea second ringCenter square.center)
    (outside : Point.orientedArea first second square.center ≤ 0) :
    square.Contains first ∨ square.Contains second ∨ square.Contains ⟨side - 1, 1⟩ := by
  obtain ⟨center_right, center_below⟩ := exterior_coordinate_bounds ringCenter first second square.center
    first_x_lower.le (by linarith) second_y_upper.le (by linarith)
    fan_orientation first_cone second_cone outside
  have triangle_hit
      (bottom_inside : 0 ≤ Point.orientedArea first ⟨side - 1, 1⟩ square.center)
      (right_inside : 0 ≤ Point.orientedArea ⟨side - 1, 1⟩ second square.center) :
      square.Contains first ∨ square.Contains second ∨ square.Contains ⟨side - 1, 1⟩ := by
    rw [Point.squaredDistance_comm] at pair_distance
    rcases square.contains_triangleVertex_of_cross_nonnegative ⟨side - 1, 1⟩ second first
      corner_orientation right_inside
      (by dsimp [Point.orientedArea] at outside ⊢; nlinarith only [outside])
      bottom_inside corner_second_distance corner_first_distance pair_distance with
      corner_inside | second_inside | first_inside
    · exact Or.inr (Or.inr corner_inside)
    · exact Or.inr (Or.inl second_inside)
    · exact Or.inl first_inside
  by_cases left_of_corner : square.center.x ≤ side - 1
  · by_cases bottom_inside : 0 ≤ Point.orientedArea first ⟨side - 1, 1⟩ square.center
    · apply triangle_hit bottom_inside
      have weighted := add_nonneg
        (mul_nonneg (show 0 ≤ second.x - (side - 1) by linarith) bottom_inside)
        (mul_nonneg corner_orientation.le (show 0 ≤ side - 1 - square.center.x by linarith))
      have identity :
          (side - 1 - first.x) * Point.orientedArea ⟨side - 1, 1⟩ second square.center =
          (second.x - (side - 1)) * Point.orientedArea first ⟨side - 1, 1⟩ square.center +
          Point.orientedArea ⟨side - 1, 1⟩ second first * (side - 1 - square.center.x) := by
        dsimp [Point.orientedArea]
        ring
      nlinarith only [weighted, identity, first_x_upper]
    · have pair := contains_short_pair (left := first.x) (width := side - 1 - first.x)
        (firstHeight := first.y) (secondHeight := 1) fits
        (by linarith) bottom_width first_y_lower first_y_upper (by norm_num) (by norm_num)
        center_right (by linarith)
        (by dsimp [Point.orientedArea] at bottom_inside; nlinarith only [bottom_inside])
      rcases pair with first_inside | corner_inside
      · exact Or.inl (by simpa using first_inside)
      · apply Or.inr; apply Or.inr
        convert corner_inside using 1
        simp
  · by_cases below_corner : square.center.y ≤ 1
    · apply Or.inr; apply Or.inr
      apply (square.reflectX_contains_iff side ⟨side - 1, 1⟩).1
      have corner := (square.reflectX side).contains_unitCorner
        ((square.reflectX_fits_iff side).2 fits)
        (by change side - square.center.x ≤ 1; linarith)
        below_corner
      simpa [Point.reflectX] using corner
    · by_cases right_inside : 0 ≤ Point.orientedArea ⟨side - 1, 1⟩ second square.center
      · apply triangle_hit _ right_inside
        have weighted := add_nonneg
          (mul_nonneg (show 0 ≤ 1 - first.y by linarith) right_inside)
          (mul_nonneg corner_orientation.le (show 0 ≤ square.center.y - 1 by linarith))
        have identity :
            (second.y - 1) * Point.orientedArea first ⟨side - 1, 1⟩ square.center =
            (1 - first.y) * Point.orientedArea ⟨side - 1, 1⟩ second square.center +
            Point.orientedArea ⟨side - 1, 1⟩ second first * (square.center.y - 1) := by
          dsimp [Point.orientedArea]
          ring
        nlinarith only [weighted, identity, second_y_lower]
      · have pair := contains_short_pair (left := 1) (width := second.y - 1)
          (firstHeight := 1) (secondHeight := side - second.x)
          (((square.reflectX side).swap_fits_iff side).2 ((square.reflectX_fits_iff side).2 fits))
          (by linarith) right_width (by norm_num) (by norm_num) (by linarith) (by linarith)
          (by change 1 ≤ square.center.y; linarith)
          (by change square.center.y ≤ 1 + (second.y - 1); linarith)
          (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, Point.swap, Point.reflectX,
            Point.orientedArea] at right_inside ⊢; nlinarith only [right_inside])
        rcases pair with corner_inside | second_inside
        · apply Or.inr; apply Or.inr
          apply (square.reflectX_contains_iff side ⟨side - 1, 1⟩).1
          apply ((square.reflectX side).swap_contains_iff ((⟨side - 1, 1⟩ : Point).reflectX side)).1
          simpa [Point.reflectX, Point.swap] using corner_inside
        · apply Or.inr; apply Or.inl
          apply (square.reflectX_contains_iff side second).1
          apply ((square.reflectX side).swap_contains_iff (second.reflectX side)).1
          convert second_inside using 1
          simp [Point.reflectX, Point.swap]

end SquarePackingArchive.Stromquist.TenPoints
