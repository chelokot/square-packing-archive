import SquarePackingArchive.Records.Square5
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.GoebelStrip

open Square5 (diagonal axisFrame diagonalFrame diagonal_positive diagonal_sq)

noncomputable def side (steps : ℕ) : ℝ := steps + 1 + diagonal

noncomputable def axisSquare (horizontal vertical : ℝ) : PlacedSquare :=
  ⟨⟨horizontal, vertical⟩, axisFrame⟩

noncomputable def stairSquare {steps : ℕ} (cell : Fin steps × Fin (steps + 1)) : PlacedSquare :=
  if cell.1.val + cell.2.val < steps then
    axisSquare (cell.1 + 1 / 2) (cell.2 + 1 / 2)
  else axisSquare (cell.1 + 3 / 2 + diagonal) (cell.2 + 1 / 2 + diagonal)

noncomputable def cornerSquare (steps : ℕ) (corner : Fin 2) : PlacedSquare :=
  if corner = 0 then axisSquare (side steps - 1 / 2) (1 / 2)
  else axisSquare (1 / 2) (side steps - 1 / 2)

noncomputable def stripSquare (steps stripCount : ℕ) (index : Fin stripCount) : PlacedSquare :=
  ⟨⟨side steps / 2 - (index - ((stripCount : ℝ) - 1) / 2) * diagonal,
    side steps / 2 + (index - ((stripCount : ℝ) - 1) / 2) * diagonal⟩, diagonalFrame⟩

lemma axis_interior_bounds {horizontal vertical : ℝ} {point : Point}
    (inside : (axisSquare horizontal vertical).InteriorContains point) :
    horizontal - 1 / 2 < point.x ∧ point.x < horizontal + 1 / 2 ∧
      vertical - 1 / 2 < point.y ∧ point.y < vertical + 1 / 2 := by
  rcases inside with ⟨localX, localY, localX_bound, localY_bound, rfl⟩
  rcases abs_lt.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_lt.mp localY_bound with ⟨localY_lower, localY_upper⟩
  norm_num [axisSquare, PlacedSquare.point, Frame.place, axisFrame]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma axis_fits {horizontal vertical bound : ℝ}
    (bounds : 1 / 2 ≤ horizontal ∧ horizontal ≤ bound - 1 / 2 ∧
      1 / 2 ≤ vertical ∧ vertical ≤ bound - 1 / 2) :
    (axisSquare horizontal vertical).Fits bound := by
  intro point inside
  rcases inside with ⟨localX, localY, localX_bound, localY_bound, rfl⟩
  rcases abs_le.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_le.mp localY_bound with ⟨localY_lower, localY_upper⟩
  norm_num [axisSquare, PlacedSquare.point, Frame.place, axisFrame, Container.Contains]
  exact ⟨by linarith [bounds.1], by linarith [bounds.2.1],
    by linarith [bounds.2.2.1], by linarith [bounds.2.2.2]⟩

lemma axis_disjoint {firstX firstY secondX secondY : ℝ}
    (gap : 1 ≤ |firstX - secondX| ∨ 1 ≤ |firstY - secondY|) :
    (axisSquare firstX firstY).InteriorDisjoint (axisSquare secondX secondY) := by
  intro point shared
  have first := axis_interior_bounds shared.1
  have second := axis_interior_bounds shared.2
  rcases gap with horizontal | vertical
  · have small : |firstX - secondX| < 1 := abs_lt.mpr ⟨by linarith [first.2.1, second.1],
      by linarith [first.1, second.2.1]⟩
    linarith
  · have small : |firstY - secondY| < 1 := abs_lt.mpr ⟨by linarith [first.2.2.2, second.2.2.1],
      by linarith [first.2.2.1, second.2.2.2]⟩
    linarith

lemma stair_fits {steps : ℕ} (cell : Fin steps × Fin (steps + 1)) :
    (stairSquare cell).Fits (side steps) := by
  have column_lower : (0 : ℝ) ≤ cell.1 := Nat.cast_nonneg _
  have row_lower : (0 : ℝ) ≤ cell.2 := Nat.cast_nonneg _
  have column_upper : (cell.1 : ℝ) + 1 ≤ steps := by exact_mod_cast cell.1.isLt
  have row_upper : (cell.2 : ℝ) ≤ steps := by exact_mod_cast Nat.le_of_lt_succ cell.2.isLt
  dsimp [stairSquare]
  split_ifs <;> apply axis_fits <;> dsimp [side] <;>
    exact ⟨by linarith [diagonal_positive], by linarith [diagonal_positive],
      by linarith [diagonal_positive], by linarith [diagonal_positive]⟩

lemma stair_interior_sum {steps : ℕ} (cell : Fin steps × Fin (steps + 1)) {point : Point}
    (inside : (stairSquare cell).InteriorContains point) :
    if cell.1.val + cell.2.val < steps then point.x + point.y < steps + 1
    else steps + 1 + 2 * diagonal < point.x + point.y := by
  dsimp [stairSquare] at inside
  split_ifs at inside ⊢ with lower
  · have sum_upper : (cell.1 : ℝ) + cell.2 + 1 ≤ steps := by exact_mod_cast lower
    have bounds := axis_interior_bounds inside
    linarith [bounds.2.1, bounds.2.2.2]
  · have sum_lower : (steps : ℝ) ≤ (cell.1 : ℝ) + cell.2 := by exact_mod_cast le_of_not_gt lower
    have bounds := axis_interior_bounds inside
    linarith [bounds.1, bounds.2.2.1]

lemma corner_fits {steps : ℕ} (positive : 1 ≤ steps) (corner : Fin 2) :
    (cornerSquare steps corner).Fits (side steps) := by
  have step_lower : (1 : ℝ) ≤ steps := by exact_mod_cast positive
  dsimp [cornerSquare]
  split_ifs <;> apply axis_fits <;> dsimp [side] <;>
    exact ⟨by linarith [diagonal_positive], by linarith [diagonal_positive],
      by linarith [diagonal_positive], by linarith [diagonal_positive]⟩

lemma strip_interior_interval (steps stripCount : ℕ) (index : Fin stripCount) {point : Point}
    (inside : (stripSquare steps stripCount index).InteriorContains point) :
    steps + 1 < point.x + point.y ∧ point.x + point.y < steps + 1 + 2 * diagonal ∧
      (2 * index - ((stripCount : ℝ) - 1) - 1) * diagonal < point.y - point.x ∧
      point.y - point.x < (2 * index - ((stripCount : ℝ) - 1) + 1) * diagonal := by
  rcases inside with ⟨localX, localY, localX_bound, localY_bound, rfl⟩
  rcases abs_lt.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_lt.mp localY_bound with ⟨localY_lower, localY_upper⟩
  have horizontal_lower := mul_pos diagonal_positive (show 0 < localX + 1 / 2 by linarith)
  have horizontal_upper := mul_pos diagonal_positive (show 0 < 1 / 2 - localX by linarith)
  have vertical_lower := mul_pos diagonal_positive (show 0 < localY + 1 / 2 by linarith)
  have vertical_upper := mul_pos diagonal_positive (show 0 < 1 / 2 - localY by linarith)
  dsimp [stripSquare, PlacedSquare.point, Frame.place, diagonalFrame, side]
  constructor
  · nlinarith only [horizontal_lower]
  constructor
  · nlinarith only [horizontal_upper]
  constructor <;> nlinarith only [vertical_lower, vertical_upper]

lemma strip_fits {steps stripCount : ℕ}
    (length_bound : ((stripCount : ℝ) - 1) * diagonal ≤ steps - 1)
    (index : Fin stripCount) : (stripSquare steps stripCount index).Fits (side steps) := by
  have index_lower : (0 : ℝ) ≤ index := Nat.cast_nonneg _
  have index_upper : (index : ℝ) + 1 ≤ stripCount := by exact_mod_cast index.isLt
  have lower_product := mul_nonneg index_lower diagonal_positive.le
  have upper_product := mul_nonneg (show 0 ≤ (stripCount : ℝ) - 1 - index by linarith) diagonal_positive.le
  have diagonal_upper : diagonal ≤ 1 := by nlinarith [diagonal_positive, diagonal_sq]
  intro point inside
  rcases inside with ⟨localX, localY, localX_bound, localY_bound, rfl⟩
  rcases abs_le.mp localX_bound with ⟨localX_lower, localX_upper⟩
  rcases abs_le.mp localY_bound with ⟨localY_lower, localY_upper⟩
  have horizontal_lower := mul_nonneg diagonal_positive.le (show 0 ≤ localX + 1 / 2 by linarith)
  have horizontal_upper := mul_nonneg diagonal_positive.le (show 0 ≤ 1 / 2 - localX by linarith)
  have vertical_lower := mul_nonneg diagonal_positive.le (show 0 ≤ localY + 1 / 2 by linarith)
  have vertical_upper := mul_nonneg diagonal_positive.le (show 0 ≤ 1 / 2 - localY by linarith)
  dsimp [stripSquare, PlacedSquare.point, Frame.place, diagonalFrame, side, Container.Contains]
  exact ⟨by nlinarith only [lower_product, upper_product, length_bound, diagonal_upper,
      horizontal_lower, vertical_upper],
    by nlinarith only [lower_product, upper_product, length_bound, diagonal_upper,
      horizontal_upper, vertical_lower],
    by nlinarith only [lower_product, upper_product, length_bound, diagonal_upper,
      horizontal_lower, vertical_lower],
    by nlinarith only [lower_product, upper_product, length_bound, diagonal_upper,
      horizontal_upper, vertical_upper]⟩

lemma translated_grid_disjoint {columns rows : ℕ}
    (left right : Fin columns × Fin rows) (different : left ≠ right)
    (horizontal vertical : ℝ) :
    (axisSquare (left.1 + horizontal) (left.2 + vertical)).InteriorDisjoint
      (axisSquare (right.1 + horizontal) (right.2 + vertical)) := by
  apply axis_disjoint
  by_cases columns_different : left.1 ≠ right.1
  · left
    simpa only [add_sub_add_right_eq_sub] using SquareNumbers.fin_cast_distance_ge_one columns_different
  · right
    have rows_different : left.2 ≠ right.2 := by
      intro equal
      exact different (Prod.ext (not_not.mp columns_different) equal)
    simpa only [add_sub_add_right_eq_sub] using SquareNumbers.fin_cast_distance_ge_one rows_different

lemma stairs_disjoint {steps : ℕ} (left right : Fin steps × Fin (steps + 1))
    (different : left ≠ right) : (stairSquare left).InteriorDisjoint (stairSquare right) := by
  by_cases left_lower : left.1.val + left.2.val < steps
  · by_cases right_lower : right.1.val + right.2.val < steps
    · simpa [stairSquare, left_lower, right_lower] using translated_grid_disjoint left right different (1 / 2) (1 / 2)
    · intro point shared
      have first := stair_interior_sum left shared.1
      have second := stair_interior_sum right shared.2
      simp only [if_pos left_lower, if_neg right_lower] at first second
      linarith [diagonal_positive]
  · by_cases right_lower : right.1.val + right.2.val < steps
    · intro point shared
      have first := stair_interior_sum left shared.1
      have second := stair_interior_sum right shared.2
      simp only [if_neg left_lower, if_pos right_lower] at first second
      linarith [diagonal_positive]
    · simpa [stairSquare, left_lower, right_lower, add_assoc] using
        translated_grid_disjoint left right different (3 / 2 + diagonal) (1 / 2 + diagonal)

lemma stair_corner_disjoint {steps : ℕ} (cell : Fin steps × Fin (steps + 1))
    (corner : Fin 2) : (stairSquare cell).InteriorDisjoint (cornerSquare steps corner) := by
  intro point shared
  have column_lower : (0 : ℝ) ≤ cell.1 := Nat.cast_nonneg _
  have column_upper : (cell.1 : ℝ) + 1 ≤ steps := by exact_mod_cast cell.1.isLt
  by_cases lower : cell.1.val + cell.2.val < steps
  · have row_upper : (cell.2 : ℝ) + 1 ≤ steps := by
      exact_mod_cast (show cell.2.val < steps by omega)
    have stair_inside := shared.1
    simp only [stairSquare, if_pos lower] at stair_inside
    have stair_bounds := axis_interior_bounds stair_inside
    fin_cases corner
    · have corner_bounds := axis_interior_bounds (show
        (axisSquare (side steps - 1 / 2) (1 / 2)).InteriorContains point from shared.2)
      dsimp [side] at corner_bounds
      linarith [stair_bounds.2.1, corner_bounds.1, diagonal_positive]
    · have corner_bounds := axis_interior_bounds (show
        (axisSquare (1 / 2) (side steps - 1 / 2)).InteriorContains point from shared.2)
      dsimp [side] at corner_bounds
      linarith [stair_bounds.2.2.2, corner_bounds.2.2.1, diagonal_positive]
  · have row_lower : (1 : ℝ) ≤ cell.2 := by
      exact_mod_cast (show 1 ≤ cell.2.val by omega)
    have stair_inside := shared.1
    simp only [stairSquare, if_neg lower] at stair_inside
    have stair_bounds := axis_interior_bounds stair_inside
    fin_cases corner
    · have corner_bounds := axis_interior_bounds (show
        (axisSquare (side steps - 1 / 2) (1 / 2)).InteriorContains point from shared.2)
      linarith [stair_bounds.2.2.1, corner_bounds.2.2.2, diagonal_positive]
    · have corner_bounds := axis_interior_bounds (show
        (axisSquare (1 / 2) (side steps - 1 / 2)).InteriorContains point from shared.2)
      linarith [stair_bounds.1, corner_bounds.2.1, diagonal_positive]

lemma stair_strip_disjoint {steps stripCount : ℕ}
    (cell : Fin steps × Fin (steps + 1)) (index : Fin stripCount) :
    (stairSquare cell).InteriorDisjoint (stripSquare steps stripCount index) := by
  intro point shared
  have stair_sum := stair_interior_sum cell shared.1
  have strip_sum := strip_interior_interval steps stripCount index shared.2
  split_ifs at stair_sum <;> linarith [strip_sum.1, strip_sum.2.1]

lemma corners_disjoint {steps : ℕ} (positive : 1 ≤ steps)
    (left right : Fin 2) (different : left ≠ right) :
    (cornerSquare steps left).InteriorDisjoint (cornerSquare steps right) := by
  have step_lower : (1 : ℝ) ≤ steps := by exact_mod_cast positive
  fin_cases left <;> fin_cases right <;> simp at different
  · apply axis_disjoint
    left
    rw [abs_of_nonneg (by dsimp [side]; linarith [diagonal_positive])]
    dsimp [side]
    linarith [diagonal_positive]
  · apply axis_disjoint
    left
    rw [abs_of_nonpos (by dsimp [side]; linarith [diagonal_positive])]
    dsimp [side]
    linarith [diagonal_positive]

lemma corner_strip_disjoint {steps stripCount : ℕ}
    (length_bound : ((stripCount : ℝ) - 1) * diagonal ≤ steps - 1)
    (corner : Fin 2) (index : Fin stripCount) :
    (cornerSquare steps corner).InteriorDisjoint (stripSquare steps stripCount index) := by
  intro point shared
  have interval := strip_interior_interval steps stripCount index shared.2
  have index_lower : (0 : ℝ) ≤ index := Nat.cast_nonneg _
  have index_upper : (index : ℝ) + 1 ≤ stripCount := by exact_mod_cast index.isLt
  have lower_product := mul_nonneg index_lower diagonal_positive.le
  have upper_product := mul_nonneg (show 0 ≤ (stripCount : ℝ) - 1 - index by linarith) diagonal_positive.le
  fin_cases corner
  · have bounds := axis_interior_bounds (show
      (axisSquare (side steps - 1 / 2) (1 / 2)).InteriorContains point from shared.1)
    dsimp [side] at bounds
    nlinarith only [bounds.1, bounds.2.2.2, interval.2.2.1, lower_product, length_bound]
  · have bounds := axis_interior_bounds (show
      (axisSquare (1 / 2) (side steps - 1 / 2)).InteriorContains point from shared.1)
    dsimp [side] at bounds
    nlinarith only [bounds.2.1, bounds.2.2.1, interval.2.2.2, upper_product, length_bound]

lemma strips_disjoint (steps stripCount : ℕ) (left right : Fin stripCount)
    (different : left ≠ right) :
    (stripSquare steps stripCount left).InteriorDisjoint (stripSquare steps stripCount right) := by
  intro point shared
  have first := strip_interior_interval steps stripCount left shared.1
  have second := strip_interior_interval steps stripCount right shared.2
  rcases lt_or_gt_of_ne different with before | after
  · have index_gap : (left : ℝ) + 1 ≤ right := by exact_mod_cast before
    have product := mul_nonneg (show 0 ≤ (right : ℝ) - left - 1 by linarith) diagonal_positive.le
    nlinarith only [first.2.2.2, second.2.2.1, product]
  · have index_gap : (right : ℝ) + 1 ≤ left := by exact_mod_cast after
    have product := mul_nonneg (show 0 ≤ (left : ℝ) - right - 1 by linarith) diagonal_positive.le
    nlinarith only [second.2.2.2, first.2.2.1, product]

abbrev Index (steps stripCount : ℕ) :=
  (Fin steps × Fin (steps + 1)) ⊕ (Fin 2 ⊕ Fin stripCount)

noncomputable def indexedSquare (steps stripCount : ℕ) : Index steps stripCount → PlacedSquare :=
  Sum.elim stairSquare (Sum.elim (cornerSquare steps) (stripSquare steps stripCount))

lemma indexed_fits {steps stripCount : ℕ} (positive : 1 ≤ steps)
    (length_bound : ((stripCount : ℝ) - 1) * diagonal ≤ steps - 1)
    (index : Index steps stripCount) : (indexedSquare steps stripCount index).Fits (side steps) := by
  rcases index with cell | corner | rotated
  · exact stair_fits cell
  · exact corner_fits positive corner
  · exact strip_fits length_bound rotated

lemma indexed_disjoint {steps stripCount : ℕ} (positive : 1 ≤ steps)
    (length_bound : ((stripCount : ℝ) - 1) * diagonal ≤ steps - 1)
    (left right : Index steps stripCount) (different : left ≠ right) :
    (indexedSquare steps stripCount left).InteriorDisjoint (indexedSquare steps stripCount right) := by
  rcases left with leftCell | leftCorner | leftRotated <;>
    rcases right with rightCell | rightCorner | rightRotated
  · exact stairs_disjoint leftCell rightCell (fun equal => different (congrArg Sum.inl equal))
  · exact stair_corner_disjoint leftCell rightCorner
  · exact stair_strip_disjoint leftCell rightRotated
  · exact (stair_corner_disjoint rightCell leftCorner).symm
  · exact corners_disjoint positive leftCorner rightCorner
      (fun equal => different (congrArg (Sum.inr ∘ Sum.inl) equal))
  · exact corner_strip_disjoint length_bound leftCorner rightRotated
  · exact (stair_strip_disjoint rightCell leftRotated).symm
  · exact (corner_strip_disjoint length_bound rightCorner leftRotated).symm
  · exact strips_disjoint steps stripCount leftRotated rightRotated
      (fun equal => different (congrArg (Sum.inr ∘ Sum.inr) equal))

noncomputable def indexEquiv (steps stripCount : ℕ) :
    Index steps stripCount ≃ Fin (steps * (steps + 1) + 2 + stripCount) :=
  (Fintype.equivFin (Index steps stripCount)).trans
    (finCongr (by simp [Nat.add_assoc]))

noncomputable def packing (steps stripCount : ℕ) (positive : 1 ≤ steps)
    (length_bound : ((stripCount : ℝ) - 1) * diagonal ≤ steps - 1) :
    Packing (steps * (steps + 1) + 2 + stripCount) (side steps) where
  squares index := indexedSquare steps stripCount ((indexEquiv steps stripCount).symm index)
  side_nonnegative := by dsimp [side]; have := diagonal_positive; positivity
  fits index := indexed_fits positive length_bound _
  disjoint left right different := indexed_disjoint positive length_bound _ _
    (fun equal => different ((indexEquiv steps stripCount).symm.injective equal))

theorem goebel_strip_hasPacking {steps stripCount : ℕ} (positive : 1 ≤ steps)
    (length_bound : ((stripCount : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ steps - 1) :
    HasPacking (steps * (steps + 1) + 2 + stripCount) (steps + 1 + Real.sqrt 2 / 2) :=
  ⟨packing steps stripCount positive length_bound⟩

theorem s27_le_goebel : HasPacking 27 (5 + Real.sqrt 2 / 2) := by
  have length_bound : ((5 : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ 4 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  convert goebel_strip_hasPacking (steps := 4) (stripCount := 5) (by norm_num) length_bound using 1
  norm_num

theorem s38_le_goebel : HasPacking 38 (6 + Real.sqrt 2 / 2) := by
  have length_bound : ((6 : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ 5 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  convert goebel_strip_hasPacking (steps := 5) (stripCount := 6) (by norm_num) length_bound using 1
  norm_num

theorem s52_le_goebel : HasPacking 52 (7 + Real.sqrt 2 / 2) := by
  have length_bound : ((8 : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ 6 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  convert goebel_strip_hasPacking (steps := 6) (stripCount := 8) (by norm_num) length_bound using 1
  norm_num

theorem s67_le_goebel : HasPacking 67 (8 + Real.sqrt 2 / 2) := by
  have length_bound : ((9 : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ 7 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  convert goebel_strip_hasPacking (steps := 7) (stripCount := 9) (by norm_num) length_bound using 1
  norm_num

theorem s84_le_goebel : HasPacking 84 (9 + Real.sqrt 2 / 2) := by
  have length_bound : ((10 : ℝ) - 1) * (Real.sqrt 2 / 2) ≤ 8 - 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  convert goebel_strip_hasPacking (steps := 8) (stripCount := 10) (by norm_num) length_bound using 1
  norm_num

end SquarePackingArchive.Records.GoebelStrip
