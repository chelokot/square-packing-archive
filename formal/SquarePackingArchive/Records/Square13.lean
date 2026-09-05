import SquarePackingArchive.Records.Square7
import SquarePackingArchive.TriangleRegions
import SquarePackingArchive.FriedmanStrip

namespace SquarePackingArchive.Records.Square13

noncomputable def initialPoints (index : Fin 16) : Point :=
  match index.val with
  | 0 => ⟨1, 457 / 500⟩
  | 1 => ⟨457 / 500, 1⟩
  | 2 => ⟨3, 457 / 500⟩
  | 3 => ⟨1543 / 500, 1⟩
  | 4 => ⟨1, 1543 / 500⟩
  | 5 => ⟨457 / 500, 3⟩
  | 6 => ⟨3, 1543 / 500⟩
  | 7 => ⟨1543 / 500, 3⟩
  | 8 => ⟨457 / 500, 2⟩
  | 9 => ⟨1543 / 500, 2⟩
  | 10 => ⟨2, 457 / 500⟩
  | 11 => ⟨2, 1543 / 500⟩
  | 12 => ⟨33 / 20, 33 / 20⟩
  | 13 => ⟨47 / 20, 33 / 20⟩
  | 14 => ⟨33 / 20, 47 / 20⟩
  | _ => ⟨47 / 20, 47 / 20⟩

def reflectXIndex : Fin 16 → Fin 16 := ![2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 10, 11, 13, 12, 15, 14]
def reflectYIndex : Fin 16 → Fin 16 := ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 11, 10, 14, 15, 12, 13]
def swapIndex : Fin 16 → Fin 16 := ![1, 0, 5, 4, 3, 2, 7, 6, 10, 11, 8, 9, 12, 14, 13, 15]

theorem initialPoints_reflectX (index : Fin 16) :
    initialPoints (reflectXIndex index) = (initialPoints index).reflectX 4 := by
  fin_cases index <;> norm_num [reflectXIndex, initialPoints, Point.reflectX,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem initialPoints_reflectY (index : Fin 16) :
    initialPoints (reflectYIndex index) = (initialPoints index).reflectY 4 := by
  fin_cases index <;> norm_num [reflectYIndex, initialPoints, Point.reflectY,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem initialPoints_swap (index : Fin 16) :
    initialPoints (swapIndex index) = (initialPoints index).swap := by
  fin_cases index <;> norm_num [swapIndex, initialPoints, Point.swap,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

lemma contains_of_center_distance_sq_le_quarter
    (square : PlacedSquare) (point : Point)
    (distance : (point.x - square.center.x)^2 + (point.y - square.center.y)^2 ≤ 1 / 4) :
    square.Contains point := by
  have invariant := square.local_coordinate_distance_sq point square.center
  have center_x : square.localX square.center = 0 := by simp [PlacedSquare.localX]
  have center_y : square.localY square.center = 0 := by simp [PlacedSquare.localY]
  rw [center_x, center_y, sub_zero, sub_zero] at invariant
  rw [square.contains_iff_localCoordinates, abs_le, abs_le]
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (square.localX point), sq_nonneg (square.localY point)]

lemma initialPoints_hit_of_triangle
    (square : PlacedSquare) (first second third : Fin 16)
    (positive : 0 < Point.orientedArea (initialPoints first) (initialPoints second) (initialPoints third))
    (first_side : 0 ≤ Point.orientedArea (initialPoints first) (initialPoints second) square.center)
    (second_side : 0 ≤ Point.orientedArea (initialPoints second) (initialPoints third) square.center)
    (third_side : 0 ≤ Point.orientedArea (initialPoints third) (initialPoints first) square.center)
    (first_second : ((initialPoints first).x - (initialPoints second).x)^2 +
      ((initialPoints first).y - (initialPoints second).y)^2 ≤ 1)
    (first_third : ((initialPoints first).x - (initialPoints third).x)^2 +
      ((initialPoints first).y - (initialPoints third).y)^2 ≤ 1)
    (second_third : ((initialPoints second).x - (initialPoints third).x)^2 +
      ((initialPoints second).y - (initialPoints third).y)^2 ≤ 1) :
    ∃ index, square.Contains (initialPoints index) := by
  obtain inside | inside | inside := square.contains_triangleVertex_of_cross_nonnegative
    (initialPoints first) (initialPoints second) (initialPoints third)
    positive first_side second_side third_side first_second first_third second_third
  · exact ⟨first, inside⟩
  · exact ⟨second, inside⟩
  · exact ⟨third, inside⟩

theorem initialPoints_wedge
    (square : PlacedSquare) (fits : square.Fits 4)
    (above_diagonal : square.center.x ≤ square.center.y)
    (below_middle : square.center.y ≤ 2) :
    ∃ index, square.Contains (initialPoints index) := by
  by_cases left_strip : square.center.x ≤ 457 / 500
  · obtain ⟨column, contained⟩ := square.swap.contains_bottomSpacedRow 2
      ((square.swap_fits_iff 4).2 fits) (left := 1) (targetHeight := 457 / 500)
      (by norm_num) (by norm_num)
      (by have root := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); have positive := Real.sqrt_nonneg (2 : ℝ); nlinarith)
      left_strip
    have original := (square.swap_contains_iff ⟨457 / 500, 1 + (column : ℝ)⟩).1 contained
    fin_cases column
    · exact ⟨1, by simpa [initialPoints] using original⟩
    · exact ⟨8, by convert original using 1; norm_num [initialPoints]⟩
    · exact ⟨5, by convert original using 1; norm_num [initialPoints]⟩
  have horizontal_lower : 457 / 500 ≤ square.center.x := by linarith
  by_cases corner : square.center.y ≤ 1
  · refine ⟨1, contains_of_center_distance_sq_le_quarter square (initialPoints 1) ?_⟩
    norm_num [initialPoints]
    nlinarith [mul_nonneg (show 0 ≤ square.center.x - 457 / 500 by linarith)
      (show 0 ≤ 1 - square.center.x by linarith),
      mul_nonneg (show 0 ≤ square.center.y - 457 / 500 by linarith)
      (show 0 ≤ 1 - square.center.y by linarith)]
  by_cases left_inner : square.center.x ≤ 33 / 20
  · by_cases above_first : (92 / 125 : ℝ) * (square.center.y - 1) ≥
        (13 / 20 : ℝ) * (square.center.x - 457 / 500)
    · by_cases below_second : (92 / 125 : ℝ) * (square.center.y - 2) ≤
          -(7 / 20 : ℝ) * (square.center.x - 457 / 500)
      · apply initialPoints_hit_of_triangle square 1 12 8 <;>
          norm_num [initialPoints, Point.orientedArea] <;> linarith
      · apply initialPoints_hit_of_triangle square 8 12 14 <;>
          norm_num [initialPoints, Point.orientedArea] <;> linarith
    · apply initialPoints_hit_of_triangle square 0 12 1 <;>
        norm_num [initialPoints, Point.orientedArea] <;> linarith
  · apply initialPoints_hit_of_triangle square 12 15 14 <;>
      norm_num [initialPoints, Point.orientedArea] <;> linarith

theorem initialPoints_quarter
    (square : PlacedSquare) (fits : square.Fits 4)
    (left_middle : square.center.x ≤ 2) (below_middle : square.center.y ≤ 2) :
    ∃ index, square.Contains (initialPoints index) := by
  by_cases above_diagonal : square.center.x ≤ square.center.y
  · exact initialPoints_wedge square fits above_diagonal below_middle
  · obtain ⟨index, contained⟩ := initialPoints_wedge square.swap
      ((square.swap_fits_iff 4).2 fits)
      (by dsimp [PlacedSquare.swap, Point.swap]; linarith) left_middle
    refine ⟨swapIndex index, ?_⟩
    rw [initialPoints_swap]
    exact (square.swap_contains_iff (initialPoints index).swap).1 (by simpa using contained)

theorem initialPoints_left_half
    (square : PlacedSquare) (fits : square.Fits 4) (left_middle : square.center.x ≤ 2) :
    ∃ index, square.Contains (initialPoints index) := by
  by_cases below_middle : square.center.y ≤ 2
  · exact initialPoints_quarter square fits left_middle below_middle
  · obtain ⟨index, contained⟩ := initialPoints_quarter (square.reflectY 4)
      ((square.reflectY_fits_iff 4).2 fits)
      (by simpa [PlacedSquare.reflectY, Point.reflectY] using left_middle)
      (by dsimp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    refine ⟨reflectYIndex index, ?_⟩
    rw [initialPoints_reflectY]
    exact (square.reflectY_contains_iff 4 ((initialPoints index).reflectY 4)).1 (by simpa using contained)

theorem initialPoints_unavoidable : Unavoidable initialPoints 4 := by
  intro square fits
  by_cases left_middle : square.center.x ≤ 2
  · exact initialPoints_left_half square fits left_middle
  · obtain ⟨index, contained⟩ := initialPoints_left_half (square.reflectX 4)
      ((square.reflectX_fits_iff 4).2 fits)
      (by dsimp [PlacedSquare.reflectX, Point.reflectX]; linarith)
    refine ⟨reflectXIndex index, ?_⟩
    rw [initialPoints_reflectX]
    exact (square.reflectX_contains_iff 4 ((initialPoints index).reflectX 4)).1 (by simpa using contained)

theorem initialPoints_interior_scaled {side : ℝ}
    (side_positive : 0 < side) (side_lt_four : side < 4) :
    InteriorUnavoidable (fun index => (initialPoints index).scale (side / 4)) side := by
  have factor_gt_one : 1 < 4 / side := (lt_div_iff₀ side_positive).2 (by simpa using side_lt_four)
  have scaled : Unavoidable initialPoints ((4 / side) * side) := by
    simpa [side_positive.ne'] using initialPoints_unavoidable
  simpa [one_div_div] using scaled.interior_scaled factor_gt_one

noncomputable def coveredIndices {side : ℝ} (packing : Packing 13 side)
    (points : Fin 16 → Point) (owner : Fin 13) : Finset (Fin 16) := by
  classical
  exact Finset.univ.filter (fun index => (packing.squares owner).InteriorContains (points index))

theorem coveredIndices_total_le {side : ℝ} (packing : Packing 13 side)
    (points : Fin 16 → Point) :
    ∑ owner, (coveredIndices packing points owner).card ≤ 16 := by
  classical
  have disjoint : (↑(Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint
      (coveredIndices packing points) := by
    intro first _ second _ different
    apply Finset.disjoint_left.2
    intro index first_mem second_mem
    simp only [coveredIndices, Finset.mem_filter, Finset.mem_univ, true_and] at first_mem second_mem
    exact packing.disjoint first second different (points index) ⟨first_mem, second_mem⟩
  rw [← Finset.card_biUnion disjoint]
  exact (Finset.card_le_univ _).trans (by norm_num)

theorem at_least_ten_singleton_owners {side : ℝ} (packing : Packing 13 side)
    (points : Fin 16 → Point)
    (each_square_hit : ∀ owner, ∃ index, (packing.squares owner).InteriorContains (points index)) :
    10 ≤ (Finset.univ.filter (fun owner => (coveredIndices packing points owner).card = 1)).card := by
  classical
  have lower (owner : Fin 13) :
      2 ≤ (coveredIndices packing points owner).card +
        if (coveredIndices packing points owner).card = 1 then 1 else 0 := by
    obtain ⟨index, contained⟩ := each_square_hit owner
    have nonempty : (coveredIndices packing points owner).Nonempty := by
      exact ⟨index, by simp [coveredIndices, contained]⟩
    have positive := Finset.card_pos.2 nonempty
    split_ifs <;> omega
  have sum_lower := Finset.sum_le_sum (s := Finset.univ) (fun owner _ => lower owner)
  have sum_upper := coveredIndices_total_le packing points
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.reduceMul] at sum_lower
  have indicator : (∑ owner : Fin 13, if (coveredIndices packing points owner).card = 1 then 1 else 0) =
      (Finset.univ.filter (fun owner => (coveredIndices packing points owner).card = 1)).card := by
    simp
  rw [indicator] at sum_lower
  omega

theorem two_corner_restricted_points {side : ℝ} (packing : Packing 13 side)
    (points : Fin 16 → Point)
    (each_square_hit : ∀ owner, ∃ index, (packing.squares owner).InteriorContains (points index)) :
    ∃ corners : Finset (Fin 16), 2 ≤ corners.card ∧
      ∀ index ∈ corners, index.val < 8 ∧
        ∃ owner, coveredIndices packing points owner = {index} := by
  classical
  choose assigned contained using each_square_hit
  have assigned_injective : Function.Injective assigned := by
    intro first second same
    by_contra different
    exact packing.disjoint first second different (points (assigned first))
      ⟨contained first, by rw [same]; exact contained second⟩
  let singletons := Finset.univ.filter (fun owner => (coveredIndices packing points owner).card = 1)
  let singletonPoints := singletons.image assigned
  let cornerPoints := Finset.univ.filter (fun index : Fin 16 => index.val < 8)
  have singleton_count : 10 ≤ singletonPoints.card := by
    dsimp [singletonPoints]
    rw [Finset.card_image_of_injective _ assigned_injective]
    exact at_least_ten_singleton_owners packing points (fun owner => ⟨assigned owner, contained owner⟩)
  have corner_count : cornerPoints.card = 8 := by decide +kernel
  have union_count : (singletonPoints ∪ cornerPoints).card ≤ 16 := by
    exact (Finset.card_le_univ _).trans (by norm_num)
  have intersection_count := Finset.card_union_add_card_inter singletonPoints cornerPoints
  refine ⟨singletonPoints ∩ cornerPoints, by omega, ?_⟩
  intro index index_mem
  obtain ⟨singleton_mem, corner_mem⟩ := Finset.mem_inter.1 index_mem
  refine ⟨(Finset.mem_filter.1 corner_mem).2, ?_⟩
  obtain ⟨owner, owner_mem, assigned_eq⟩ := Finset.mem_image.1 singleton_mem
  have card_one := (Finset.mem_filter.1 owner_mem).2
  obtain ⟨unique, unique_eq⟩ := Finset.card_eq_one.1 card_one
  have assigned_mem : assigned owner ∈ coveredIndices packing points owner := by
    simp [coveredIndices, contained owner]
  rw [unique_eq, Finset.mem_singleton] at assigned_mem
  exact ⟨owner, by rw [unique_eq, ← assigned_mem, assigned_eq]⟩

theorem packing_has_two_corner_restricted_points {side : ℝ} (packing : Packing 13 side)
    (side_lt_four : side < 4) :
    ∃ corners : Finset (Fin 16), 2 ≤ corners.card ∧
      ∀ index ∈ corners, index.val < 8 ∧
        ∃ owner, coveredIndices packing (fun point => (initialPoints point).scale (side / 4)) owner = {index} := by
  apply two_corner_restricted_points
  intro owner
  exact initialPoints_interior_scaled (packing.side_positive (by norm_num)) side_lt_four
    (packing.squares owner) (packing.fits owner)

theorem singleton_replacement_forces_point
    (square : PlacedSquare) {side : ℝ} (fits : square.Fits side)
    (points : Fin 16 → Point) (index : Fin 16) (replacement : Point)
    (singleton : ∀ other, square.Contains (points other) → other = index)
    (replacement_unavoidable : Unavoidable (Function.update points index replacement) side) :
    square.Contains replacement := by
  obtain ⟨other, covered⟩ := replacement_unavoidable square fits
  by_cases same : other = index
  · simpa [same] using covered
  · have old_mem : square.Contains (points other) := by simpa [Function.update_of_ne same] using covered
    exact (same (singleton other old_mem)).elim

end SquarePackingArchive.Records.Square13
