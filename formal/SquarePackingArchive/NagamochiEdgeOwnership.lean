import SquarePackingArchive.NagamochiBadSquare

namespace SquarePackingArchive.Nagamochi

lemma different_edge_sides_squared_distance_lower_bound
    {size : ℕ} {firstCoordinate secondCoordinate : ℝ}
    (firstSide secondSide : NagamochiResource.EdgePoint)
    (different : firstSide ≠ secondSide) (size_lower : 4 ≤ size)
    (first_lower : 2 ≤ firstCoordinate) (first_upper : firstCoordinate ≤ (size : ℝ) - 2)
    (second_lower : 2 ≤ secondCoordinate) (second_upper : secondCoordinate ≤ (size : ℝ) - 2) :
    121 / 50 ≤
      (firstSide.pointAt size firstCoordinate 0 - secondSide.pointAt size secondCoordinate 0) ^ 2 +
        (firstSide.pointAt size firstCoordinate 1 - secondSide.pointAt size secondCoordinate 1) ^ 2 := by
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_lower
  cases firstSide <;> cases secondSide <;>
    simp_all only [ne_eq, not_true_eq_false, NagamochiResource.EdgePoint.pointAt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals nlinarith [sq_nonneg (firstCoordinate - 2), sq_nonneg (secondCoordinate - 2),
    sq_nonneg ((size : ℝ) - firstCoordinate - 2), sq_nonneg ((size : ℝ) - secondCoordinate - 2),
    sq_nonneg ((size : ℝ) - 4), sq_nonneg (firstCoordinate - secondCoordinate)]

theorem edge_point_sides_equal_of_same_square
    (square : PlacedSquare) {size firstCoordinate secondCoordinate : ℕ} {factor : ℝ}
    (firstSide secondSide : NagamochiResource.EdgePoint)
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (first_coordinate_mem : firstCoordinate ∈ Finset.Icc 2 (size - 2))
    (second_coordinate_mem : secondCoordinate ∈ Finset.Icc 2 (size - 2))
    (first_mem : NagamochiResource.edgePoint size firstCoordinate firstSide ∈
      square.dilatedInteriorRegion factor)
    (second_mem : NagamochiResource.edgePoint size secondCoordinate secondSide ∈
      square.dilatedInteriorRegion factor) :
    firstSide = secondSide := by
  by_contra different
  have real_bounds {coordinate : ℕ} (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2)) :
      (2 : ℝ) ≤ coordinate ∧ (coordinate : ℝ) ≤ (size : ℝ) - 2 := by
    rw [Finset.mem_Icc] at coordinate_mem
    constructor
    · exact_mod_cast coordinate_mem.1
    · have cast_bound : (coordinate : ℝ) ≤ ((size - 2 : ℕ) : ℝ) := by exact_mod_cast coordinate_mem.2
      simpa only [Nat.cast_sub (by omega : 2 ≤ size), Nat.cast_ofNat] using cast_bound
  have first_bounds := real_bounds first_coordinate_mem
  have second_bounds := real_bounds second_coordinate_mem
  have separation := different_edge_sides_squared_distance_lower_bound firstSide secondSide different
    size_lower first_bounds.1 first_bounds.2 second_bounds.1 second_bounds.2
  simp only [NagamochiResource.EdgePoint.pointAt_nat] at separation
  have diameter := dilated_square_squared_distance_lt_twice_factor_sq square factor_positive
    first_mem second_mem
  nlinarith

end SquarePackingArchive.Nagamochi
