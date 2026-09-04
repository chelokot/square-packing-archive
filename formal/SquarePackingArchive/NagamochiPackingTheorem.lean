import SquarePackingArchive.NagamochiVerifiedTransfer
import SquarePackingArchive.Records.Square7

namespace SquarePackingArchive

open Set

theorem Packing.squareMinusTwo_impossible_of_scaled_fits
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size) :
    False := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have size_at_least_three : 3 ≤ size := by omega
  obtain ⟨cornerAssignment, corner_injective, corner_mem⟩ := packing.badSquares_corner_embedding
    size_lower factor_gt_one factor_at_most scaled_side_le
  let sourceCorner := fun origin => (cornerAssignment origin).val
  have source_injective : Function.Injective sourceCorner := by
    intro first second same
    exact corner_injective (Subtype.ext same)
  have transfers (origin : packing.badSquares size factor) :
      ∃ owner credit, 0 ≤ credit ∧
        1 < packing.originalScore size factor origin.val + credit ∧
        Nagamochi.TerminalSupport packing size factor (sourceCorner origin) owner ∧
        1 + (packing.terminalCapacity size factor owner : ℝ) * credit <
          packing.originalScore size factor owner := by
    have bad : NagamochiResource.measure size ((packing.squares origin.val).dilatedInteriorRegion factor) ≤ 1 := by
      simpa [Packing.badSquares] using origin.property
    exact Nagamochi.bad_corner_owner_has_capacity_transfer packing size_lower factor_gt_one
      factor_at_most scaled_side_le (sourceCorner origin) origin.val (corner_mem origin) bad
  choose assigned credit credit_nonnegative bad_repaid support target_repaid using transfers
  have assigned_not_bad : ∀ origin, assigned origin ∉ packing.badSquares size factor := by
    intro origin assigned_bad
    have bad_bound := (packing.mem_badSquares_iff_originalScore size_at_least_three _).mp assigned_bad
    have positive_credit := mul_nonneg
      (Nat.cast_nonneg (packing.terminalCapacity size factor (assigned origin))) (credit_nonnegative origin)
    linarith [target_repaid origin]
  have others_baseline : ∀ index, index ∉ packing.badSquares size factor →
      1 < packing.originalScore size factor index := by
    intro index not_bad
    exact lt_of_not_ge fun bound => not_bad
      ((packing.mem_badSquares_iff_originalScore size_at_least_three index).mpr bound)
  have square_lower : 2 < size * size := by nlinarith
  have count_positive : 0 < size * size - 2 := by omega
  have score_sum_strict := finite_scores_sum_gt_card_of_capacity_compensation count_positive
    (packing.originalScore size factor) (packing.badSquares size factor) assigned credit
    (packing.terminalCapacity size factor) assigned_not_bad credit_nonnegative bad_repaid
    (packing.terminalAssignment_fiber_card_le_capacity size_lower factor_positive factor_at_most
      (packing.badSquares size factor) sourceCorner source_injective assigned support)
    target_repaid others_baseline
  exact (not_lt_of_ge (packing.squareMinusTwo_originalScore_sum_le_card size_at_least_three
    factor_positive)) score_sum_strict

theorem Packing.squareMinusTwo_side_ge
    {size : ℕ} {side : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) :
    (size : ℝ) ≤ side := by
  by_contra smaller
  have side_lt_size : side < size := lt_of_not_ge smaller
  have square_lower : 2 < size * size := by nlinarith
  have count_positive : 0 < size * size - 2 := by omega
  have side_positive := packing.side_positive count_positive
  have ratio_gt_one : 1 < (size : ℝ) / side := by
    rw [lt_div_iff₀ side_positive]
    simpa using side_lt_size
  have upper_gt_one : 1 < min (101 / 100 : ℝ) ((size : ℝ) / side) :=
    lt_min (by norm_num) ratio_gt_one
  obtain ⟨factor, factor_gt_one, factor_lt_upper⟩ := exists_between upper_gt_one
  have factor_at_most : factor ≤ 101 / 100 :=
    (factor_lt_upper.trans_le (min_le_left _ _)).le
  have scaled_side_lt : factor * side < size := by
    rw [← lt_div_iff₀ side_positive]
    exact factor_lt_upper.trans_le (min_le_right _ _)
  exact packing.squareMinusTwo_impossible_of_scaled_fits size_lower factor_gt_one
    factor_at_most scaled_side_lt.le

theorem Records.NearSquare.squareMinusTwo_isMinimumSide
    {size : ℕ} (size_lower : 2 ≤ size) :
    IsMinimumSide (size * size - 2) size := by
  by_cases size_two : size = 2
  · subst size
    simpa using Records.NearSquare.s2_eq_two
  by_cases size_three : size = 3
  · subst size
    simpa using Records.Square7.s7_eq_three
  exact ⟨Records.NearSquare.squareMinusTwo_hasPacking size,
    fun _ packing => packing.some.squareMinusTwo_side_ge (by omega)⟩

theorem Records.NearSquare.s14_eq_four : IsMinimumSide 14 4 := by
  simpa using (Records.NearSquare.squareMinusTwo_isMinimumSide (size := 4) (by norm_num))

theorem Records.NearSquare.s62_eq_eight : IsMinimumSide 62 8 := by
  simpa using (Records.NearSquare.squareMinusTwo_isMinimumSide (size := 8) (by norm_num))

theorem Records.NearSquare.s79_eq_nine : IsMinimumSide 79 9 := by
  simpa using (Records.NearSquare.squareMinusTwo_isMinimumSide (size := 9) (by norm_num))

theorem Records.NearSquare.s98_eq_ten : IsMinimumSide 98 10 := by
  simpa using (Records.NearSquare.squareMinusTwo_isMinimumSide (size := 10) (by norm_num))

end SquarePackingArchive
