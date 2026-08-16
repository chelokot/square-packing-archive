import SquarePackingArchive.NagamochiLemmas
import SquarePackingArchive.Records.NearSquare

namespace SquarePackingArchive

open Function MeasureTheory Set

def NagamochiResource.ScoresDilatedSquares (size : ℕ) : Prop :=
  ∀ (factor : ℝ) (square : PlacedSquare),
    1 < factor →
      factor ≤ 101 / 100 →
        square.dilatedInteriorRegion factor ⊆ containerRegion size →
          1 < NagamochiResource.measure size
            (square.dilatedInteriorRegion factor)

lemma Packing.side_positive
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (squareCount_positive : 0 < squareCount) :
    0 < side := by
  have positive_real : (0 : ℝ) < squareCount := by exact_mod_cast squareCount_positive
  have side_sq_positive : 0 < side ^ 2 :=
    positive_real.trans_le packing.squareCount_le_side_sq
  have side_nonzero : side ≠ 0 := by
    intro side_zero
    rw [side_zero] at side_sq_positive
    norm_num at side_sq_positive
  exact lt_of_le_of_ne packing.side_nonnegative (Ne.symm side_nonzero)

theorem Packing.squareCount_lt_nagamochiMass
    {squareCount size : ℕ} {side : ℝ}
    (packing : Packing squareCount side)
    (squareCount_positive : 0 < squareCount)
    (size_at_least_three : 3 ≤ size)
    (side_lt_size : side < size)
    (scores : NagamochiResource.ScoresDilatedSquares size) :
    squareCount < size * size - 2 := by
  have side_positive := packing.side_positive squareCount_positive
  have one_lt_size_div_side : 1 < (size : ℝ) / side := by
    rw [lt_div_iff₀ side_positive]
    simpa only [one_mul] using side_lt_size
  have one_lt_upper : 1 < min (101 / 100 : ℝ) ((size : ℝ) / side) := by
    rw [lt_min_iff]
    exact ⟨by norm_num, one_lt_size_div_side⟩
  rcases exists_between one_lt_upper with ⟨factor, factor_gt_one, factor_lt_upper⟩
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_nonzero : factor ≠ 0 := factor_positive.ne'
  have factor_at_most : factor ≤ 101 / 100 :=
    le_of_lt (factor_lt_upper.trans_le (min_le_left _ _))
  have scaled_side_lt : factor * side < size := by
    rw [← lt_div_iff₀ side_positive]
    exact factor_lt_upper.trans_le (min_le_right _ _)
  let regions : Fin squareCount → Set Plane :=
    fun index => (packing.squares index).dilatedInteriorRegion factor
  have regions_measurable : ∀ index, MeasurableSet (regions index) := by
    intro index
    exact (packing.squares index).measurableSet_dilatedInteriorRegion factor_nonzero
  have regions_disjoint : Pairwise (Disjoint on regions) := by
    intro left right different
    exact PlacedSquare.disjoint_dilatedInteriorRegion
      (packing.disjoint left right different) factor_nonzero
  have regions_score :
      ∀ index, 1 < NagamochiResource.measure size (regions index) := by
    intro index
    apply scores factor (packing.squares index) factor_gt_one factor_at_most
    exact (packing.squares index).dilatedInteriorRegion_subset_containerRegion
      (packing.fits index) factor_positive.le scaled_side_lt.le
  have count_lt_mass := finiteFamily_card_lt_resourceMass
    (NagamochiResource.measure size) squareCount_positive
    (NagamochiResource.measure_univ_ne_top size_at_least_three)
    regions regions_measurable regions_disjoint regions_score
  rw [NagamochiResource.measure_univ_nat size_at_least_three] at count_lt_mass
  exact_mod_cast count_lt_mass

theorem Records.NearSquare.squareMinusTwo_isMinimumSide_of_nagamochiScores
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    (scores : NagamochiResource.ScoresDilatedSquares size) :
    IsMinimumSide (size * size - 2) size := by
  constructor
  · exact Records.NearSquare.squareMinusTwo_hasPacking size
  · intro candidateSide hasPacking
    by_contra side_too_small
    have square_product_at_least_nine : 9 ≤ size * size :=
      Nat.mul_le_mul size_at_least_three size_at_least_three
    have count_lt := hasPacking.some.squareCount_lt_nagamochiMass
      (by omega) size_at_least_three (lt_of_not_ge side_too_small) scores
    omega

theorem Records.NearSquare.squareMinusOne_isMinimumSide_of_nagamochiScores
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    (scores : NagamochiResource.ScoresDilatedSquares size) :
    IsMinimumSide (size * size - 1) size := by
  constructor
  · exact Records.NearSquare.squareMinusOne_hasPacking size
  · intro candidateSide hasPacking
    have two_removed_packing := hasPacking.mono (by omega : size * size - 2 ≤ size * size - 1)
    exact (Records.NearSquare.squareMinusTwo_isMinimumSide_of_nagamochiScores
      size_at_least_three scores).2 candidateSide two_removed_packing

end SquarePackingArchive
