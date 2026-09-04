import SquarePackingArchive.Compensation
import SquarePackingArchive.NagamochiBadPacking

namespace SquarePackingArchive

open Function MeasureTheory Set

noncomputable def Packing.originalScore
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (size : ℕ) (factor : ℝ) (index : Fin squareCount) : ℝ :=
  (NagamochiResource.measure size ((packing.squares index).dilatedInteriorRegion factor)).toReal

lemma Packing.originalMeasure_finite
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 3 ≤ size) (index : Fin squareCount) :
    NagamochiResource.measure size ((packing.squares index).dilatedInteriorRegion factor) ≠ ⊤ :=
  ne_top_of_le_ne_top (NagamochiResource.measure_univ_ne_top size_lower)
    (measure_mono (subset_univ _))

lemma Packing.mem_badSquares_iff_originalScore
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 3 ≤ size) (index : Fin squareCount) :
    index ∈ packing.badSquares size factor ↔ packing.originalScore size factor index ≤ 1 := by
  classical
  simp only [Packing.badSquares, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [Packing.originalScore, ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal (b := (1 : ENNReal))
      (packing.originalMeasure_finite size_lower index) (by finiteness)).symm

lemma Packing.originalScore_gt_of_measure_bound
    {squareCount size : ℕ} {side factor bound : ℝ} (packing : Packing squareCount side)
    (size_lower : 3 ≤ size) (index : Fin squareCount) (bound_nonnegative : 0 ≤ bound)
    (score_bound : ENNReal.ofReal bound <
      NagamochiResource.measure size ((packing.squares index).dilatedInteriorRegion factor)) :
    bound < packing.originalScore size factor index :=
  (ENNReal.ofReal_lt_iff_lt_toReal bound_nonnegative (packing.originalMeasure_finite size_lower index)).mp score_bound

theorem Packing.squareMinusTwo_originalScore_sum_le_card
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_positive : 0 < factor) :
    ∑ index, packing.originalScore size factor index ≤ ((size * size - 2 : ℕ) : ℝ) := by
  have mass_finite := NagamochiResource.measure_univ_ne_top size_lower
  have score_bound := finiteFamily_real_score_sum_le_mass (NagamochiResource.measure size) mass_finite
    (fun index => (packing.squares index).dilatedInteriorRegion factor)
    (fun index => (packing.squares index).measurableSet_dilatedInteriorRegion factor_positive.ne')
    (by
      intro first second different
      exact PlacedSquare.disjoint_dilatedInteriorRegion
        (packing.disjoint first second different) factor_positive.ne')
  rw [NagamochiResource.measure_univ size_lower] at score_bound
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_lower
  rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ (size : ℝ) ^ 2 - 2)] at score_bound
  have count_identity : ((size * size - 2 : ℕ) : ℝ) = (size : ℝ) ^ 2 - 2 := by
    rw [Nat.cast_sub (by nlinarith : 2 ≤ size * size), Nat.cast_mul, Nat.cast_ofNat, pow_two]
  simpa only [Packing.originalScore, count_identity] using score_bound

theorem Packing.squareMinusTwo_impossible_of_compensation
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_positive : 0 < factor)
    (assigned : packing.badSquares size factor → Fin (size * size - 2))
    (credit : packing.badSquares size factor → ℝ)
    (assigned_not_bad : ∀ origin, assigned origin ∉ packing.badSquares size factor)
    (bad_repaid : ∀ origin, 1 < packing.originalScore size factor origin.val + credit origin)
    (others_repaid : ∀ index, index ∉ packing.badSquares size factor →
      1 + ∑ origin : packing.badSquares size factor,
        (if assigned origin = index then credit origin else 0) < packing.originalScore size factor index) :
    False := by
  have count_positive : 0 < size * size - 2 := by
    have square_lower : 2 < size * size := by nlinarith
    omega
  have score_strict := finite_scores_sum_gt_card_of_compensation count_positive
    (packing.originalScore size factor) (packing.badSquares size factor) assigned credit
    assigned_not_bad bad_repaid others_repaid
  exact (not_lt_of_ge (packing.squareMinusTwo_originalScore_sum_le_card size_lower factor_positive)) score_strict

end SquarePackingArchive
