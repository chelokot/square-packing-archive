import SquarePackingArchive.NagamochiCapLowerBound

namespace SquarePackingArchive.Nagamochi

private lemma positive_bernstein_quartic
    {parameter coefficientZero coefficientOne coefficientTwo coefficientThree coefficientFour : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_at_most : parameter ≤ 1)
    (zero_positive : 0 < coefficientZero) (one_positive : 0 < coefficientOne)
    (two_positive : 0 < coefficientTwo) (three_positive : 0 < coefficientThree)
    (four_positive : 0 < coefficientFour) :
    0 < coefficientZero * (1 - parameter) ^ 4 +
      coefficientOne * parameter * (1 - parameter) ^ 3 +
      coefficientTwo * parameter ^ 2 * (1 - parameter) ^ 2 +
      coefficientThree * parameter ^ 3 * (1 - parameter) + coefficientFour * parameter ^ 4 := by
  have shifted_nonnegative : 0 ≤ 1 - parameter := by linarith
  by_cases strict : parameter < 1
  · have shifted_positive : 0 < 1 - parameter := by linarith
    positivity
  · have identity : parameter = 1 := by linarith
    subst parameter
    simpa using four_positive

lemma chain_endpoint_quartic_negative {parameter : ℝ}
    (parameter_positive : 0 < parameter) (parameter_lt_one : parameter < 1) :
    5 * parameter ^ 4 + 10 * parameter ^ 3 - 40 * parameter ^ 2 + 26 * parameter - 5 < 0 := by
  by_cases first_interval : parameter ≤ 1 / 4
  · have certificate := positive_bernstein_quartic
      (parameter := 4 * parameter)
      (coefficientZero := 5) (coefficientOne := 27 / 2) (coefficientTwo := 13)
      (coefficientThree := 171 / 32) (coefficientFour := 211 / 256)
      (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    nlinarith
  · by_cases second_interval : parameter ≤ 1 / 2
    · have certificate := positive_bernstein_quartic
        (parameter := 4 * parameter - 1)
        (coefficientZero := 211 / 256) (coefficientOne := 5 / 4) (coefficientTwo := 23 / 32)
        (coefficientThree := 3 / 4) (coefficientFour := 7 / 16)
        (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      nlinarith
    · have certificate := positive_bernstein_quartic
        (parameter := 2 * parameter - 1)
        (coefficientZero := 7 / 16) (coefficientOne := 15 / 4) (coefficientTwo := 13)
        (coefficientThree := 14) (coefficientFour := 4)
        (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      nlinarith

lemma no_crossing_exit_deficit_lt_half_cap_surplus {cosine sine : ℝ}
    (cosine_positive : 0 < cosine) (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) / cosine ^ 2 <
      (cosine + sine - 1) / (2 * (cosine + sine + 1)) := by
  let parameter := sine / (1 + cosine)
  have denominator_positive : 0 < 1 + cosine := by positivity
  have parameter_positive : 0 < parameter := div_pos sine_positive denominator_positive
  have sine_lt_one : sine < 1 := by nlinarith [sq_pos_of_pos cosine_positive]
  have parameter_lt_one : parameter < 1 := by
    dsimp [parameter]
    rw [div_lt_one denominator_positive]
    linarith
  have cosine_eq : cosine = (1 - parameter ^ 2) / (1 + parameter ^ 2) := by
    dsimp [parameter]
    field_simp
    nlinarith [unit]
  have sine_eq : sine = 2 * parameter / (1 + parameter ^ 2) := by
    dsimp [parameter]
    field_simp
    nlinarith [unit]
  have quartic_negative := chain_endpoint_quartic_negative parameter_positive parameter_lt_one
  have identity :
      (cosine ^ 2 * (cosine + sine - 1) -
        2 * ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) * (cosine + sine + 1)) *
        (5 * (1 + parameter ^ 2) ^ 3) =
      (2 * parameter * (parameter + 1)) *
        -(5 * parameter ^ 4 + 10 * parameter ^ 3 - 40 * parameter ^ 2 + 26 * parameter - 5) := by
    rw [cosine_eq, sine_eq]
    field_simp
    ring
  have difference_positive : 0 < cosine ^ 2 * (cosine + sine - 1) -
      2 * ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) * (cosine + sine + 1) := by
    apply (mul_pos_iff_of_pos_right (by positivity : 0 < 5 * (1 + parameter ^ 2) ^ 3)).mp
    rw [identity]
    exact mul_pos (by positivity) (neg_pos.mpr quartic_negative)
  apply (div_lt_div_iff₀ (sq_pos_of_pos cosine_positive)
    (by positivity : 0 < 2 * (cosine + sine + 1))).mpr
  linarith

lemma terminal_height_potential_repaid
    {cosine sine exitHeight : ℝ}
    (cosine_positive : 0 < cosine)
    (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (sine_at_most : sine ≤ 9 / 10)
    (exit_above_grid : 9 / 10 < exitHeight)
    (lower_local_bound : cosine - (9 / 10) * sine ^ 2 < cosine ^ 2 * exitHeight) :
    1 < (cosine + sine) / (1 + cosine + sine) + exitHeight / 2 := by
  have cosine_at_most : cosine ≤ 1 := by nlinarith [sq_nonneg sine]
  have denominator_positive : 0 < 1 + cosine + sine := by positivity
  suffices height_bound : 2 < exitHeight * (1 + cosine + sine) by
    have fraction_bound : 2 / (1 + cosine + sine) < exitHeight :=
      (div_lt_iff₀ denominator_positive).2 height_bound
    have identity :
        (cosine + sine) / (1 + cosine + sine) +
          (2 / (1 + cosine + sine)) / 2 = 1 := by
      field_simp
      ring
    linarith
  by_cases small_sine : sine ≤ 2 / 5
  · have cosine_lower : 9 / 10 < cosine := by
      by_contra! contrary
      nlinarith [mul_nonneg (sub_nonneg.mpr contrary) cosine_positive.le,
        mul_nonneg (sub_nonneg.mpr small_sine) sine_positive.le]
    have sum_at_most : 1 + cosine + sine ≤ 12 / 5 := by linarith
    have product_at_most : sine * (1 + cosine + sine) ≤ 24 / 25 := by
      calc
        sine * (1 + cosine + sine) ≤ (2 / 5) * (12 / 5) :=
          mul_le_mul small_sine sum_at_most denominator_positive.le (by norm_num)
        _ = 24 / 25 := by norm_num
    have strict_remainder : 0 < cosine - (9 / 10) * sine * (1 + cosine + sine) := by
      nlinarith
    have numerator_positive :
        2 * cosine ^ 2 < (cosine - (9 / 10) * sine ^ 2) * (1 + cosine + sine) := by
      nlinarith [mul_pos sine_positive strict_remainder,
        mul_nonneg cosine_positive.le (sub_nonneg.mpr cosine_at_most)]
    have multiplied_local := mul_lt_mul_of_pos_right lower_local_bound denominator_positive
    have multiplied_height : cosine ^ 2 * 2 < cosine ^ 2 * (exitHeight * (1 + cosine + sine)) := by
      nlinarith
    exact (mul_lt_mul_iff_right₀ (pow_pos cosine_positive 2)).1 multiplied_height
  · have sine_lower : 2 / 5 ≤ sine := by linarith
    have cosine_lower : 2 / 5 < cosine := by
      by_contra! contrary
      nlinarith [mul_nonneg (sub_nonneg.mpr contrary) cosine_positive.le,
        mul_nonneg (sub_nonneg.mpr sine_at_most) sine_positive.le]
    have sum_lower : 11 / 9 < cosine + sine := by
      have product_nonnegative := mul_nonneg
        (sub_nonneg.mpr cosine_lower.le) (sub_nonneg.mpr sine_lower)
      by_contra! contrary
      nlinarith [mul_nonneg (sub_nonneg.mpr contrary)
        (show 0 ≤ cosine + sine + 11 / 9 by positivity)]
    nlinarith [mul_pos (sub_pos.mpr exit_above_grid) denominator_positive]

lemma terminal_height_potential_repaid_of_local_geometry
    {cosine sine factor bottomHeight horizontalOffset exitHeight : ℝ}
    (cosine_positive : 0 < cosine)
    (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (factor_gt_one : 1 < factor)
    (bottom_nonnegative : 0 ≤ bottomHeight)
    (rightmost_vertex_below_grid : bottomHeight + factor * sine ≤ 9 / 10)
    (point_local_positive : 0 < cosine * horizontalOffset + sine * (9 / 10 - bottomHeight))
    (exit_identity : cosine * (exitHeight - bottomHeight) = factor + sine * horizontalOffset)
    (exit_above_grid : 9 / 10 < exitHeight) :
    1 < (cosine + sine) / (1 + cosine + sine) + exitHeight / 2 := by
  have sine_at_most : sine ≤ 9 / 10 := by
    nlinarith [mul_lt_mul_of_pos_right factor_gt_one sine_positive]
  have lower_local_bound : cosine - (9 / 10) * sine ^ 2 < cosine ^ 2 * exitHeight := by
    have scaled_local := mul_pos sine_positive point_local_positive
    have scaled_identity := congrArg (fun value : ℝ => cosine * value) exit_identity
    have scaled_unit := congrArg (fun value : ℝ => bottomHeight * value) unit
    have factor_strict := mul_lt_mul_of_pos_right factor_gt_one cosine_positive
    nlinarith
  exact terminal_height_potential_repaid cosine_positive sine_positive unit sine_at_most
    exit_above_grid lower_local_bound

lemma endpoint_height_potential_repaid
    {cosine sine exitHeight : ℝ}
    (cosine_positive : 0 < cosine)
    (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (exit_deficit_bound : 1 - exitHeight ≤
      ((1 - cosine) * (1 - sine) - sine ^ 2 / 10) / cosine ^ 2) :
    1 + (1 - exitHeight) / 2 <
      (cosine + sine) / (1 + cosine + sine) + exitHeight / 2 := by
  have strict_bound := no_crossing_exit_deficit_lt_half_cap_surplus
    cosine_positive sine_positive unit
  have identity : (cosine + sine - 1) / (2 * (cosine + sine + 1)) =
      (cosine + sine) / (1 + cosine + sine) - 1 / 2 := by
    have denominator_nonzero : cosine + sine + 1 ≠ 0 := by positivity
    have other_denominator_nonzero : 1 + cosine + sine ≠ 0 := by positivity
    field_simp
    ring
  rw [identity] at strict_bound
  linarith

end SquarePackingArchive.Nagamochi
