import SquarePackingArchive.Records.Square13
import SquarePackingArchive.StromquistSixLemma8

namespace SquarePackingArchive.BentzThirteen

theorem frame_weight_from_cubic {cosine sine quadraticWeight mixedWeight : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (cubic_nonnegative : ∀ parameter : ℝ, 0 ≤ parameter → parameter ≤ 1 →
      0 ≤ (1 - mixedWeight) + (2 * quadraticWeight - 1) * parameter +
        (1 + mixedWeight) * parameter ^ 2 - parameter ^ 3) :
    0 ≤ cosine + sine - 1 + quadraticWeight * sine ^ 2 - mixedWeight * cosine * sine := by
  have denominator_positive : 0 < 1 + cosine := by linarith
  have sine_le_one : sine ≤ 1 := by nlinarith [sq_nonneg cosine]
  let parameter := sine / (1 + cosine)
  have parameter_nonnegative : 0 ≤ parameter := div_nonneg sine_nonnegative denominator_positive.le
  have parameter_le_one : parameter ≤ 1 := (div_le_iff₀ denominator_positive).2 (by linarith)
  have cosine_identity : cosine + parameter * sine - 1 = 0 := by
    dsimp [parameter]
    field_simp
    nlinarith
  have ratio_identity : parameter * (1 + cosine) - sine = 0 := by
    dsimp [parameter]
    field_simp
    ring
  have sine_identity : sine * (1 + parameter ^ 2) - 2 * parameter = 0 := by
    linear_combination parameter * cosine_identity - ratio_identity
  have weight_identity :
      (cosine + sine - 1 + quadraticWeight * sine ^ 2 - mixedWeight * cosine * sine) *
        (1 + parameter ^ 2) = sine * ((1 - mixedWeight) +
          (2 * quadraticWeight - 1) * parameter + (1 + mixedWeight) * parameter ^ 2 - parameter ^ 3) := by
    linear_combination (1 - mixedWeight * sine) * (1 + parameter ^ 2) * cosine_identity +
      sine * (quadraticWeight + mixedWeight * parameter) * sine_identity
  have weighted := mul_nonneg sine_nonnegative (cubic_nonnegative parameter parameter_nonnegative parameter_le_one)
  have factor_positive : 0 < 1 + parameter ^ 2 := by positivity
  nlinarith

theorem near_horizontal_frame_weight {cosine sine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    0 ≤ cosine + sine - 1 + 43 / 500 * sine ^ 2 - 22 / 25 * cosine * sine := by
  apply frame_weight_from_cubic cosine_nonnegative sine_nonnegative unit
  intro parameter parameter_nonnegative parameter_le_one
  by_cases parameter_small : parameter ≤ 2 / 5
  · have cubic_bound := mul_nonneg (sq_nonneg parameter) (show 0 ≤ 2 / 5 - parameter by linarith)
    nlinarith [sq_nonneg (740 * parameter - 207)]
  · have quotient_nonnegative : 0 ≤ -parameter ^ 2 + 37 / 25 * parameter - 59 / 250 := by
      nlinarith [mul_nonneg (show 0 ≤ parameter - 2 / 5 by linarith) (show 0 ≤ 1 - parameter by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ parameter - 2 / 5 by linarith) quotient_nonnegative]

theorem extended_frame_weight {cosine sine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    0 ≤ cosine + sine - 1 + 6 / 25 * sine ^ 2 - 24 / 25 * cosine * sine := by
  apply frame_weight_from_cubic cosine_nonnegative sine_nonnegative unit
  intro parameter parameter_nonnegative parameter_le_one
  by_cases parameter_small : parameter ≤ 1 / 4
  · have cubic_bound := mul_nonneg (sq_nonneg parameter) (show 0 ≤ 1 / 4 - parameter by linarith)
    nlinarith [sq_nonneg (171 * parameter - 26)]
  · have quotient_nonnegative : 0 ≤ -parameter ^ 2 + 171 / 100 * parameter - 37 / 400 := by
      nlinarith [mul_nonneg parameter_nonnegative (show 0 ≤ 1 - parameter by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ parameter - 1 / 4 by linarith) quotient_nonnegative]

theorem ordinary_frame_weight {cosine sine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) :
    0 ≤ cosine + sine - 1 - 413 / 500 * cosine * sine := by
  have sum_lower : 1 ≤ cosine + sine := by nlinarith
  have sum_upper : cosine + sine ≤ 17 / 12 := by
    nlinarith [sq_nonneg (cosine - sine)]
  nlinarith [mul_nonneg (show 0 ≤ cosine + sine - 1 by linarith)
    (show 0 ≤ 17 / 12 - (cosine + sine) by linarith), mul_nonneg cosine_nonnegative sine_nonnegative]

structure LocalCornerConditions (cosine sine horizontal vertical : ℝ) : Prop where
  cosine_nonnegative : 0 ≤ cosine
  sine_nonnegative : 0 ≤ sine
  unit : cosine ^ 2 + sine ^ 2 = 1
  horizontal_bounds : |horizontal| ≤ 1 / 2
  vertical_bounds : |vertical| ≤ 1 / 2
  left_wall : horizontal * cosine - vertical * sine ≤ 1 - (cosine + sine) / 2
  bottom_wall : horizontal * sine + vertical * cosine ≤ 457 / 500 - (cosine + sine) / 2
  neighbor_missing : ¬ (|horizontal - 43 / 500 * cosine + 43 / 500 * sine| ≤ 1 / 2 ∧
    |vertical + 43 / 500 * sine + 43 / 500 * cosine| ≤ 1 / 2)
  diagonal_missing : ¬ (|horizontal + 13 / 20 * cosine + 92 / 125 * sine| ≤ 1 / 2 ∧
    |vertical - 13 / 20 * sine + 92 / 125 * cosine| ≤ 1 / 2)
  bottom_neighbor_missing : ¬ (|horizontal + cosine| ≤ 1 / 2 ∧ |vertical - sine| ≤ 1 / 2)

theorem LocalCornerConditions.neighbor_cases {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical) :
    horizontal < -(1 / 2) + 43 / 500 * (cosine - sine) ∨
      vertical > 1 / 2 - 43 / 500 * (cosine + sine) := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have weighted_left := mul_nonneg conditions.cosine_nonnegative (sub_nonneg.2 conditions.left_wall)
  have weighted_bottom := mul_nonneg conditions.sine_nonnegative (sub_nonneg.2 conditions.bottom_wall)
  have weighted_unit : horizontal * (cosine ^ 2 + sine ^ 2 - 1) = 0 := by rw [conditions.unit]; ring
  have neighbor_horizontal_upper : horizontal - 43 / 500 * cosine + 43 / 500 * sine ≤ 1 / 2 := by
    nlinarith [conditions.unit, conditions.cosine_nonnegative,
      mul_nonneg (show 0 ≤ 1 - cosine by linarith) (show 0 ≤ 1 - sine by linarith)]
  have missing := conditions.neighbor_missing
  simp only [abs_le, not_and_or, not_le] at missing
  rcases missing with (missing | missing) | (missing | missing)
  · exact Or.inl (by linarith)
  · linarith
  · linarith [conditions.cosine_nonnegative, conditions.sine_nonnegative]
  · exact Or.inr (by linarith)

theorem LocalCornerConditions.bottom_neighbor_cases {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical) :
    1 / 2 - cosine < horizontal ∨ vertical < sine - 1 / 2 := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have missing := conditions.bottom_neighbor_missing
  simp only [abs_le, not_and_or, not_le] at missing
  rcases missing with (missing | missing) | (missing | missing)
  · linarith [conditions.cosine_nonnegative]
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · linarith [conditions.sine_nonnegative]

theorem LocalCornerConditions.left_case_diagonal {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (left_case : horizontal < -(1 / 2) + 43 / 500 * (cosine - sine)) :
    sine < cosine ∧ 1 / 2 + 13 / 20 * sine - 92 / 125 * cosine < vertical := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have order : sine < cosine := by linarith
  have diagonal_bound : 92 / 125 * cosine + 13 / 20 * sine < 1 := by
    nlinarith [conditions.unit, sq_nonneg (325 * cosine - 368 * sine)]
  have missing := conditions.diagonal_missing
  simp only [abs_le, not_and_or, not_le] at missing
  refine ⟨order, ?_⟩
  rcases missing with (missing | missing) | (missing | missing)
  · linarith [conditions.cosine_nonnegative, conditions.sine_nonnegative]
  · linarith
  · linarith [conditions.cosine_nonnegative, conditions.sine_nonnegative]
  · linarith

theorem LocalCornerConditions.upper_case_diagonal {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (upper_case : 1 / 2 - 43 / 500 * (cosine + sine) < vertical) :
    1 / 2 - 13 / 20 * cosine - 92 / 125 * sine < horizontal ∨
      1 / 2 + 13 / 20 * sine - 92 / 125 * cosine < vertical := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have missing := conditions.diagonal_missing
  simp only [abs_le, not_and_or, not_le] at missing
  rcases missing with (missing | missing) | (missing | missing)
  · linarith [conditions.cosine_nonnegative, conditions.sine_nonnegative]
  · exact Or.inl (by linarith)
  · linarith [conditions.cosine_nonnegative]
  · exact Or.inr (by linarith)

theorem LocalCornerConditions.horizontal_line_upper {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical) :
    vertical - 3 / 25 * sine + 43 / 500 * cosine ≤ 1 / 2 := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  rcases conditions.bottom_neighbor_cases with horizontal_large | vertical_small
  · have weighted := mul_nonneg conditions.sine_nonnegative
      (show 0 ≤ horizontal - (1 / 2 - cosine) by linarith)
    have frame_bound := near_horizontal_frame_weight conditions.cosine_nonnegative conditions.sine_nonnegative conditions.unit
    by_cases cosine_positive : 0 < cosine
    · by_contra! outside
      have weighted_outside := mul_pos cosine_positive
        (show 0 < vertical - 3 / 25 * sine + 43 / 500 * cosine - 1 / 2 by linarith)
      nlinarith [conditions.bottom_wall, conditions.unit]
    · have cosine_zero : cosine = 0 := by linarith [conditions.cosine_nonnegative]
      rw [cosine_zero]
      linarith [conditions.sine_nonnegative]
  · linarith [conditions.cosine_nonnegative, conditions.sine_nonnegative]

theorem LocalCornerConditions.corner_missing_height {cosine sine horizontal vertical : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (corner_missing : ¬ (|horizontal + 43 / 500 * sine| ≤ 1 / 2 ∧
      |vertical + 43 / 500 * cosine| ≤ 1 / 2)) :
    1 / 2 - 43 / 500 * cosine < vertical := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have cosine_sine_nonnegative := mul_nonneg conditions.cosine_nonnegative conditions.sine_nonnegative
  simp only [abs_le, not_and_or, not_le] at corner_missing
  rcases corner_missing with (missing | missing) | (missing | missing)
  · linarith [conditions.sine_nonnegative]
  · rcases conditions.neighbor_cases with left_case | upper_case
    · linarith
    · have weighted_horizontal := mul_nonneg conditions.sine_nonnegative
        (show 0 ≤ horizontal - (1 / 2 - 43 / 500 * sine) by linarith)
      have weighted_vertical := mul_nonneg conditions.cosine_nonnegative
        (show 0 ≤ vertical - (1 / 2 - 43 / 500 * (cosine + sine)) by linarith)
      have frame_bound := ordinary_frame_weight conditions.cosine_nonnegative conditions.sine_nonnegative conditions.unit
      by_cases cosine_positive : 0 < cosine
      · have weighted_vertical_strict := mul_pos cosine_positive
          (show 0 < vertical - (1 / 2 - 43 / 500 * (cosine + sine)) by linarith)
        nlinarith [conditions.bottom_wall, conditions.unit]
      · have cosine_zero : cosine = 0 := by linarith [conditions.cosine_nonnegative]
        have sine_one : sine = 1 := by nlinarith [conditions.unit, conditions.sine_nonnegative]
        nlinarith [conditions.bottom_wall]
  · linarith [conditions.cosine_nonnegative]
  · linarith

theorem LocalCornerConditions.horizontal_replacement_upper {cosine sine horizontal vertical offset : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (offset_bounds : 3 / 25 ≤ offset ∧ offset ≤ 41 / 50)
    (clearance : offset ≤ 37 / 50 ∨ 1 / 2 - 43 / 500 * cosine < vertical) :
    horizontal + offset * cosine + 43 / 500 * sine ≤ 1 / 2 := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have offset_cosine_upper := mul_nonneg conditions.cosine_nonnegative (sub_nonneg.2 offset_bounds.2)
  have product_nonnegative := mul_nonneg conditions.cosine_nonnegative conditions.sine_nonnegative
  rcases conditions.neighbor_cases with left_case | upper_case
  · linarith [conditions.sine_nonnegative]
  · have sine_positive : 0 < sine := by
      by_contra! not_positive
      have sine_zero : sine = 0 := by linarith [conditions.sine_nonnegative]
      have cosine_one : cosine = 1 := by nlinarith [conditions.unit, conditions.cosine_nonnegative]
      nlinarith [conditions.bottom_wall]
    by_contra! outside
    have weighted_outside := mul_pos sine_positive
      (show 0 < horizontal + offset * cosine + 43 / 500 * sine - 1 / 2 by linarith)
    have frame_bound := ordinary_frame_weight conditions.cosine_nonnegative conditions.sine_nonnegative conditions.unit
    rcases clearance with ordinary | extended
    · have weighted_height := mul_nonneg conditions.cosine_nonnegative
        (show 0 ≤ vertical - (1 / 2 - 43 / 500 * (cosine + sine)) by linarith)
      have weighted_offset := mul_nonneg product_nonnegative (show 0 ≤ 37 / 50 - offset by linarith)
      nlinarith [conditions.bottom_wall, conditions.unit]
    · have weighted_height := mul_nonneg conditions.cosine_nonnegative
        (show 0 ≤ vertical - (1 / 2 - 43 / 500 * cosine) by linarith)
      have weighted_offset := mul_nonneg product_nonnegative (sub_nonneg.2 offset_bounds.2)
      nlinarith [conditions.bottom_wall, conditions.unit]

theorem LocalCornerConditions.horizontal_replacement {cosine sine horizontal vertical offset : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (offset_bounds : 3 / 25 ≤ offset ∧ offset ≤ 41 / 50)
    (clearance : offset ≤ 37 / 50 ∨ 1 / 2 - 43 / 500 * cosine < vertical) :
    |horizontal + offset * cosine + 43 / 500 * sine| ≤ 1 / 2 ∧
      |vertical - offset * sine + 43 / 500 * cosine| ≤ 1 / 2 := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have horizontal_lower := mul_nonneg conditions.cosine_nonnegative (show 0 ≤ offset by linarith)
  have offset_sine_upper := mul_nonneg conditions.sine_nonnegative (sub_nonneg.2 offset_bounds.2)
  have offset_sine_lower := mul_nonneg conditions.sine_nonnegative (sub_nonneg.2 offset_bounds.1)
  have vertical_upper := conditions.horizontal_line_upper
  rw [abs_le, abs_le]
  refine ⟨⟨by linarith [conditions.sine_nonnegative], conditions.horizontal_replacement_upper offset_bounds clearance⟩,
    ⟨?_, by linarith⟩⟩
  rcases conditions.neighbor_cases with left_case | upper_case
  · have diagonal := (conditions.left_case_diagonal left_case).2
    linarith
  · linarith

theorem LocalCornerConditions.lower_replacement_upper {cosine sine horizontal vertical offset : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (offset_bounds : 87 / 100 ≤ offset ∧ offset ≤ 24 / 25)
    (clearance : offset ≤ 87 / 100 ∨ 1 / 2 - 43 / 500 * cosine < vertical) :
    horizontal + offset * cosine - 77 / 500 * sine ≤ 1 / 2 := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have product_nonnegative := mul_nonneg conditions.cosine_nonnegative conditions.sine_nonnegative
  have frame_bound := extended_frame_weight conditions.cosine_nonnegative conditions.sine_nonnegative conditions.unit
  rcases clearance with ordinary | extended
  · rcases conditions.neighbor_cases with left_case | upper_case
    · have weighted_offset := mul_nonneg conditions.cosine_nonnegative (show 0 ≤ 87 / 100 - offset by linarith)
      linarith [conditions.sine_nonnegative]
    · have sine_positive : 0 < sine := by
        by_contra! not_positive
        have sine_zero : sine = 0 := by linarith [conditions.sine_nonnegative]
        have cosine_one : cosine = 1 := by nlinarith [conditions.unit, conditions.cosine_nonnegative]
        nlinarith [conditions.bottom_wall]
      by_contra! outside
      have weighted_outside := mul_pos sine_positive
        (show 0 < horizontal + offset * cosine - 77 / 500 * sine - 1 / 2 by linarith)
      have weighted_height := mul_nonneg conditions.cosine_nonnegative
        (show 0 ≤ vertical - (1 / 2 - 43 / 500 * (cosine + sine)) by linarith)
      have weighted_offset := mul_nonneg product_nonnegative (show 0 ≤ 87 / 100 - offset by linarith)
      nlinarith [conditions.bottom_wall, conditions.unit]
  · have sine_positive : 0 < sine := by
      by_contra! not_positive
      have sine_zero : sine = 0 := by linarith [conditions.sine_nonnegative]
      have cosine_one : cosine = 1 := by nlinarith [conditions.unit, conditions.cosine_nonnegative]
      nlinarith [conditions.bottom_wall]
    by_contra! outside
    have weighted_outside := mul_pos sine_positive
      (show 0 < horizontal + offset * cosine - 77 / 500 * sine - 1 / 2 by linarith)
    have weighted_height := mul_nonneg conditions.cosine_nonnegative
      (show 0 ≤ vertical - (1 / 2 - 43 / 500 * cosine) by linarith)
    have weighted_offset := mul_nonneg product_nonnegative (sub_nonneg.2 offset_bounds.2)
    nlinarith [conditions.bottom_wall, conditions.unit]

theorem LocalCornerConditions.lower_replacement {cosine sine horizontal vertical offset : ℝ}
    (conditions : LocalCornerConditions cosine sine horizontal vertical)
    (offset_bounds : 87 / 100 ≤ offset ∧ offset ≤ 24 / 25)
    (clearance : offset ≤ 87 / 100 ∨ 1 / 2 - 43 / 500 * cosine < vertical) :
    |horizontal + offset * cosine - 77 / 500 * sine| ≤ 1 / 2 ∧
      |vertical - offset * sine - 77 / 500 * cosine| ≤ 1 / 2 := by
  have horizontal_bounds := abs_le.1 conditions.horizontal_bounds
  have vertical_bounds := abs_le.1 conditions.vertical_bounds
  have cosine_le_one : cosine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [conditions.unit, sq_nonneg cosine]
  have offset_cosine_lower := mul_nonneg conditions.cosine_nonnegative (sub_nonneg.2 offset_bounds.1)
  have offset_sine_upper := mul_nonneg conditions.sine_nonnegative (sub_nonneg.2 offset_bounds.2)
  have offset_sine_nonnegative := mul_nonneg conditions.sine_nonnegative (show 0 ≤ offset by linarith)
  have first_weight : 89 / 100 * cosine + 31 / 100 * sine ≤ 1 := by
    nlinarith [conditions.unit, sq_nonneg (31 * cosine - 89 * sine)]
  have second_weight : 24 / 25 * sine + 6 / 25 * cosine ≤ 1 := by
    nlinarith [conditions.unit, sq_nonneg (6 * sine - 24 * cosine)]
  have horizontal_lower : -(1 / 2) ≤ horizontal + offset * cosine - 77 / 500 * sine := by
    rcases conditions.neighbor_cases with left_case | upper_case
    · have order := (conditions.left_case_diagonal left_case).1
      linarith [conditions.cosine_nonnegative]
    · rcases conditions.upper_case_diagonal upper_case with horizontal_large | vertical_large
      · linarith [conditions.cosine_nonnegative]
      · linarith
  rw [abs_le, abs_le]
  refine ⟨⟨horizontal_lower, conditions.lower_replacement_upper offset_bounds clearance⟩,
    ⟨?_, by linarith [conditions.cosine_nonnegative]⟩⟩
  rcases conditions.neighbor_cases with left_case | upper_case
  · have diagonal := (conditions.left_case_diagonal left_case).2
    linarith
  · rcases clearance with ordinary | extended
    · have weighted_offset := mul_nonneg conditions.sine_nonnegative (show 0 ≤ 87 / 100 - offset by linarith)
      linarith [conditions.sine_nonnegative]
    · linarith

theorem normalized_corner_conditions {square : PlacedSquare}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0) :
    LocalCornerConditions square.firstQuadrant.frame.cosine square.firstQuadrant.frame.sine
      (square.firstQuadrant.localX ⟨1, 457 / 500⟩) (square.firstQuadrant.localY ⟨1, 457 / 500⟩) := by
  have anchor_mem : square.firstQuadrant.Contains ⟨1, 457 / 500⟩ :=
    (square.firstQuadrant_contains_iff _).2 ((only_anchor 0).2 rfl)
  have anchor_bounds := (square.firstQuadrant.contains_iff_localCoordinates _).1 anchor_mem
  have walls := StromquistSix.local_wall_constraints ((square.firstQuadrant_fits_iff 4).2 fits) (⟨1, 457 / 500⟩ : Point)
  refine ⟨square.firstQuadrant_cosine_nonnegative, square.firstQuadrant_sine_nonnegative,
    square.firstQuadrant.frame.unit, anchor_bounds.1, anchor_bounds.2,
    by dsimp at walls; linarith [walls.1], walls.2, ?_, ?_, ?_⟩
  · intro local_mem
    have neighbor_mem : square.firstQuadrant.Contains (Records.Square13.initialPoints 1) := by
      rw [square.firstQuadrant.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;>
        norm_num [PlacedSquare.localX, PlacedSquare.localY, Records.Square13.initialPoints] <;> ring
    have impossible := (only_anchor 1).1 ((square.firstQuadrant_contains_iff _).1 neighbor_mem)
    norm_num [Fin.ext_iff] at impossible
  · intro local_mem
    have diagonal_mem : square.firstQuadrant.Contains (Records.Square13.initialPoints 12) := by
      rw [square.firstQuadrant.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;>
        norm_num [PlacedSquare.localX, PlacedSquare.localY, Records.Square13.initialPoints] <;> ring
    have impossible := (only_anchor 12).1 ((square.firstQuadrant_contains_iff _).1 diagonal_mem)
    norm_num [Fin.ext_iff] at impossible
  · intro local_mem
    have bottom_mem : square.firstQuadrant.Contains (Records.Square13.initialPoints 10) := by
      rw [square.firstQuadrant.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;>
        norm_num [PlacedSquare.localX, PlacedSquare.localY, Records.Square13.initialPoints] <;> ring
    have impossible := (only_anchor 10).1 ((square.firstQuadrant_contains_iff _).1 bottom_mem)
    norm_num [Fin.ext_iff] at impossible

theorem normalized_corner_missing_height {square : PlacedSquare}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0)
    (corner_missing : ¬ square.Contains ⟨1, 1⟩) :
    1 / 2 - 43 / 500 * square.firstQuadrant.frame.cosine < square.firstQuadrant.localY ⟨1, 457 / 500⟩ := by
  apply (normalized_corner_conditions fits only_anchor).corner_missing_height
  intro local_mem
  apply corner_missing
  apply (square.firstQuadrant_contains_iff _).1
  rw [square.firstQuadrant.contains_iff_localCoordinates]
  convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring

theorem corner_restricted_horizontal_segment {square : PlacedSquare} {horizontal : ℝ}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0)
    (horizontal_bounds : 28 / 25 ≤ horizontal ∧ horizontal ≤ 87 / 50) :
    square.Contains ⟨horizontal, 1⟩ := by
  have local_mem := (normalized_corner_conditions fits only_anchor).horizontal_replacement
    (offset := horizontal - 1) (by constructor <;> linarith) (Or.inl (by linarith))
  apply (square.firstQuadrant_contains_iff _).1
  rw [square.firstQuadrant.contains_iff_localCoordinates]
  convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring

theorem corner_restricted_lower_point {square : PlacedSquare}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0) :
    square.Contains ⟨187 / 100, 19 / 25⟩ := by
  have local_mem := (normalized_corner_conditions fits only_anchor).lower_replacement
    (offset := 87 / 100) (by norm_num) (Or.inl (by norm_num))
  apply (square.firstQuadrant_contains_iff _).1
  rw [square.firstQuadrant.contains_iff_localCoordinates]
  convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring

theorem lemma10_replacements {square : PlacedSquare}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0) :
    square.Contains ⟨28 / 25, 1⟩ ∧ square.Contains ⟨87 / 50, 1⟩ ∧ square.Contains ⟨187 / 100, 19 / 25⟩ := by
  exact ⟨corner_restricted_horizontal_segment fits only_anchor (by norm_num),
    corner_restricted_horizontal_segment fits only_anchor (by norm_num), corner_restricted_lower_point fits only_anchor⟩

theorem lemma11_replacements {square : PlacedSquare}
    (fits : square.Fits 4)
    (only_anchor : ∀ index : Fin 16, square.Contains (Records.Square13.initialPoints index) ↔ index = 0)
    (corner_missing : ¬ square.Contains ⟨1, 1⟩) :
    square.Contains ⟨91 / 50, 1⟩ ∧ square.Contains ⟨49 / 25, 19 / 25⟩ := by
  have conditions := normalized_corner_conditions fits only_anchor
  have clearance := normalized_corner_missing_height fits only_anchor corner_missing
  constructor
  · have local_mem := conditions.horizontal_replacement (offset := 41 / 50) (by norm_num) (Or.inr clearance)
    apply (square.firstQuadrant_contains_iff _).1
    rw [square.firstQuadrant.contains_iff_localCoordinates]
    convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring
  · have local_mem := conditions.lower_replacement (offset := 24 / 25) (by norm_num) (Or.inr clearance)
    apply (square.firstQuadrant_contains_iff _).1
    rw [square.firstQuadrant.contains_iff_localCoordinates]
    convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring

end SquarePackingArchive.BentzThirteen
