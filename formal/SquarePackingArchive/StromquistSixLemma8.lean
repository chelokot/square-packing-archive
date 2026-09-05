import SquarePackingArchive.Records.Square6

namespace SquarePackingArchive.StromquistSix

set_option maxHeartbeats 1000000 in
theorem corner_reach_sum {cosine sine horizontal vertical : ℝ}
    (cosine_positive : 0 < cosine) (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (horizontal_bounds : -(1 / 2) ≤ horizontal ∧ horizontal ≤ 1 / 2)
    (vertical_bounds : -(1 / 2) ≤ vertical ∧ vertical ≤ 1 / 2)
    (left_wall : (cosine + sine) / 2 ≤ 1 - horizontal * cosine + vertical * sine)
    (north_missing : (1 - sine) / 2 < horizontal ∨ (1 - cosine) / 2 < vertical) :
    1 / 2 ≤ min ((1 / 2 - horizontal) / cosine) ((1 / 2 + vertical) / sine) +
      min ((1 / 2 + horizontal) / sine) ((1 / 2 + vertical) / cosine) := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [sq_nonneg cosine]
  have sum_ge_one : 1 ≤ cosine + sine := by nlinarith [mul_pos cosine_positive sine_positive]
  have first_nonnegative : 0 ≤ (1 / 2 - horizontal) / cosine := div_nonneg (by linarith) (le_of_lt cosine_positive)
  have second_nonnegative : 0 ≤ (1 / 2 + vertical) / sine := div_nonneg (by linarith) (le_of_lt sine_positive)
  have third_nonnegative : 0 ≤ (1 / 2 + horizontal) / sine := div_nonneg (by linarith) (le_of_lt sine_positive)
  have fourth_nonnegative : 0 ≤ (1 / 2 + vertical) / cosine := div_nonneg (by linarith) (le_of_lt cosine_positive)
  have first_third : 1 ≤ (1 / 2 - horizontal) / cosine + (1 / 2 + horizontal) / sine := by
    have first : 1 / 2 - horizontal ≤ (1 / 2 - horizontal) / cosine :=
      (le_div_iff₀ cosine_positive).2 (by nlinarith)
    have third : 1 / 2 + horizontal ≤ (1 / 2 + horizontal) / sine :=
      (le_div_iff₀ sine_positive).2 (by nlinarith)
    linarith
  have remaining :
      1 / 2 ≤ (1 / 2 - horizontal) / cosine + (1 / 2 + vertical) / cosine ∧
      1 / 2 ≤ (1 / 2 + vertical) / sine + (1 / 2 + horizontal) / sine ∧
      1 / 2 ≤ (1 / 2 + vertical) / sine + (1 / 2 + vertical) / cosine := by
    rcases north_missing with horizontal_large | vertical_large
    · have horizontal_nonnegative : 0 ≤ horizontal := by linarith
      have third_ge_half : 1 / 2 ≤ (1 / 2 + horizontal) / sine :=
        (le_div_iff₀ sine_positive).2 (by linarith)
      have first_fourth : cosine / 2 ≤ 1 - horizontal + vertical := by
        have frame_bound : cosine * sine / 2 ≤ cosine + sine - 1 := by
          nlinarith [mul_nonneg (sub_nonneg.2 sum_ge_one)
            (show 0 ≤ 3 - (cosine + sine) by linarith)]
        by_cases order : sine ≤ cosine
        · have special : 0 ≤ cosine + sine - 1 + sine ^ 2 / 2 - cosine * sine := by
            nlinarith [mul_nonneg (show 0 ≤ 1 - cosine by linarith)
              (show 0 ≤ cosine + 2 * sine - 1 by linarith)]
          have weighted := mul_nonneg (sub_nonneg.2 order)
            (show 0 ≤ horizontal - (1 - sine) / 2 by linarith)
          nlinarith
        · have weighted := mul_nonneg (show 0 ≤ sine - cosine by linarith)
            (show 0 ≤ 1 / 2 - horizontal by linarith)
          nlinarith
      have second_fourth : cosine * sine / 2 ≤ (1 / 2 + vertical) * (cosine + sine) := by
        have frame_bound : 0 ≤
            (cosine + sine - 1 - cosine * sine / 2) * (cosine + sine) - sine ^ 2 * cosine / 2 := by
          have factor_nonnegative := mul_nonneg (sq_nonneg (1 - sine))
            (show 0 ≤ 1 - cosine + sine / 2 by linarith)
          nlinarith [unit, mul_nonneg (show 0 ≤ sine by linarith) (sq_nonneg (cosine + sine)),
            show sine * (cosine ^ 2 + sine ^ 2 - 1) = 0 by rw [unit]; ring]
        have weighted_horizontal := mul_nonneg (show 0 ≤ cosine by linarith)
          (show 0 ≤ horizontal - (1 - sine) / 2 by linarith)
        have weighted_wall := mul_nonneg (show 0 ≤ cosine + sine by linarith)
          (show 0 ≤ (1 / 2 + vertical) * sine - (cosine + sine - 1 - cosine * sine / 2) by nlinarith)
        nlinarith
      refine ⟨?_, by linarith, ?_⟩
      · rw [← add_div, le_div_iff₀ cosine_positive]
        linarith
      · have combine : (1 / 2 + vertical) / sine + (1 / 2 + vertical) / cosine =
            ((1 / 2 + vertical) * (cosine + sine)) / (sine * cosine) := by
          field_simp
        rw [combine, le_div_iff₀ (mul_pos sine_positive cosine_positive)]
        linarith
    · have second_ge_half : 1 / 2 ≤ (1 / 2 + vertical) / sine :=
        (le_div_iff₀ sine_positive).2 (by nlinarith)
      have fourth_ge_half : 1 / 2 ≤ (1 / 2 + vertical) / cosine :=
        (le_div_iff₀ cosine_positive).2 (by nlinarith)
      exact ⟨by linarith, by linarith, by linarith⟩
  rcases min_cases ((1 / 2 - horizontal) / cosine) ((1 / 2 + vertical) / sine) with first | second <;>
    rcases min_cases ((1 / 2 + horizontal) / sine) ((1 / 2 + vertical) / cosine) with third | fourth
  · rw [first.1, third.1]; linarith
  · rw [first.1, fourth.1]; exact remaining.1
  · rw [second.1, third.1]; exact remaining.2.1
  · rw [second.1, fourth.1]; exact remaining.2.2

set_option maxHeartbeats 1000000 in
theorem midpoint_gap_sum {cosine sine horizontal vertical : ℝ}
    (cosine_positive : 0 < cosine) (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (horizontal_large : (1 - cosine) / 2 < horizontal)
    (vertical_large : (1 - sine) / 2 < vertical)
    (bottom_wall : horizontal * sine + vertical * cosine ≤ 1 - (cosine + sine) / 2) :
    0 < (vertical - 1 / 2 + sine / 2) / sine ∧
    0 < (vertical - 1 / 2 + sine / 2) / cosine ∧
    (vertical - 1 / 2 + sine / 2) / sine +
      (vertical - 1 / 2 + sine / 2) / cosine < 1 / 2 := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [sq_nonneg cosine]
  have numerator_positive : 0 < vertical - 1 / 2 + sine / 2 := by linarith
  refine ⟨div_pos numerator_positive sine_positive, div_pos numerator_positive cosine_positive, ?_⟩
  have strict_bound : (vertical - 1 / 2 + sine / 2) * cosine < (1 - cosine) * (1 - sine) := by
    nlinarith [mul_pos sine_positive (show 0 < horizontal - (1 - cosine) / 2 by linarith)]
  have frame_bound : 2 * (1 - cosine) * (1 - sine) * (cosine + sine) ≤ cosine ^ 2 * sine := by
    have product_bound : 2 * sine * (cosine + sine) ≤ (1 + cosine) * (1 + sine) := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - sine by linarith)
        (show 0 ≤ 1 + cosine + 2 * sine by linarith)]
    have cancellation :
        (cosine ^ 2 * sine - 2 * (1 - cosine) * (1 - sine) * (cosine + sine)) *
          ((1 + cosine) * (1 + sine)) =
        cosine ^ 2 * sine * ((1 + cosine) * (1 + sine) - 2 * sine * (cosine + sine)) := by
      nlinarith [show (cosine ^ 2 + sine ^ 2 - 1) *
          (2 * (cosine + sine) * (1 - sine ^ 2)) = 0 by rw [unit]; ring]
    have weighted := mul_nonneg (show 0 ≤ cosine ^ 2 * sine by positivity)
      (sub_nonneg.2 product_bound)
    have factor_positive : 0 < (1 + cosine) * (1 + sine) := by positivity
    nlinarith
  have multiplied := mul_lt_mul_of_pos_right strict_bound (show 0 < cosine + sine by linarith)
  have desired : (vertical - 1 / 2 + sine / 2) * (cosine + sine) < sine * cosine / 2 := by
    nlinarith
  have combine : (vertical - 1 / 2 + sine / 2) / sine +
      (vertical - 1 / 2 + sine / 2) / cosine =
      ((vertical - 1 / 2 + sine / 2) * (cosine + sine)) / (sine * cosine) := by
    field_simp
  rw [combine, div_lt_iff₀ (mul_pos sine_positive cosine_positive)]
  linarith

theorem midpoint_orientation {cosine sine horizontal vertical : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (cosine_le_one : cosine ≤ 1) (sine_le_one : sine ≤ 1)
    (horizontal_bounds : -(1 / 2) ≤ horizontal ∧ horizontal ≤ 1 / 2)
    (vertical_bounds : -(1 / 2) ≤ vertical ∧ vertical ≤ 1 / 2)
    (west_missing : ¬ (|horizontal - cosine / 2| ≤ 1 / 2 ∧ |vertical + sine / 2| ≤ 1 / 2))
    (east_missing : ¬ (|horizontal + cosine / 2| ≤ 1 / 2 ∧ |vertical - sine / 2| ≤ 1 / 2))
    (north_missing : ¬ (|horizontal + sine / 2| ≤ 1 / 2 ∧ |vertical + cosine / 2| ≤ 1 / 2)) :
    (1 - cosine) / 2 < horizontal ∧ (1 - sine) / 2 < vertical := by
  simp only [abs_le, not_and_or, not_le] at west_missing east_missing north_missing
  rcases west_missing with (west | west) | (west | west) <;>
    rcases east_missing with (east | east) | (east | east) <;>
    rcases north_missing with (north | north) | (north | north) <;>
    constructor <;> linarith

set_option maxHeartbeats 1000000 in
theorem midpoint_gap_endpoints {cosine sine horizontal vertical : ℝ}
    (cosine_positive : 0 < cosine) (sine_positive : 0 < sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (horizontal_bounds : -(1 / 2) ≤ horizontal ∧ horizontal ≤ 1 / 2)
    (_vertical_bounds : -(1 / 2) ≤ vertical ∧ vertical ≤ 1 / 2)
    (horizontal_large : (1 - cosine) / 2 < horizontal)
    (vertical_large : (1 - sine) / 2 < vertical)
    (bottom_wall : horizontal * sine + vertical * cosine ≤ 1 - (cosine + sine) / 2) :
    |horizontal + cosine * ((vertical - 1 / 2 + sine / 2) / sine - 1 / 2)| ≤ 1 / 2 ∧
    |horizontal - cosine / 2 - sine * ((vertical - 1 / 2 + sine / 2) / cosine)| ≤ 1 / 2 := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [sq_nonneg cosine]
  have gap := midpoint_gap_sum cosine_positive sine_positive unit horizontal_large vertical_large bottom_wall
  have first_identity :
      (horizontal + cosine * ((vertical - 1 / 2 + sine / 2) / sine - 1 / 2)) * sine =
      horizontal * sine + cosine * (vertical - 1 / 2) := by field_simp; ring
  have second_identity :
      (horizontal - cosine / 2 - sine * ((vertical - 1 / 2 + sine / 2) / cosine)) * cosine =
      cosine * horizontal - sine * vertical + sine / 2 - 1 / 2 := by
    field_simp
    nlinarith
  have first_lower : (cosine - sine) / 2 ≤ horizontal * sine + cosine * vertical := by
    nlinarith [mul_pos sine_positive (show 0 < horizontal - (1 - cosine) / 2 by linarith),
      mul_pos cosine_positive (show 0 < vertical - (1 - sine) / 2 by linarith),
      mul_nonneg (le_of_lt sine_positive) (show 0 ≤ 1 - cosine by linarith)]
  have second_lower : (1 - cosine - sine) / 2 ≤ cosine * horizontal - sine * vertical := by
    have weighted_wall := mul_nonneg (le_of_lt sine_positive)
      (show 0 ≤ 1 - (cosine + sine) / 2 - horizontal * sine - vertical * cosine by linarith)
    have weighted_unit : horizontal * (cosine ^ 2 + sine ^ 2 - 1) = 0 := by rw [unit]; ring
    have extra := mul_nonneg (show 0 ≤ 1 - cosine by linarith) (show 0 ≤ 1 - sine by linarith)
    nlinarith
  constructor <;> rw [abs_le]
  · constructor
    · nlinarith
    · have weighted := mul_nonneg (le_of_lt cosine_positive)
        (show 0 ≤ 1 / 2 - (vertical - 1 / 2 + sine / 2) / sine by linarith [gap.2.1, gap.2.2])
      linarith
  · constructor
    · nlinarith
    · have weighted := mul_nonneg (le_of_lt sine_positive) (le_of_lt gap.2.1)
      linarith

theorem corner_contains_gap_endpoint {cosine sine horizontal vertical right_gap down_gap : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (horizontal_bounds : -(1 / 2) ≤ horizontal ∧ horizontal ≤ 1 / 2)
    (vertical_bounds : -(1 / 2) ≤ vertical ∧ vertical ≤ 1 / 2)
    (left_wall : (cosine + sine) / 2 ≤ 1 - horizontal * cosine + vertical * sine)
    (north_missing : (1 - sine) / 2 < horizontal ∨ (1 - cosine) / 2 < vertical)
    (right_positive : 0 < right_gap) (down_positive : 0 < down_gap)
    (gap_sum : right_gap + down_gap < 1 / 2) :
    (|horizontal + cosine * right_gap| ≤ 1 / 2 ∧ |vertical - sine * right_gap| ≤ 1 / 2) ∨
    (|horizontal - sine * down_gap| ≤ 1 / 2 ∧ |vertical - cosine * down_gap| ≤ 1 / 2) := by
  by_cases cosine_zero : cosine = 0
  · have sine_one : sine = 1 := by nlinarith
    right
    subst cosine sine
    simp only [abs_le, zero_mul, one_mul, sub_zero]
    rcases north_missing with horizontal_large | vertical_large
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · linarith
  by_cases sine_zero : sine = 0
  · have cosine_one : cosine = 1 := by nlinarith
    right
    subst cosine sine
    simp only [abs_le, zero_mul, one_mul, sub_zero]
    rcases north_missing with horizontal_large | vertical_large
    · linarith
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have cosine_positive : 0 < cosine := lt_of_le_of_ne cosine_nonnegative (Ne.symm cosine_zero)
  have sine_positive : 0 < sine := lt_of_le_of_ne sine_nonnegative (Ne.symm sine_zero)
  have reach := corner_reach_sum cosine_positive sine_positive unit horizontal_bounds vertical_bounds left_wall north_missing
  by_cases right_reached : right_gap ≤ min ((1 / 2 - horizontal) / cosine) ((1 / 2 + vertical) / sine)
  · left
    have first := (le_div_iff₀ cosine_positive).1 ((le_min_iff).1 right_reached).1
    have second := (le_div_iff₀ sine_positive).1 ((le_min_iff).1 right_reached).2
    rw [abs_le, abs_le]
    have first_nonnegative := mul_pos cosine_positive right_positive
    have second_nonnegative := mul_pos sine_positive right_positive
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · right
    have down_reached : down_gap ≤ min ((1 / 2 + horizontal) / sine) ((1 / 2 + vertical) / cosine) := by
      linarith [lt_of_not_ge right_reached]
    have first := (le_div_iff₀ sine_positive).1 ((le_min_iff).1 down_reached).1
    have second := (le_div_iff₀ cosine_positive).1 ((le_min_iff).1 down_reached).2
    rw [abs_le, abs_le]
    have first_nonnegative := mul_pos sine_positive down_positive
    have second_nonnegative := mul_pos cosine_positive down_positive
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem localX_relative (square : PlacedSquare) (point anchor : Point) :
    square.localX point = square.localX anchor + square.frame.cosine * (point.x - anchor.x) +
      square.frame.sine * (point.y - anchor.y) := by
  dsimp [PlacedSquare.localX]
  ring

theorem localY_relative (square : PlacedSquare) (point anchor : Point) :
    square.localY point = square.localY anchor - square.frame.sine * (point.x - anchor.x) +
      square.frame.cosine * (point.y - anchor.y) := by
  dsimp [PlacedSquare.localY]
  ring

theorem local_wall_constraints {square : PlacedSquare} {side : ℝ}
    (fits : square.Fits side) (anchor : Point) :
    (square.frame.cosine + square.frame.sine) / 2 ≤
      anchor.x - square.localX anchor * square.frame.cosine + square.localY anchor * square.frame.sine ∧
    square.localX anchor * square.frame.sine + square.localY anchor * square.frame.cosine ≤
      anchor.y - (square.frame.cosine + square.frame.sine) / 2 := by
  have leftmost := (fits (point := square.point (-1 / 2) (1 / 2))
    ⟨-1 / 2, 1 / 2, by norm_num, by norm_num, rfl⟩).1
  have lowest := (fits (point := square.point (-1 / 2) (-1 / 2))
    ⟨-1 / 2, -1 / 2, by norm_num, by norm_num, rfl⟩).2.2.1
  dsimp [PlacedSquare.point, Frame.place] at leftmost lowest
  have horizontal_identity : square.localX anchor * square.frame.cosine -
      square.localY anchor * square.frame.sine = anchor.x - square.center.x := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY]
    nlinarith [show (anchor.x - square.center.x) *
      (square.frame.cosine ^ 2 + square.frame.sine ^ 2 - 1) = 0 by rw [square.frame.unit]; ring]
  have vertical_identity : square.localX anchor * square.frame.sine +
      square.localY anchor * square.frame.cosine = anchor.y - square.center.y := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY]
    nlinarith [show (anchor.y - square.center.y) *
      (square.frame.cosine ^ 2 + square.frame.sine ^ 2 - 1) = 0 by rw [square.frame.unit]; ring]
  exact ⟨by linarith, by linarith⟩

theorem midpoint_square_gap_endpoints {square : PlacedSquare} {side : ℝ}
    (fits : square.Fits side)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (midpoint_mem : square.Contains ⟨3 / 2, 1⟩)
    (west_missing : ¬ square.Contains ⟨1, 1⟩)
    (east_missing : ¬ square.Contains ⟨2, 1⟩)
    (north_missing : ¬ square.Contains ⟨3 / 2, 3 / 2⟩) :
    ∃ right_gap down_gap : ℝ, 0 < right_gap ∧ 0 < down_gap ∧ right_gap + down_gap < 1 / 2 ∧
      square.Contains ⟨1 + right_gap, 1⟩ ∧ square.Contains ⟨1, 1 - down_gap⟩ := by
  have midpoint_bounds := (square.contains_iff_localCoordinates _).1 midpoint_mem
  have local_orientation := midpoint_orientation cosine_nonnegative sine_nonnegative
    (square.frame.cosine_le_one cosine_nonnegative) (square.frame.sine_le_one sine_nonnegative)
    (abs_le.1 midpoint_bounds.1) (abs_le.1 midpoint_bounds.2)
  have orientation : (1 - square.frame.cosine) / 2 < square.localX ⟨3 / 2, 1⟩ ∧
      (1 - square.frame.sine) / 2 < square.localY ⟨3 / 2, 1⟩ := by
    apply local_orientation
    · intro local_mem
      apply west_missing
      rw [square.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring
    · intro local_mem
      apply east_missing
      rw [square.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring
    · intro local_mem
      apply north_missing
      rw [square.contains_iff_localCoordinates]
      convert local_mem using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring
  have cosine_positive : 0 < square.frame.cosine := by
    have := (abs_le.1 midpoint_bounds.1).2
    linarith [orientation.1]
  have sine_positive : 0 < square.frame.sine := by
    have := (abs_le.1 midpoint_bounds.2).2
    linarith [orientation.2]
  have wall := (local_wall_constraints fits (⟨3 / 2, 1⟩ : Point)).2
  have gap := midpoint_gap_sum cosine_positive sine_positive square.frame.unit orientation.1 orientation.2 wall
  have endpoints := midpoint_gap_endpoints cosine_positive sine_positive square.frame.unit
    (abs_le.1 midpoint_bounds.1) (abs_le.1 midpoint_bounds.2) orientation.1 orientation.2 wall
  refine ⟨_, _, gap.1, gap.2.1, gap.2.2, ?_, ?_⟩
  · rw [square.contains_iff_localCoordinates]
    constructor
    · convert endpoints.1 using 1
      congr 2
      dsimp [PlacedSquare.localX]
      ring
    · have boundary : square.localY
          ⟨1 + (square.localY ⟨3 / 2, 1⟩ - 1 / 2 + square.frame.sine / 2) / square.frame.sine, 1⟩ = 1 / 2 := by
        rw [localY_relative square _ ⟨3 / 2, 1⟩]
        dsimp
        field_simp
        ring
      rw [boundary]
      norm_num
  · rw [square.contains_iff_localCoordinates]
    constructor
    · convert endpoints.2 using 1
      congr 2
      dsimp [PlacedSquare.localX]
      ring
    · have boundary : square.localY
          ⟨1, 1 - (square.localY ⟨3 / 2, 1⟩ - 1 / 2 + square.frame.sine / 2) / square.frame.cosine⟩ = 1 / 2 := by
        rw [localY_relative square _ ⟨3 / 2, 1⟩]
        dsimp
        field_simp
        ring
      rw [boundary]
      norm_num

theorem corner_square_contains_gap_endpoint {square : PlacedSquare} {side right_gap down_gap : ℝ}
    (fits : square.Fits side)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (corner_mem : square.Contains ⟨1, 1⟩)
    (north_missing : ¬ square.Contains ⟨1, 3 / 2⟩)
    (right_positive : 0 < right_gap) (down_positive : 0 < down_gap)
    (gap_sum : right_gap + down_gap < 1 / 2) :
    square.Contains ⟨1 + right_gap, 1⟩ ∨ square.Contains ⟨1, 1 - down_gap⟩ := by
  have corner_bounds := (square.contains_iff_localCoordinates _).1 corner_mem
  have local_north_missing : (1 - square.frame.sine) / 2 < square.localX ⟨1, 1⟩ ∨
      (1 - square.frame.cosine) / 2 < square.localY ⟨1, 1⟩ := by
    by_contra! neither
    apply north_missing
    rw [square.contains_iff_localCoordinates, localX_relative square _ ⟨1, 1⟩,
      localY_relative square _ ⟨1, 1⟩, abs_le, abs_le]
    dsimp
    have horizontal_bounds := abs_le.1 corner_bounds.1
    have vertical_bounds := abs_le.1 corner_bounds.2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have endpoint := corner_contains_gap_endpoint cosine_nonnegative sine_nonnegative square.frame.unit
    (abs_le.1 corner_bounds.1) (abs_le.1 corner_bounds.2)
    (local_wall_constraints fits (⟨1, 1⟩ : Point)).1 local_north_missing
    right_positive down_positive gap_sum
  rcases endpoint with horizontal | vertical
  · left
    rw [square.contains_iff_localCoordinates]
    convert horizontal using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring
  · right
    rw [square.contains_iff_localCoordinates]
    convert vertical using 2 <;> congr 1 <;> dsimp [PlacedSquare.localX, PlacedSquare.localY] <;> ring

theorem adjacent_singletons_intersect_nonnegative_frames {corner midpoint : PlacedSquare} {side : ℝ}
    (corner_fits : corner.Fits side) (midpoint_fits : midpoint.Fits side)
    (corner_cosine : 0 ≤ corner.frame.cosine) (corner_sine : 0 ≤ corner.frame.sine)
    (midpoint_cosine : 0 ≤ midpoint.frame.cosine) (midpoint_sine : 0 ≤ midpoint.frame.sine)
    (corner_mem : corner.Contains ⟨1, 1⟩)
    (corner_north_missing : ¬ corner.Contains ⟨1, 3 / 2⟩)
    (midpoint_mem : midpoint.Contains ⟨3 / 2, 1⟩)
    (midpoint_west_missing : ¬ midpoint.Contains ⟨1, 1⟩)
    (midpoint_east_missing : ¬ midpoint.Contains ⟨2, 1⟩)
    (midpoint_north_missing : ¬ midpoint.Contains ⟨3 / 2, 3 / 2⟩) :
    ∃ point : Point, corner.Contains point ∧ midpoint.Contains point := by
  obtain ⟨right_gap, down_gap, right_positive, down_positive, gap_sum, horizontal_mem, vertical_mem⟩ :=
    midpoint_square_gap_endpoints midpoint_fits midpoint_cosine midpoint_sine midpoint_mem
      midpoint_west_missing midpoint_east_missing midpoint_north_missing
  rcases corner_square_contains_gap_endpoint corner_fits corner_cosine corner_sine corner_mem
      corner_north_missing right_positive down_positive gap_sum with horizontal | vertical
  · exact ⟨_, horizontal, horizontal_mem⟩
  · exact ⟨_, vertical, vertical_mem⟩

theorem adjacent_singletons_intersect {corner midpoint : PlacedSquare} {side : ℝ}
    (corner_fits : corner.Fits side) (midpoint_fits : midpoint.Fits side)
    (corner_mem : corner.Contains ⟨1, 1⟩)
    (corner_north_missing : ¬ corner.Contains ⟨1, 3 / 2⟩)
    (midpoint_mem : midpoint.Contains ⟨3 / 2, 1⟩)
    (midpoint_west_missing : ¬ midpoint.Contains ⟨1, 1⟩)
    (midpoint_east_missing : ¬ midpoint.Contains ⟨2, 1⟩)
    (midpoint_north_missing : ¬ midpoint.Contains ⟨3 / 2, 3 / 2⟩) :
    ∃ point : Point, corner.Contains point ∧ midpoint.Contains point := by
  obtain ⟨point, corner_point, midpoint_point⟩ := adjacent_singletons_intersect_nonnegative_frames
    ((corner.firstQuadrant_fits_iff side).2 corner_fits)
    ((midpoint.firstQuadrant_fits_iff side).2 midpoint_fits)
    corner.firstQuadrant_cosine_nonnegative corner.firstQuadrant_sine_nonnegative
    midpoint.firstQuadrant_cosine_nonnegative midpoint.firstQuadrant_sine_nonnegative
    ((corner.firstQuadrant_contains_iff _).2 corner_mem)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using corner_north_missing)
    ((midpoint.firstQuadrant_contains_iff _).2 midpoint_mem)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using midpoint_west_missing)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using midpoint_east_missing)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using midpoint_north_missing)
  exact ⟨point, (corner.firstQuadrant_contains_iff _).1 corner_point,
    (midpoint.firstQuadrant_contains_iff _).1 midpoint_point⟩

end SquarePackingArchive.StromquistSix
