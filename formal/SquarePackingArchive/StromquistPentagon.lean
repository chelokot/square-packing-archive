import SquarePackingArchive.Stromquist

namespace SquarePackingArchive.Stromquist

lemma coordinate_pair_misses_force_adjacent
    {firstX firstY secondX secondY : ℝ}
    (first_x_upper : firstX ≤ 1 / 2) (first_y_nonnegative : 0 ≤ firstY)
    (second_x_lower : -1 / 2 ≤ secondX) (second_y_upper : secondY ≤ 1 / 2)
    (distance_upper : (firstX - secondX) ^ 2 + (firstY - secondY) ^ 2 ≤ 1)
    (cross_nonpositive : firstX * secondY - firstY * secondX ≤ 0)
    (first_missed : ¬ (|firstX| ≤ 1 / 2 ∧ |firstY| ≤ 1 / 2))
    (second_missed : ¬ (|secondX| ≤ 1 / 2 ∧ |secondY| ≤ 1 / 2)) :
    1 / 2 < firstY ∧ 1 / 2 < secondX := by
  have first_miss : firstX < -1 / 2 ∨ 1 / 2 < firstY := by
    by_contra neither
    push Not at neither
    exact first_missed ⟨abs_le.mpr ⟨by linarith, first_x_upper⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have second_miss : 1 / 2 < secondX ∨ secondY < -1 / 2 := by
    by_contra neither
    push Not at neither
    exact second_missed ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, second_y_upper⟩⟩
  rcases first_miss with first_left | first_above
  · rcases second_miss with second_right | second_below
    · nlinarith [sq_nonneg (firstY - secondY)]
    · have impossible := distance_gt_one_of_adjacent_misses
        first_left first_y_nonnegative second_below cross_nonpositive
      linarith
  · rcases second_miss with second_right | second_below
    · exact ⟨first_above, second_right⟩
    · nlinarith [sq_nonneg (firstX - secondX)]

lemma boundary_pair_misses_force_adjacent
    {square : PlacedSquare} {side left width : ℝ}
    (fits : square.Fits side)
    (width_nonnegative : 0 ≤ width) (width_upper : width ≤ 1)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_y_upper : square.center.y ≤ 1)
    (first_missed : ¬ square.Contains ⟨left, 1⟩)
    (second_missed : ¬ square.Contains ⟨left + width, 1⟩) :
    1 / 2 < square.localY ⟨left, 1⟩ ∧
      1 / 2 < square.localX ⟨left + width, 1⟩ := by
  have bottom_bounds := fits
    (point := square.point (-1 / 2) (-1 / 2))
    ⟨-1 / 2, -1 / 2, by norm_num, by norm_num, rfl⟩
  have center_y_lower : (square.frame.cosine + square.frame.sine) / 2 ≤ square.center.y := by
    have bottom_nonnegative := bottom_bounds.2.2.1
    simp [PlacedSquare.point, Frame.place] at bottom_nonnegative
    linarith
  have vertical_sine_upper : (1 - square.center.y) * square.frame.sine ≤ 1 / 2 := by
    have weighted_center := mul_le_mul_of_nonneg_right center_y_lower sine_nonnegative
    nlinarith [square.frame.unit, sq_nonneg (1 - square.frame.sine)]
  have vertical_cosine_upper : (1 - square.center.y) * square.frame.cosine ≤ 1 / 2 := by
    have weighted_center := mul_le_mul_of_nonneg_right center_y_lower cosine_nonnegative
    nlinarith [square.frame.unit, sq_nonneg (1 - square.frame.cosine)]
  apply coordinate_pair_misses_force_adjacent
    (firstX := square.localX ⟨left, 1⟩) (secondY := square.localY ⟨left + width, 1⟩)
  · have horizontal := mul_nonpos_of_nonpos_of_nonneg
      (show left - square.center.x ≤ 0 by linarith) cosine_nonnegative
    dsimp [PlacedSquare.localX]
    nlinarith only [horizontal, vertical_sine_upper]
  · have horizontal := mul_nonneg
      (show 0 ≤ square.center.x - left by linarith) sine_nonnegative
    have vertical := mul_nonneg (show 0 ≤ 1 - square.center.y by linarith) cosine_nonnegative
    dsimp [PlacedSquare.localY]
    nlinarith only [horizontal, vertical]
  · have horizontal := mul_nonneg
      (show 0 ≤ left + width - square.center.x by linarith) cosine_nonnegative
    have vertical := mul_nonneg (show 0 ≤ 1 - square.center.y by linarith) sine_nonnegative
    dsimp [PlacedSquare.localX]
    nlinarith only [horizontal, vertical]
  · have horizontal := mul_nonpos_of_nonpos_of_nonneg
      (show -(left + width - square.center.x) ≤ 0 by linarith) sine_nonnegative
    dsimp [PlacedSquare.localY]
    nlinarith only [horizontal, vertical_cosine_upper]
  · have distance_identity := square.local_coordinate_distance_sq ⟨left, 1⟩ ⟨left + width, 1⟩
    nlinarith only [distance_identity, width_nonnegative, width_upper]
  · have cross_identity :
        square.localX ⟨left, 1⟩ * square.localY ⟨left + width, 1⟩ -
          square.localY ⟨left, 1⟩ * square.localX ⟨left + width, 1⟩ =
        -width * (1 - square.center.y) := by
      dsimp [PlacedSquare.localX, PlacedSquare.localY]
      linear_combination (-width * (1 - square.center.y)) * square.frame.unit
    rw [cross_identity]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact fun inside => first_missed ((square.contains_iff_localCoordinates _).2 inside)
  · exact fun inside => second_missed ((square.contains_iff_localCoordinates _).2 inside)

lemma boundary_chord_clearance (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    1 + (207 / 250) * frame.cosine * frame.sine ≤ frame.cosine + frame.sine := by
  have sum_lower : 1 ≤ frame.cosine + frame.sine := by
    nlinarith [frame.unit, mul_nonneg cosine_nonnegative sine_nonnegative]
  have sum_upper : frame.cosine + frame.sine ≤ 283 / 200 := by
    nlinarith [frame.unit, sq_nonneg (frame.cosine - frame.sine)]
  have product_nonnegative := mul_nonneg
    (show 0 ≤ frame.cosine + frame.sine - 1 by linarith)
    (show 0 ≤ 2 - (207 / 250) * (frame.cosine + frame.sine + 1) by linarith)
  nlinarith [frame.unit]

lemma pentagon_left_clearance
    {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_x_lower : 1 ≤ square.center.x)
    (center_y_lower : (square.frame.cosine + square.frame.sine) / 2 ≤ square.center.y)
    (first_above : 1 / 2 < square.localY ⟨1, 1⟩)
    (second_right : 1 / 2 < square.localX ⟨2, 1⟩)
    (left_segment_missed : ∀ height : ℝ, 197 / 250 ≤ height → height ≤ 1 →
      ¬ square.Contains ⟨1, height⟩) :
    1 / 2 < square.localY ⟨1, 197 / 250⟩ := by
  have cosine_positive : 0 < square.frame.cosine := by
    by_contra not_positive
    have cosine_zero : square.frame.cosine = 0 := by linarith
    have sine_one : square.frame.sine = 1 := by nlinarith [square.frame.unit]
    simp [PlacedSquare.localX, cosine_zero, sine_one] at second_right
    rw [cosine_zero, sine_one] at center_y_lower
    linarith
  have left_support : square.center.x < 1 + (square.frame.cosine + square.frame.sine) / 2 := by
    by_contra not_left
    have weighted_horizontal := mul_le_mul_of_nonneg_right
      (le_of_not_gt not_left) cosine_nonnegative
    have weighted_vertical := mul_le_mul_of_nonneg_right center_y_lower sine_nonnegative
    dsimp [PlacedSquare.localX] at second_right
    nlinarith [sq_nonneg (square.frame.cosine + square.frame.sine - 1)]
  by_contra not_above
  have lower_point_localY : square.localY ⟨1, 197 / 250⟩ ≤ 1 / 2 := le_of_not_gt not_above
  let height := square.center.y +
    (1 / 2 - (square.center.x - 1) * square.frame.sine) / square.frame.cosine
  have height_identity : height * square.frame.cosine =
      square.center.y * square.frame.cosine + 1 / 2 -
        (square.center.x - 1) * square.frame.sine := by
    dsimp [height]
    field_simp
    ring
  have height_lower : 197 / 250 ≤ height := by
    dsimp [PlacedSquare.localY] at lower_point_localY
    nlinarith only [lower_point_localY, height_identity, cosine_positive]
  have height_upper : height ≤ 1 := by
    dsimp [PlacedSquare.localY] at first_above
    nlinarith only [first_above, height_identity, cosine_positive]
  have localY_identity : square.localY ⟨1, height⟩ = 1 / 2 := by
    dsimp [PlacedSquare.localY]
    nlinarith only [height_identity]
  have inverse_identity :
      square.frame.cosine * square.localX ⟨1, height⟩ -
        square.frame.sine * square.localY ⟨1, height⟩ = 1 - square.center.x := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY]
    linear_combination (1 - square.center.x) * square.frame.unit
  have localX_lower : -1 / 2 ≤ square.localX ⟨1, height⟩ := by
    rw [localY_identity] at inverse_identity
    nlinarith only [inverse_identity, left_support, cosine_positive]
  have localX_upper : square.localX ⟨1, height⟩ ≤ 1 / 2 := by
    have weighted_center := mul_le_mul_of_nonneg_right center_y_lower sine_nonnegative
    have horizontal_nonpositive := mul_nonpos_of_nonpos_of_nonneg
      (show 1 - square.center.x ≤ 0 by linarith) cosine_nonnegative
    have vertical_upper := mul_le_mul_of_nonneg_right
      (show height - square.center.y ≤ 1 - square.center.y by linarith) sine_nonnegative
    dsimp [PlacedSquare.localX]
    nlinarith [square.frame.unit, sq_nonneg (1 - square.frame.sine)]
  apply left_segment_missed height height_lower height_upper
  rw [square.contains_iff_localCoordinates, localY_identity]
  exact ⟨abs_le.mpr ⟨by linarith, localX_upper⟩, by norm_num⟩

lemma pentagon_shallow_clearance (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine)
    (slope_upper : frame.sine ≤ (6 / 5) * frame.cosine) :
    frame.sine * frame.cosine ≤
      (53 / 250) * frame.cosine ^ 2 + frame.sine + frame.cosine - 1 := by
  have chord_bound := boundary_chord_clearance frame cosine_nonnegative sine_nonnegative
  have weighted_slope := mul_le_mul_of_nonneg_right slope_upper cosine_nonnegative
  nlinarith [sq_nonneg frame.cosine]

lemma pentagon_steep_clearance (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_lower : 9 / 10 ≤ frame.sine) :
    (6 / 5) * frame.sine * (1 - frame.sine) ≤
      1 + frame.sine * frame.cosine - (197 / 250) * frame.cosine - frame.sine := by
  have sine_nonnegative : 0 ≤ frame.sine := by linarith
  have sine_upper := frame.sine_le_one sine_nonnegative
  have cosine_lower : 2 * (1 - frame.sine) ≤ frame.cosine := by
    have product_nonnegative := mul_nonneg
      (show 0 ≤ 1 - frame.sine by linarith)
      (show 0 ≤ 5 * frame.sine - 3 by linarith)
    nlinarith [frame.unit]
  have clearance_nonnegative := mul_nonneg
    (show 0 ≤ frame.cosine - 2 * (1 - frame.sine) by linarith)
    (show 0 ≤ frame.sine - 197 / 250 by linarith)
  have sine_product := mul_nonneg
    (show 0 ≤ 1 - frame.sine by linarith)
    (show 0 ≤ frame.sine - 9 / 10 by linarith)
  nlinarith

lemma pentagon_clearance_polynomial_positive {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_upper : parameter ≤ 1) :
    0 < -447 * parameter ^ 4 + 1060 * parameter ^ 3 -
      506 * parameter ^ 2 - 60 * parameter + 53 := by
  have quartic_nonnegative := mul_nonneg
    (mul_nonneg parameter_nonnegative (show 0 ≤ 1 - parameter by linarith))
    (sq_nonneg (parameter - 1 / 2))
  have cubic_nonnegative := mul_nonneg parameter_nonnegative
    (sq_nonneg (parameter - 1 / 2))
  have square_nonnegative := sq_nonneg (parameter - 853 / 1750)
  nlinarith only [quartic_nonnegative, cubic_nonnegative, square_nonnegative]

lemma pentagon_middle_clearance (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    (28 / 25) * frame.sine * frame.cosine <
      (14 / 125) * frame.cosine ^ 2 + frame.sine + frame.cosine - 9 / 10 := by
  let parameter := frame.sine / (1 + frame.cosine)
  have denominator_positive : 0 < 1 + frame.cosine := by linarith
  have parameter_nonnegative : 0 ≤ parameter := div_nonneg sine_nonnegative denominator_positive.le
  have parameter_upper : parameter ≤ 1 := by
    apply (div_le_one denominator_positive).2
    linarith [frame.sine_le_one sine_nonnegative]
  have parameter_cosine : frame.cosine * (1 + parameter ^ 2) = 1 - parameter ^ 2 := by
    dsimp [parameter]
    field_simp
    nlinarith [frame.unit]
  have parameter_sine : frame.sine * (1 + parameter ^ 2) = 2 * parameter := by
    dsimp [parameter]
    field_simp
    nlinarith [frame.unit]
  have polynomial_positive := pentagon_clearance_polynomial_positive
    parameter_nonnegative parameter_upper
  have factor_positive : 0 < (1 + parameter ^ 2) ^ 2 := by positivity
  apply (mul_lt_mul_iff_right₀ factor_positive).mp
  have identity :
      ((14 / 125) * frame.cosine ^ 2 + frame.sine + frame.cosine - 9 / 10 -
          (28 / 25) * frame.sine * frame.cosine) * (1 + parameter ^ 2) ^ 2 =
        (-447 * parameter ^ 4 + 1060 * parameter ^ 3 -
          506 * parameter ^ 2 - 60 * parameter + 53) / 250 := by
    calc
      _ = (14 / 125) * (frame.cosine * (1 + parameter ^ 2)) ^ 2 +
          (frame.sine * (1 + parameter ^ 2) + frame.cosine * (1 + parameter ^ 2)) *
            (1 + parameter ^ 2) - (9 / 10) * (1 + parameter ^ 2) ^ 2 -
          (28 / 25) * (frame.sine * (1 + parameter ^ 2)) *
            (frame.cosine * (1 + parameter ^ 2)) := by ring
      _ = _ := by rw [parameter_cosine, parameter_sine]; ring
  nlinarith only [identity, polynomial_positive]

set_option maxHeartbeats 1000000 in
theorem lemma5_of_nonnegative_frame
    {square : PlacedSquare} {side : ℝ}
    (fits : square.Fits side)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 53 / 25)
    (center_y_upper : square.center.y ≤ 1)
    (center_below_segment : 5 * square.center.x + 6 * square.center.y ≤ 16) :
    (∃ height : ℝ, 197 / 250 ≤ height ∧ height ≤ 1 ∧ square.Contains ⟨1, height⟩) ∨
      (∃ parameter : ℝ, 0 ≤ parameter ∧ parameter ≤ 1 ∧
        square.Contains ⟨2 + (3 / 25) * parameter, 1 - parameter / 10⟩) := by
  by_contra neither_segment
  push Not at neither_segment
  obtain ⟨left_missed, right_missed⟩ := neither_segment
  have bottom_bounds := fits
    (point := square.point (-1 / 2) (-1 / 2))
    ⟨-1 / 2, -1 / 2, by norm_num, by norm_num, rfl⟩
  have center_y_lower : (square.frame.cosine + square.frame.sine) / 2 ≤ square.center.y := by
    have bottom_nonnegative := bottom_bounds.2.2.1
    simp [PlacedSquare.point, Frame.place] at bottom_nonnegative
    linarith
  have bottom_point_missed : ¬ square.Contains ⟨2, 1⟩ := by
    simpa using right_missed 0 (by norm_num) (by norm_num)
  have endpoint_missed : ¬ square.Contains ⟨53 / 25, 9 / 10⟩ := by
    convert right_missed 1 (by norm_num) (by norm_num) using 1; norm_num
  have center_x_le_two : square.center.x ≤ 2 := by
    by_contra center_right
    have pair := contains_quadrilateral_pair (left := 2) (width := 3 / 25) (height := 9 / 10)
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun frame cosine_nonnegative sine_nonnegative => by
        have chord := boundary_chord_clearance frame cosine_nonnegative sine_nonnegative
        nlinarith [frame.unit, mul_nonneg cosine_nonnegative sine_nonnegative,
          sq_nonneg frame.sine])
      (by linarith) (by linarith) (by nlinarith only [center_below_segment])
    rcases pair with bottom_inside | endpoint_inside
    · exact bottom_point_missed bottom_inside
    · apply endpoint_missed
      convert endpoint_inside using 1; norm_num
  have initial_pair := boundary_pair_misses_force_adjacent (left := 1) (width := 1)
    fits (by norm_num) (by norm_num) cosine_nonnegative sine_nonnegative
    center_x_lower (by linarith) center_y_upper
    (left_missed 1 (by norm_num) (by norm_num))
    (by convert bottom_point_missed using 1; norm_num)
  norm_num at initial_pair
  have left_clearance := pentagon_left_clearance cosine_nonnegative sine_nonnegative
    center_x_lower center_y_lower initial_pair.1 initial_pair.2 left_missed
  let leftY := square.localY ⟨1, 197 / 250⟩
  let bottomX := square.localX ⟨2, 1⟩
  let bottomY := square.localY ⟨2, 1⟩
  let endpointX := square.localX ⟨53 / 25, 9 / 10⟩
  let endpointY := square.localY ⟨53 / 25, 9 / 10⟩
  have leftY_lower : 1 / 2 < leftY := left_clearance
  have bottomX_lower : 1 / 2 < bottomX := initial_pair.2
  have bottom_identity : leftY * square.frame.cosine + bottomX * square.frame.sine =
      (197 / 250) * square.frame.cosine ^ 2 + square.frame.sine ^ 2 +
        square.frame.cosine * square.frame.sine - square.center.y := by
    dsimp [leftY, bottomX, PlacedSquare.localY, PlacedSquare.localX]
    linear_combination -square.center.y * square.frame.unit
  have endpoint_identity : leftY * square.frame.cosine + endpointX * square.frame.sine =
      (197 / 250) * square.frame.cosine ^ 2 + (9 / 10) * square.frame.sine ^ 2 +
        (28 / 25) * square.frame.cosine * square.frame.sine - square.center.y := by
    dsimp [leftY, endpointX, PlacedSquare.localY, PlacedSquare.localX]
    linear_combination -square.center.y * square.frame.unit
  have slope_lower : (6 / 5) * square.frame.cosine < square.frame.sine := by
    by_contra not_steep
    have shallow := pentagon_shallow_clearance square.frame cosine_nonnegative
      sine_nonnegative (le_of_not_gt not_steep)
    have cosine_positive : 0 < square.frame.cosine := by nlinarith [square.frame.unit]
    have left_weighted := mul_lt_mul_of_pos_right leftY_lower cosine_positive
    have bottom_weighted := mul_le_mul_of_nonneg_right bottomX_lower.le sine_nonnegative
    nlinarith [square.frame.unit]
  have sine_positive : 0 < square.frame.sine := by linarith
  have endpointX_upper : endpointX < 1 / 2 := by
    by_contra not_left
    have middle := pentagon_middle_clearance square.frame cosine_nonnegative sine_nonnegative
    have left_weighted := mul_le_mul_of_nonneg_right leftY_lower.le cosine_nonnegative
    have endpoint_weighted := mul_le_mul_of_nonneg_right (le_of_not_gt not_left) sine_nonnegative
    nlinarith [square.frame.unit]
  have endpointX_lower : -1 / 2 ≤ endpointX := by
    have delta : endpointX - bottomX = (3 / 25) * square.frame.cosine - square.frame.sine / 10 := by
      dsimp [endpointX, bottomX, PlacedSquare.localX]
      ring
    nlinarith [square.frame.sine_le_one sine_nonnegative]
  have bottomY_upper : bottomY ≤ 1 / 2 := by
    have weighted_center := mul_le_mul_of_nonneg_right center_y_lower cosine_nonnegative
    have horizontal_nonpositive := mul_nonpos_of_nonpos_of_nonneg
      (show -(2 - square.center.x) ≤ 0 by linarith) sine_nonnegative
    dsimp [bottomY, PlacedSquare.localY]
    nlinarith [square.frame.unit, sq_nonneg (1 - square.frame.cosine)]
  have endpointY_delta : endpointY - bottomY =
      -(3 / 25) * square.frame.sine - square.frame.cosine / 10 := by
    dsimp [endpointY, bottomY, PlacedSquare.localY]
    ring
  have endpointY_upper : endpointY ≤ 1 / 2 := by linarith
  have sine_large : 9 / 10 < square.frame.sine := by
    by_contra not_large
    have sine_upper : square.frame.sine ≤ 9 / 10 := le_of_not_gt not_large
    have cosine_lower : 1 / 10 ≤ square.frame.cosine := by nlinarith [square.frame.unit]
    have vertical_delta : endpointY = leftY - (28 / 25) * square.frame.sine +
        (14 / 125) * square.frame.cosine := by
      dsimp [endpointY, leftY, PlacedSquare.localY]
      ring
    have endpointY_lower : -1 / 2 ≤ endpointY := by linarith
    apply endpoint_missed
    rw [square.contains_iff_localCoordinates]
    exact ⟨abs_le.mpr ⟨by linarith, endpointX_upper.le⟩,
      abs_le.mpr ⟨by linarith, endpointY_upper⟩⟩
  have vertex_support : 16 ≤ 5 * square.center.x + 6 * square.center.y +
      (11 * square.frame.sine - square.frame.cosine) / 2 := by
    apply (mul_le_mul_iff_right₀ sine_positive).mp
    have steep := pentagon_steep_clearance square.frame cosine_nonnegative sine_large.le
    have weighted_center := mul_le_mul_of_nonneg_right center_y_lower
      (show 0 ≤ 5 * square.frame.cosine + 6 * square.frame.sine by positivity)
    dsimp [leftY, PlacedSquare.localY] at leftY_lower
    nlinarith [square.frame.unit]
  let parameter := (bottomX - 1 / 2) / (bottomX - endpointX)
  have denominator_positive : 0 < bottomX - endpointX := by linarith
  have parameter_nonnegative : 0 ≤ parameter := by
    exact div_nonneg (by linarith) denominator_positive.le
  have parameter_upper : parameter ≤ 1 := by
    apply (div_le_one denominator_positive).2
    linarith
  have parameter_identity : parameter * (bottomX - endpointX) = bottomX - 1 / 2 := by
    dsimp [parameter]
    exact div_mul_cancel₀ _ denominator_positive.ne'
  let contact : Point := ⟨2 + (3 / 25) * parameter, 1 - parameter / 10⟩
  have contactX_identity : square.localX contact = bottomX + parameter * (endpointX - bottomX) := by
    dsimp [contact, bottomX, endpointX, PlacedSquare.localX]
    ring
  have contactY_identity : square.localY contact = bottomY + parameter * (endpointY - bottomY) := by
    dsimp [contact, bottomY, endpointY, PlacedSquare.localY]
    ring
  have contactX : square.localX contact = 1 / 2 := by
    nlinarith only [contactX_identity, parameter_identity]
  have contactY_upper : square.localY contact ≤ 1 / 2 := by
    have product_nonpositive := mul_nonpos_of_nonneg_of_nonpos parameter_nonnegative
      (show endpointY - bottomY ≤ 0 by linarith)
    nlinarith only [contactY_identity, product_nonpositive, bottomY_upper]
  have contact_normal :
      5 * square.center.x + 6 * square.center.y +
        (5 * square.frame.cosine + 6 * square.frame.sine) * square.localX contact +
        (6 * square.frame.cosine - 5 * square.frame.sine) * square.localY contact = 16 := by
    dsimp [contact, PlacedSquare.localX, PlacedSquare.localY]
    linear_combination (16 - 5 * square.center.x - 6 * square.center.y) * square.frame.unit
  have contactY_lower : -1 / 2 ≤ square.localY contact := by
    rw [contactX] at contact_normal
    by_contra below_bottom
    have product_positive := mul_pos_of_neg_of_neg
      (show 6 * square.frame.cosine - 5 * square.frame.sine < 0 by linarith)
      (show square.localY contact + 1 / 2 < 0 by linarith)
    nlinarith only [contact_normal, vertex_support, product_positive]
  apply right_missed parameter parameter_nonnegative parameter_upper
  change square.Contains contact
  rw [square.contains_iff_localCoordinates, contactX]
  exact ⟨by norm_num, abs_le.mpr ⟨by linarith, contactY_upper⟩⟩

theorem lemma5
    {square : PlacedSquare} {side : ℝ}
    (fits : square.Fits side)
    (center_x_lower : 1 ≤ square.center.x)
    (center_x_upper : square.center.x ≤ 53 / 25)
    (center_y_upper : square.center.y ≤ 1)
    (center_below_segment : 5 * square.center.x + 6 * square.center.y ≤ 16) :
    (∃ height : ℝ, 197 / 250 ≤ height ∧ height ≤ 1 ∧ square.Contains ⟨1, height⟩) ∨
      (∃ parameter : ℝ, 0 ≤ parameter ∧ parameter ≤ 1 ∧
        square.Contains ⟨2 + (3 / 25) * parameter, 1 - parameter / 10⟩) := by
  have normalized := lemma5_of_nonnegative_frame
    ((square.firstQuadrant_fits_iff side).2 fits)
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    (by simpa using center_x_lower) (by simpa using center_x_upper)
    (by simpa using center_y_upper) (by simpa using center_below_segment)
  simpa using normalized

end SquarePackingArchive.Stromquist
