import SquarePackingArchive.Records.Square5

namespace SquarePackingArchive.Stromquist

def clearancePolynomial (width height cosine : ℝ) : ℝ :=
  (1 + cosine) * (1 - width * cosine) ^ 2 -
    (1 - cosine) * (height + (height - 1) * cosine) ^ 2

lemma clearancePolynomial_first_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ clearancePolynomial (427 / 500) (97 / 100) cosine := by
  have cubic_nonnegative :=
    mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 77 / 100))
  have square_nonnegative := sq_nonneg (cosine - 7708971 / 9429200)
  dsimp [clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma clearancePolynomial_second_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ clearancePolynomial (24 / 25) (3 / 4) cosine := by
  have cubic_nonnegative :=
    mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 97 / 100))
  have square_nonnegative := sq_nonneg (cosine - 90843969 / 94650800)
  dsimp [clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma clearancePolynomial_bentz_first_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ clearancePolynomial (89 / 100) (921 / 1000) cosine := by
  have cubic_nonnegative :=
    mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 17 / 20))
  have square_nonnegative := sq_nonneg (cosine - 145216949 / 174016560)
  dsimp [clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma clearancePolynomial_bentz_second_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ clearancePolynomial (9 / 10) (9 / 10) cosine := by
  have cubic_nonnegative :=
    mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 87 / 100))
  have square_nonnegative := sq_nonneg (cosine - 215329 / 246800)
  dsimp [clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma clearancePolynomial_bentz_third_nonnegative {cosine : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) :
    0 ≤ clearancePolynomial (24 / 25) (19 / 25) cosine := by
  have cubic_nonnegative :=
    mul_nonneg cosine_nonnegative (sq_nonneg (cosine - 24 / 25))
  have square_nonnegative := sq_nonneg (cosine - 171881 / 179400)
  dsimp [clearancePolynomial]
  nlinarith only [cubic_nonnegative, square_nonnegative]

lemma boundary_clearance_of_polynomial_nonnegative
    (frame : Frame) {width height : ℝ}
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (width_nonnegative : 0 ≤ width) (width_upper : width ≤ 1)
    (polynomial_nonnegative : 0 ≤ clearancePolynomial width height frame.cosine) :
    height * frame.sine * (1 + frame.cosine) ≤
      frame.cosine * frame.sine + (1 - width * frame.cosine) * (1 + frame.cosine) := by
  have cosine_upper := frame.cosine_le_one cosine_nonnegative
  have width_cosine_upper : width * frame.cosine ≤ 1 := by
    calc
      width * frame.cosine ≤ width :=
        mul_le_of_le_one_right width_nonnegative cosine_upper
      _ ≤ 1 := width_upper
  have left_nonnegative : 0 ≤ (1 + frame.cosine) * (1 - width * frame.cosine) := by
    exact mul_nonneg (by linarith) (by linarith)
  have product_nonnegative := mul_nonneg
    (show 0 ≤ 1 + frame.cosine by linarith) polynomial_nonnegative
  have square_identity :
      ((1 + frame.cosine) * (1 - width * frame.cosine)) ^ 2 -
        (frame.sine * (height + (height - 1) * frame.cosine)) ^ 2 =
      (1 + frame.cosine) * clearancePolynomial width height frame.cosine := by
    calc
      _ = (1 + frame.cosine) ^ 2 * (1 - width * frame.cosine) ^ 2 -
          frame.sine ^ 2 * (height + (height - 1) * frame.cosine) ^ 2 := by ring
      _ = _ := by
        rw [show frame.sine ^ 2 = 1 - frame.cosine ^ 2 by nlinarith [frame.unit]]
        dsimp [clearancePolynomial]
        ring
  have clearance :
      frame.sine * (height + (height - 1) * frame.cosine) ≤
        (1 + frame.cosine) * (1 - width * frame.cosine) := by
    nlinarith only [left_nonnegative, product_nonnegative, square_identity]
  nlinarith only [clearance]

lemma boundary_clearance_first (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine) :
    (97 / 100) * frame.sine * (1 + frame.cosine) ≤
      frame.cosine * frame.sine +
        (1 - ((1 + Real.sqrt 2 / 2) / 2) * frame.cosine) * (1 + frame.cosine) := by
  have rational_bound := boundary_clearance_of_polynomial_nonnegative frame
    cosine_nonnegative
    (by norm_num : (0 : ℝ) ≤ 427 / 500) (by norm_num)
    (clearancePolynomial_first_nonnegative cosine_nonnegative)
  have width_bound : (1 + Real.sqrt 2 / 2) / 2 ≤ (427 / 500 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have product_nonnegative := mul_nonneg
    (show 0 ≤ (427 / 500 - (1 + Real.sqrt 2 / 2) / 2) * frame.cosine from
      mul_nonneg (by linarith) cosine_nonnegative)
    (show 0 ≤ 1 + frame.cosine by linarith)
  nlinarith only [rational_bound, product_nonnegative]

lemma boundary_clearance_second (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine) :
    (3 / 4) * frame.sine * (1 + frame.cosine) ≤
      frame.cosine * frame.sine +
        (1 - (24 / 25) * frame.cosine) * (1 + frame.cosine) :=
  boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    (by norm_num) (by norm_num) (clearancePolynomial_second_nonnegative cosine_nonnegative)

lemma weighted_boundary_clearance (frame : Frame) {width height : ℝ}
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine)
    (clearance : height * frame.sine * (1 + frame.cosine) ≤
      frame.cosine * frame.sine + (1 - width * frame.cosine) * (1 + frame.cosine)) :
    frame.cosine ^ 2 + height * frame.sine ^ 2 + width * frame.cosine * frame.sine ≤
      frame.cosine + frame.sine := by
  apply (mul_le_mul_iff_right₀ (show 0 < 1 + frame.cosine by linarith)).mp
  have multiplied := mul_le_mul_of_nonneg_right clearance sine_nonnegative
  have unit_multiplied := congrArg (fun value : ℝ => frame.cosine * value) frame.unit
  nlinarith only [multiplied, unit_multiplied]

lemma weighted_boundary_clearance_first (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    frame.cosine ^ 2 + (97 / 100) * frame.sine ^ 2 +
        ((1 + Real.sqrt 2 / 2) / 2) * frame.cosine * frame.sine ≤
      frame.cosine + frame.sine :=
  weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
    (boundary_clearance_first frame cosine_nonnegative)

lemma weighted_boundary_clearance_second (frame : Frame)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    frame.cosine ^ 2 + (3 / 4) * frame.sine ^ 2 +
        (24 / 25) * frame.cosine * frame.sine ≤
      frame.cosine + frame.sine :=
  weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
    (boundary_clearance_second frame cosine_nonnegative)

lemma distance_gt_one_of_adjacent_misses
    {firstX firstY secondX secondY : ℝ}
    (first_left : firstX < -1 / 2) (first_y_nonnegative : 0 ≤ firstY)
    (second_below : secondY < -1 / 2)
    (below_segment : firstX * secondY - firstY * secondX ≤ 0) :
    1 < (firstX - secondX) ^ 2 + (firstY - secondY) ^ 2 := by
  have second_x_positive : 0 < secondX := by
    by_contra not_positive
    have product_nonpositive := mul_nonpos_of_nonneg_of_nonpos
      first_y_nonnegative (le_of_not_gt not_positive)
    have product_positive := mul_pos_of_neg_of_neg
      (show firstX < 0 by linarith) (show secondY < 0 by linarith)
    nlinarith only [below_segment, product_nonpositive, product_positive]
  have large_product : 1 / 4 < firstX * secondY := by
    nlinarith [mul_pos (show 0 < -firstX - 1 / 2 by linarith)
      (show 0 < -secondY - 1 / 2 by linarith)]
  have first_product := mul_nonpos_of_nonpos_of_nonneg
    (show firstX ≤ 0 by linarith) second_x_positive.le
  have second_product := mul_nonpos_of_nonneg_of_nonpos
    first_y_nonnegative (show secondY ≤ 0 by linarith)
  nlinarith only [sq_nonneg (firstX - secondY), sq_nonneg (firstY - secondX),
    below_segment, large_product, first_product, second_product]

lemma contains_quadrilateral_pair_of_nonnegative_frame
    {square : PlacedSquare} {side left width height : ℝ}
    (fits : square.Fits side)
    (width_positive : 0 < width)
    (height_lower : 1 / 2 ≤ height) (height_upper : height ≤ 1)
    (distance_upper : width ^ 2 + (1 - height) ^ 2 ≤ 1)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (weighted_bound : square.frame.cosine ^ 2 + height * square.frame.sine ^ 2 +
      width * square.frame.cosine * square.frame.sine ≤
        square.frame.cosine + square.frame.sine)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below_segment : width * square.center.y ≤
      width + (height - 1) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, height⟩ := by
  have cosine_upper := square.frame.cosine_le_one cosine_nonnegative
  have sine_upper := square.frame.sine_le_one sine_nonnegative
  have center_y_upper : square.center.y ≤ 1 := by
    have offset_nonpositive := mul_nonpos_of_nonpos_of_nonneg
      (show height - 1 ≤ 0 by linarith) (show 0 ≤ square.center.x - left by linarith)
    nlinarith
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
  let firstX := square.localX ⟨left, 1⟩
  let firstY := square.localY ⟨left, 1⟩
  let secondX := square.localX ⟨left + width, height⟩
  let secondY := square.localY ⟨left + width, height⟩
  have first_x_upper : firstX ≤ 1 / 2 := by
    have offset_nonpositive := mul_nonpos_of_nonpos_of_nonneg
      (show left - square.center.x ≤ 0 by linarith) cosine_nonnegative
    dsimp [firstX, PlacedSquare.localX]
    nlinarith only [offset_nonpositive, vertical_sine_upper]
  have first_y_nonnegative : 0 ≤ firstY := by
    have horizontal_nonnegative := mul_nonneg
      (show 0 ≤ square.center.x - left by linarith) sine_nonnegative
    have vertical_nonnegative := mul_nonneg
      (show 0 ≤ 1 - square.center.y by linarith) cosine_nonnegative
    dsimp [firstY, PlacedSquare.localY]
    nlinarith only [horizontal_nonnegative, vertical_nonnegative]
  have second_x_lower : -1 / 2 ≤ secondX := by
    have horizontal_nonnegative := mul_nonneg
      (show 0 ≤ left + width - square.center.x by linarith) cosine_nonnegative
    have height_nonnegative := mul_nonneg
      (show 0 ≤ height - square.center.y + 1 / 2 by linarith) sine_nonnegative
    dsimp [secondX, PlacedSquare.localX]
    nlinarith only [horizontal_nonnegative, height_nonnegative, sine_upper]
  have second_y_upper : secondY ≤ 1 / 2 := by
    have horizontal_nonpositive := mul_nonpos_of_nonpos_of_nonneg
      (show -(left + width - square.center.x) ≤ 0 by linarith) sine_nonnegative
    have vertical_upper := mul_le_mul_of_nonneg_right
      (show height - square.center.y ≤ 1 - square.center.y by linarith) cosine_nonnegative
    dsimp [secondY, PlacedSquare.localY]
    nlinarith only [horizontal_nonpositive, vertical_upper, vertical_cosine_upper]
  have local_distance_upper : (firstX - secondX) ^ 2 + (firstY - secondY) ^ 2 ≤ 1 := by
    have distance_identity := square.local_coordinate_distance_sq
      ⟨left, 1⟩ ⟨left + width, height⟩
    change (firstX - secondX) ^ 2 + (firstY - secondY) ^ 2 = _ at distance_identity
    nlinarith only [distance_identity, distance_upper]
  have local_cross_nonpositive : firstX * secondY - firstY * secondX ≤ 0 := by
    have cross_identity : firstX * secondY - firstY * secondX =
        (square.center.x - left) * (1 - height) - width * (1 - square.center.y) := by
      dsimp [firstX, firstY, secondX, secondY, PlacedSquare.localX, PlacedSquare.localY]
      linear_combination
        ((square.center.x - left) * (1 - height) - width * (1 - square.center.y)) *
          square.frame.unit
    nlinarith only [cross_identity, center_below_segment]
  by_contra neither_point
  push Not at neither_point
  have first_miss : firstX < -1 / 2 ∨ 1 / 2 < firstY := by
    by_contra coordinates_inside
    push Not at coordinates_inside
    apply neither_point.1
    rw [square.contains_iff_localCoordinates]
    exact ⟨abs_le.mpr ⟨by linarith [coordinates_inside.1], first_x_upper⟩,
      abs_le.mpr ⟨by linarith, coordinates_inside.2⟩⟩
  have second_miss : 1 / 2 < secondX ∨ secondY < -1 / 2 := by
    by_contra coordinates_inside
    push Not at coordinates_inside
    apply neither_point.2
    rw [square.contains_iff_localCoordinates]
    exact ⟨abs_le.mpr ⟨by linarith, coordinates_inside.1⟩,
      abs_le.mpr ⟨by linarith [coordinates_inside.2], second_y_upper⟩⟩
  rcases first_miss with first_left | first_above
  · rcases second_miss with second_right | second_below
    · nlinarith [sq_nonneg (firstY - secondY)]
    · have impossible := distance_gt_one_of_adjacent_misses
        first_left first_y_nonnegative second_below local_cross_nonpositive
      linarith
  · rcases second_miss with second_right | second_below
    · have weighted_coordinates_strict :
          (square.frame.cosine + square.frame.sine) / 2 <
            firstY * square.frame.cosine + secondX * square.frame.sine := by
        have sine_weighted := mul_nonneg
          (show 0 ≤ secondX - 1 / 2 by linarith) sine_nonnegative
        by_cases cosine_zero : square.frame.cosine = 0
        · have sine_positive : 0 < square.frame.sine := by nlinarith [square.frame.unit]
          have sine_strict := mul_pos (show 0 < secondX - 1 / 2 by linarith) sine_positive
          rw [cosine_zero]
          nlinarith only [sine_strict]
        · have cosine_positive : 0 < square.frame.cosine := lt_of_le_of_ne cosine_nonnegative (Ne.symm cosine_zero)
          have cosine_strict := mul_pos (show 0 < firstY - 1 / 2 by linarith) cosine_positive
          nlinarith only [cosine_strict, sine_weighted]
      have weighted_identity : firstY * square.frame.cosine + secondX * square.frame.sine =
          square.frame.cosine ^ 2 + height * square.frame.sine ^ 2 +
            width * square.frame.cosine * square.frame.sine - square.center.y := by
        dsimp [firstY, secondX, PlacedSquare.localX, PlacedSquare.localY]
        linear_combination -square.center.y * square.frame.unit
      linarith
    · nlinarith [sq_nonneg (firstX - secondX)]

lemma contains_quadrilateral_pair
    {square : PlacedSquare} {side left width height : ℝ}
    (fits : square.Fits side)
    (width_positive : 0 < width)
    (height_lower : 1 / 2 ≤ height) (height_upper : height ≤ 1)
    (distance_upper : width ^ 2 + (1 - height) ^ 2 ≤ 1)
    (weighted_bound : ∀ frame : Frame, 0 ≤ frame.cosine → 0 ≤ frame.sine →
      frame.cosine ^ 2 + height * frame.sine ^ 2 + width * frame.cosine * frame.sine ≤
        frame.cosine + frame.sine)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below_segment : width * square.center.y ≤
      width + (height - 1) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, height⟩ := by
  have normalized := contains_quadrilateral_pair_of_nonnegative_frame
    ((square.firstQuadrant_fits_iff side).2 fits)
    width_positive height_lower height_upper distance_upper
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    (weighted_bound square.firstQuadrant.frame square.firstQuadrant_cosine_nonnegative
      square.firstQuadrant_sine_nonnegative)
    (by simpa using center_x_lower) (by simpa using center_x_upper)
    (by simpa using center_below_segment)
  simpa using normalized

theorem lemma4_first
    {square : PlacedSquare} {side left : ℝ}
    (fits : square.Fits side)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + (1 + Real.sqrt 2 / 2) / 2)
    (center_below_segment : ((1 + Real.sqrt 2 / 2) / 2) * square.center.y ≤
      (1 + Real.sqrt 2 / 2) / 2 - (3 / 100) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨
      square.Contains ⟨left + (1 + Real.sqrt 2 / 2) / 2, 97 / 100⟩ := by
  apply contains_quadrilateral_pair fits
    (by positivity) (by norm_num) (by norm_num)
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  · exact weighted_boundary_clearance_first
  · exact center_x_lower
  · exact center_x_upper
  · nlinarith only [center_below_segment]

theorem lemma4_second
    {square : PlacedSquare} {side left : ℝ}
    (fits : square.Fits side)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 24 / 25)
    (center_below_segment : (24 / 25) * square.center.y ≤
      24 / 25 - (1 / 4) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + 24 / 25, 3 / 4⟩ := by
  apply contains_quadrilateral_pair fits
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    weighted_boundary_clearance_second center_x_lower center_x_upper
  nlinarith only [center_below_segment]

lemma contains_quadrilateral_pair_of_clearance_polynomial
    {square : PlacedSquare} {side left width height : ℝ}
    (fits : square.Fits side)
    (width_positive : 0 < width) (width_upper : width ≤ 1)
    (height_lower : 1 / 2 ≤ height) (height_upper : height ≤ 1)
    (distance_upper : width ^ 2 + (1 - height) ^ 2 ≤ 1)
    (polynomial_nonnegative : ∀ cosine : ℝ, 0 ≤ cosine →
      0 ≤ clearancePolynomial width height cosine)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + width)
    (center_below_segment : width * square.center.y ≤
      width + (height - 1) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + width, height⟩ := by
  apply contains_quadrilateral_pair fits width_positive height_lower height_upper distance_upper
    _ center_x_lower center_x_upper center_below_segment
  intro frame cosine_nonnegative sine_nonnegative
  apply weighted_boundary_clearance frame cosine_nonnegative sine_nonnegative
  exact boundary_clearance_of_polynomial_nonnegative frame cosine_nonnegative
    width_positive.le width_upper (polynomial_nonnegative _ cosine_nonnegative)

theorem lemma4_bentz_first
    {square : PlacedSquare} {side left : ℝ}
    (fits : square.Fits side)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 89 / 100)
    (center_below_segment : (89 / 100) * square.center.y ≤
      89 / 100 - (79 / 1000) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + 89 / 100, 921 / 1000⟩ := by
  apply contains_quadrilateral_pair_of_clearance_polynomial fits
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => clearancePolynomial_bentz_first_nonnegative) center_x_lower center_x_upper
  nlinarith only [center_below_segment]

theorem lemma4_bentz_second
    {square : PlacedSquare} {side left : ℝ}
    (fits : square.Fits side)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 9 / 10)
    (center_below_segment : (9 / 10) * square.center.y ≤
      9 / 10 - (1 / 10) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + 9 / 10, 9 / 10⟩ := by
  apply contains_quadrilateral_pair_of_clearance_polynomial fits
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => clearancePolynomial_bentz_second_nonnegative) center_x_lower center_x_upper
  nlinarith only [center_below_segment]

theorem lemma4_bentz_third
    {square : PlacedSquare} {side left : ℝ}
    (fits : square.Fits side)
    (center_x_lower : left ≤ square.center.x)
    (center_x_upper : square.center.x ≤ left + 24 / 25)
    (center_below_segment : (24 / 25) * square.center.y ≤
      24 / 25 - (6 / 25) * (square.center.x - left)) :
    square.Contains ⟨left, 1⟩ ∨ square.Contains ⟨left + 24 / 25, 19 / 25⟩ := by
  apply contains_quadrilateral_pair_of_clearance_polynomial fits
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => clearancePolynomial_bentz_third_nonnegative) center_x_lower center_x_upper
  nlinarith only [center_below_segment]

end SquarePackingArchive.Stromquist
