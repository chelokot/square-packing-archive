import SquarePackingArchive.BentzLineCuts
import SquarePackingArchive.BentzFiveRowsPoints

namespace SquarePackingArchive.Bentz

theorem strip_chord_weight {cosine sine distance : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) (distance_upper : distance ≤ 1) :
    distance + (2 * Real.sqrt 2 - 2 * distance) * (cosine * sine) ≤ cosine + sine := by
  have root_nonnegative := Real.sqrt_nonneg (2 : ℝ)
  have root_sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have root_ge_one : 1 ≤ Real.sqrt 2 := by nlinarith
  have sum_lower : 1 ≤ cosine + sine := by nlinarith [mul_nonneg cosine_nonnegative sine_nonnegative]
  have sum_upper : cosine + sine ≤ Real.sqrt 2 := by nlinarith [sq_nonneg (cosine - sine)]
  have endpoint_product := mul_nonneg (show 0 ≤ Real.sqrt 2 - (cosine + sine) by linarith)
    (show 0 ≤ cosine + sine - 1 by linarith)
  have coefficient_nonnegative : 0 ≤ Real.sqrt 2 - distance := by linarith
  have weighted_product := mul_nonneg coefficient_nonnegative endpoint_product
  have remaining_product := mul_nonneg (show 0 ≤ 1 - distance by linarith)
    (show 0 ≤ Real.sqrt 2 - (cosine + sine) by linarith)
  have root_remaining := mul_nonneg root_nonnegative remaining_product
  nlinarith

theorem horizontal_chord_of_length_bound
    (square : PlacedSquare) {height length : ℝ}
    (cosine_positive : 0 < square.frame.cosine) (sine_positive : 0 < square.frame.sine)
    (cosine_length : length * square.frame.cosine ≤ 1)
    (sine_length : length * square.frame.sine ≤ 1)
    (offset_bound : |height - square.center.y| ≤
      (square.frame.cosine + square.frame.sine) / 2 - length * square.frame.cosine * square.frame.sine) :
    ∃ lower upper : ℝ, length ≤ upper - lower ∧
      ∀ horizontal ∈ Set.Ioo lower upper, square.Contains ⟨horizontal, height⟩ := by
  let lower := max (square.horizontalAdjacentChordStart 1 height)
    (square.horizontalAdjacentOtherLower 1 height)
  let upper := min (square.horizontalAdjacentOtherUpper 1 height)
    (square.horizontalAdjacentChordEnd 1 height)
  refine ⟨lower, upper, ?_, ?_⟩
  · have offset_limits := abs_le.mp offset_bound
    have pair_bounds :
        square.horizontalAdjacentChordStart 1 height + length ≤ square.horizontalAdjacentOtherUpper 1 height ∧
        square.horizontalAdjacentChordStart 1 height + length ≤ square.horizontalAdjacentChordEnd 1 height ∧
        square.horizontalAdjacentOtherLower 1 height + length ≤ square.horizontalAdjacentOtherUpper 1 height ∧
        square.horizontalAdjacentOtherLower 1 height + length ≤ square.horizontalAdjacentChordEnd 1 height := by
      dsimp [PlacedSquare.horizontalAdjacentChordStart, PlacedSquare.horizontalAdjacentChordEnd,
        PlacedSquare.horizontalAdjacentOtherLower, PlacedSquare.horizontalAdjacentOtherUpper]
      have scaled_unit :
          (height - square.center.y) * square.frame.cosine ^ 2 +
            (height - square.center.y) * square.frame.sine ^ 2 = height - square.center.y := by
        linear_combination (height - square.center.y) * square.frame.unit
      constructor
      · field_simp
        nlinarith
      constructor
      · field_simp
        nlinarith
      constructor
      · field_simp
        nlinarith
      · field_simp
        nlinarith
    dsimp [lower, upper]
    rw [le_sub_iff_add_le, add_comm length, ← max_add_add_right, le_min_iff, max_le_iff, max_le_iff]
    exact ⟨⟨pair_bounds.1, pair_bounds.2.2.1⟩, ⟨pair_bounds.2.1, pair_bounds.2.2.2⟩⟩
  · intro horizontal horizontal_mem
    have inside := square.horizontalChord_inside_dilatedInteriorRegion
      (show (0 : ℝ) < 1 by norm_num) cosine_positive sine_positive
      (le_max_left _ _) (le_max_right _ _) (min_le_left _ _) (min_le_right _ _)
      horizontal horizontal_mem
    rw [PlacedSquare.dilatedInteriorRegion_one] at inside
    exact ((square.mem_interiorRegion_iff _).1 inside).contains

theorem allocate_strip_chord_lengths {extent product distance position total : ℝ}
    (product_positive : 0 < product) (total_nonnegative : 0 ≤ total)
    (width_bound : distance + total * product ≤ 2 * extent) :
    ∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧ first + second = total ∧
      (0 < first → position ≤ extent - first * product) ∧
      (0 < second → distance - position ≤ extent - second * product) := by
  by_cases first_fits : position ≤ extent - total * product
  · exact ⟨total, 0, total_nonnegative, le_rfl, by ring, fun _ => first_fits, by intro positive; linarith⟩
  by_cases first_empty : extent ≤ position
  · exact ⟨0, total, le_rfl, total_nonnegative, by ring, by intro positive; linarith,
      fun _ => by linarith⟩
  let first := (extent - position) / product
  have first_positive : 0 < first := div_pos (by linarith) product_positive
  have first_upper : first ≤ total := by
    dsimp [first]
    rw [div_le_iff₀ product_positive]
    linarith
  have first_product : first * product = extent - position := by
    dsimp [first]
    field_simp
  exact ⟨first, total - first, first_positive.le, by linarith, by ring,
    fun _ => by linarith, fun _ => by nlinarith⟩

theorem horizontal_chord_of_axis_aligned
    (square : PlacedSquare) {height : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine) (sine_nonnegative : 0 ≤ square.frame.sine)
    (axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0)
    (offset : |height - square.center.y| ≤ 1 / 2) :
    ∃ lower upper : ℝ, 1 ≤ upper - lower ∧
      ∀ horizontal ∈ Set.Ioo lower upper, square.Contains ⟨horizontal, height⟩ := by
  refine ⟨square.center.x - 1 / 2, square.center.x + 1 / 2, by linarith, ?_⟩
  intro horizontal horizontal_mem
  have horizontal_bound : |horizontal - square.center.x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [horizontal_mem.1, horizontal_mem.2]
  rw [square.contains_iff_localCoordinates]
  rcases axis_aligned with cosine_zero | sine_zero
  · have sine_one : square.frame.sine = 1 := by nlinarith [square.frame.unit]
    simpa [PlacedSquare.localX, PlacedSquare.localY, cosine_zero, sine_one, abs_sub_comm] using
      And.intro offset horizontal_bound
  · have cosine_one : square.frame.cosine = 1 := by nlinarith [square.frame.unit]
    simpa [PlacedSquare.localX, PlacedSquare.localY, cosine_one, sine_zero] using
      And.intro horizontal_bound offset

theorem horizontal_two_line_chords_nonnegative_frame
    (square : PlacedSquare) {firstLine secondLine : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine) (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_lower : firstLine ≤ square.center.y) (center_upper : square.center.y ≤ secondLine)
    (distance_upper : secondLine - firstLine ≤ 1) :
    ∃ firstLower firstUpper secondLower secondUpper : ℝ,
      0 ≤ firstUpper - firstLower ∧ 0 ≤ secondUpper - secondLower ∧
      min 1 (2 * Real.sqrt 2 - 2 * (secondLine - firstLine)) ≤
        (firstUpper - firstLower) + (secondUpper - secondLower) ∧
      (∀ horizontal ∈ Set.Ioo firstLower firstUpper, square.Contains ⟨horizontal, firstLine⟩) ∧
      (∀ horizontal ∈ Set.Ioo secondLower secondUpper, square.Contains ⟨horizontal, secondLine⟩) := by
  let total := min 1 (2 * Real.sqrt 2 - 2 * (secondLine - firstLine))
  have root_lower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have total_nonnegative : 0 ≤ total := le_min (by norm_num) (by linarith)
  have total_upper : total ≤ 1 := min_le_left _ _
  have empty_interval (line : ℝ) : ∀ horizontal ∈ Set.Ioo (0 : ℝ) 0,
      square.Contains ⟨horizontal, line⟩ := by
    intro horizontal inside
    exact (lt_irrefl horizontal (inside.2.trans inside.1)).elim
  by_cases axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0
  · by_cases first_near : square.center.y - firstLine ≤ 1 / 2
    · obtain ⟨lower, upper, length_bound, inside⟩ := horizontal_chord_of_axis_aligned square
        cosine_nonnegative sine_nonnegative axis_aligned
        (height := firstLine) (by rw [abs_of_nonpos (by linarith)]; linarith)
      exact ⟨lower, upper, 0, 0, by linarith, by norm_num, by dsimp [total] at total_upper; linarith,
        inside, empty_interval secondLine⟩
    · obtain ⟨lower, upper, length_bound, inside⟩ := horizontal_chord_of_axis_aligned square
        cosine_nonnegative sine_nonnegative axis_aligned
        (height := secondLine) (by rw [abs_of_nonneg (by linarith)]; linarith)
      exact ⟨0, 0, lower, upper, by norm_num, by linarith, by dsimp [total] at total_upper; linarith,
        empty_interval firstLine, inside⟩
  push Not at axis_aligned
  have cosine_positive : 0 < square.frame.cosine := lt_of_le_of_ne cosine_nonnegative axis_aligned.1.symm
  have sine_positive : 0 < square.frame.sine := lt_of_le_of_ne sine_nonnegative axis_aligned.2.symm
  have product_positive := mul_pos cosine_positive sine_positive
  have cosine_upper : square.frame.cosine ≤ 1 := by nlinarith [square.frame.unit]
  have sine_upper : square.frame.sine ≤ 1 := by nlinarith [square.frame.unit]
  have weighted := strip_chord_weight cosine_nonnegative sine_nonnegative square.frame.unit distance_upper
  have smaller_weight := mul_le_mul_of_nonneg_right
    (min_le_right (1 : ℝ) (2 * Real.sqrt 2 - 2 * (secondLine - firstLine))) product_positive.le
  obtain ⟨first, second, first_nonnegative, second_nonnegative, total_eq, first_offset, second_offset⟩ :=
    allocate_strip_chord_lengths (extent := (square.frame.cosine + square.frame.sine) / 2)
      (product := square.frame.cosine * square.frame.sine) (position := square.center.y - firstLine)
      (distance := secondLine - firstLine) product_positive total_nonnegative (by dsimp [total] at *; linarith)
  have chord (line length : ℝ) (nonnegative : 0 ≤ length) (length_upper : length ≤ 1)
      (offset : 0 < length → |line - square.center.y| ≤
        (square.frame.cosine + square.frame.sine) / 2 - length * square.frame.cosine * square.frame.sine) :
      ∃ lower upper : ℝ, length ≤ upper - lower ∧
        ∀ horizontal ∈ Set.Ioo lower upper, square.Contains ⟨horizontal, line⟩ := by
    by_cases positive : 0 < length
    · exact horizontal_chord_of_length_bound square cosine_positive sine_positive
        (by nlinarith) (by nlinarith) (offset positive)
    · have zero : length = 0 := by linarith
      exact ⟨0, 0, by simp [zero], empty_interval line⟩
  obtain ⟨firstLower, firstUpper, first_length, first_inside⟩ := chord firstLine first first_nonnegative
    (by linarith) (by intro positive; rw [abs_of_nonpos (by linarith)]; nlinarith [first_offset positive])
  obtain ⟨secondLower, secondUpper, second_length, second_inside⟩ := chord secondLine second second_nonnegative
    (by linarith) (by intro positive; rw [abs_of_nonneg (by linarith)]; nlinarith [second_offset positive])
  exact ⟨firstLower, firstUpper, secondLower, secondUpper, by linarith, by linarith,
    by change total ≤ _; linarith, first_inside, second_inside⟩

theorem horizontal_two_line_chords
    (square : PlacedSquare) {firstLine secondLine : ℝ}
    (center_lower : firstLine ≤ square.center.y) (center_upper : square.center.y ≤ secondLine)
    (distance_upper : secondLine - firstLine ≤ 1) :
    ∃ firstLower firstUpper secondLower secondUpper : ℝ,
      0 ≤ firstUpper - firstLower ∧ 0 ≤ secondUpper - secondLower ∧
      min 1 (2 * Real.sqrt 2 - 2 * (secondLine - firstLine)) ≤
        (firstUpper - firstLower) + (secondUpper - secondLower) ∧
      (∀ horizontal ∈ Set.Ioo firstLower firstUpper, square.Contains ⟨horizontal, firstLine⟩) ∧
      (∀ horizontal ∈ Set.Ioo secondLower secondUpper, square.Contains ⟨horizontal, secondLine⟩) := by
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_nonnegative, second_nonnegative,
      length_bound, first_inside, second_inside⟩ := horizontal_two_line_chords_nonnegative_frame
    square.firstQuadrant square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    (by simpa only [PlacedSquare.firstQuadrant_center] using center_lower)
    (by simpa only [PlacedSquare.firstQuadrant_center] using center_upper) distance_upper
  exact ⟨firstLower, firstUpper, secondLower, secondUpper, first_nonnegative, second_nonnegative,
    length_bound, fun coordinate inside => (square.firstQuadrant_contains_iff _).1 (first_inside coordinate inside),
    fun coordinate inside => (square.firstQuadrant_contains_iff _).1 (second_inside coordinate inside)⟩

theorem vertical_two_line_chords
    (square : PlacedSquare) {firstLine secondLine : ℝ}
    (center_lower : firstLine ≤ square.center.x) (center_upper : square.center.x ≤ secondLine)
    (distance_upper : secondLine - firstLine ≤ 1) :
    ∃ firstLower firstUpper secondLower secondUpper : ℝ,
      0 ≤ firstUpper - firstLower ∧ 0 ≤ secondUpper - secondLower ∧
      min 1 (2 * Real.sqrt 2 - 2 * (secondLine - firstLine)) ≤
        (firstUpper - firstLower) + (secondUpper - secondLower) ∧
      (∀ vertical ∈ Set.Ioo firstLower firstUpper, square.Contains ⟨firstLine, vertical⟩) ∧
      (∀ vertical ∈ Set.Ioo secondLower secondUpper, square.Contains ⟨secondLine, vertical⟩) := by
  obtain ⟨firstLower, firstUpper, secondLower, secondUpper, first_nonnegative, second_nonnegative,
      length_bound, first_inside, second_inside⟩ := horizontal_two_line_chords square.swap
    center_lower center_upper distance_upper
  exact ⟨firstLower, firstUpper, secondLower, secondUpper, first_nonnegative, second_nonnegative,
    length_bound, fun coordinate inside => (square.swap_contains_iff _).1 (first_inside coordinate inside),
    fun coordinate inside => (square.swap_contains_iff _).1 (second_inside coordinate inside)⟩

end SquarePackingArchive.Bentz
