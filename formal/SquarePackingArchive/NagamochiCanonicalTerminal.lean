import SquarePackingArchive.NagamochiCanonicalBoundary

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma vertical_openSegment_subset_of_open_convex_closure
    {region : Set Plane} (region_convex : Convex ℝ region)
    (region_open : IsOpen region)
    {bottom top width : ℝ} (bottom_lt_top : bottom < top)
    (bottom_mem : ![width, bottom] ∈ region)
    (top_mem : ![width, top] ∈ closure region) :
    ∀ coordinate ∈ Ioo bottom top, ![width, coordinate] ∈ region := by
  intro coordinate coordinate_mem
  let ratio := (coordinate - bottom) / (top - bottom)
  have denominator_positive : 0 < top - bottom := sub_pos.mpr bottom_lt_top
  have ratio_mem : ratio ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [ratio]
      exact div_pos (sub_pos.mpr coordinate_mem.1) denominator_positive
    · dsimp [ratio]
      rw [div_lt_one denominator_positive]
      linarith [coordinate_mem.2]
  have segment_mem := lineMap_mem_openSegment
    ℝ ![width, bottom] ![width, top] ratio_mem
  have interior_mem :=
    region_convex.openSegment_interior_closure_subset_interior
      (by simpa [region_open.interior_eq] using bottom_mem) top_mem segment_mem
  rw [region_open.interior_eq] at interior_mem
  convert interior_mem using 1
  funext index
  fin_cases index
  · simp [AffineMap.lineMap_apply_module]
    ring
  · simp [AffineMap.lineMap_apply_module, ratio]
    field_simp [ne_of_gt denominator_positive]
    ring

lemma canonicalPinned_horizontal_boundary_chord
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    NagamochiResource.HasBoundaryChord size .bottom
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion
      (pinnedCutChord tangentHalfAngle) := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have cosine_positive :
      0 < (canonicalPinnedSquare tangentHalfAngle).frame.cosine := by
    rw [canonicalPinnedSquare_frame]
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) denominator_positive
  have sine_positive :
      0 < (canonicalPinnedSquare tangentHalfAngle).frame.sine := by
    rw [canonicalPinnedSquare_frame]
    simp only [Frame.ofTangentHalfAngle_sine]
    exact div_pos (by positivity) denominator_positive
  have endpoint_bounds := canonicalPinned_cut_vertex_x_bounds
    tangent_positive tangent_lt
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  refine ⟨canonicalPinnedFirstCutVertex tangentHalfAngle 0,
    canonicalPinnedSecondCutVertex tangentHalfAngle 0, ?_, ?_, ?_⟩
  · rw [canonicalPinned_cut_chord_length tangent_positive tangent_lt_one]
  · intro coordinate coordinate_mem
    rcases coordinate_mem with ⟨coordinate_gt, coordinate_lt⟩
    constructor <;> linarith
  · intro coordinate coordinate_mem
    have order := canonicalPinned_horizontal_other_order
      tangent_positive tangent_lt_one
    have inside :=
      (canonicalPinnedSquare tangentHalfAngle).horizontalOtherAdjacentChord_inside_dilatedInteriorRegion
          (factor := 1) (height := 1) (by norm_num) cosine_positive sine_positive
          order.1 order.2 coordinate
    rw [canonicalPinned_horizontal_start_eq tangent_positive tangent_lt_one,
      canonicalPinned_horizontal_end_eq tangent_positive tangent_lt_one] at inside
    rw [(canonicalPinnedSquare tangentHalfAngle).dilatedInteriorRegion_one] at inside
    exact inside coordinate_mem

noncomputable def canonicalPinnedVerticalCrossing (tangentHalfAngle : ℝ) : ℝ :=
  1 - pinnedCutMissingLength tangentHalfAngle

noncomputable def canonicalPinnedVerticalCrossingCoordinates
    (tangentHalfAngle : ℝ) : Plane :=
  let frame := Frame.ofTangentHalfAngle tangentHalfAngle
  let verticalDelta := 1 / 10 - pinnedCutMissingLength tangentHalfAngle
  pinnedPointOneCoordinates frame +
    ![frame.sine * verticalDelta, frame.cosine * verticalDelta]

lemma canonicalPinned_vertical_crossing_transform
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    (canonicalPinnedSquare tangentHalfAngle).transform
        (canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle) =
      ![(1 : ℝ), canonicalPinnedVerticalCrossing tangentHalfAngle] := by
  have cosine_nonzero :
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ≠ 0 := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    apply div_ne_zero
    · nlinarith
    · positivity
  have point_one := pinned_point_one_eq
    (Frame.ofTangentHalfAngle tangentHalfAngle) cosine_nonzero
  change (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform _ = _
  rw [show canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle =
      pinnedPointOneCoordinates (Frame.ofTangentHalfAngle tangentHalfAngle) +
        ![(Frame.ofTangentHalfAngle tangentHalfAngle).sine *
            (1 / 10 - pinnedCutMissingLength tangentHalfAngle),
          (Frame.ofTangentHalfAngle tangentHalfAngle).cosine *
            (1 / 10 - pinnedCutMissingLength tangentHalfAngle)] by
      rfl]
  rw [show
      (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform
          (pinnedPointOneCoordinates (Frame.ofTangentHalfAngle tangentHalfAngle) +
            ![(Frame.ofTangentHalfAngle tangentHalfAngle).sine *
                (1 / 10 - pinnedCutMissingLength tangentHalfAngle),
              (Frame.ofTangentHalfAngle tangentHalfAngle).cosine *
                (1 / 10 - pinnedCutMissingLength tangentHalfAngle)]) =
        (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform
            (pinnedPointOneCoordinates (Frame.ofTangentHalfAngle tangentHalfAngle)) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
            ![(Frame.ofTangentHalfAngle tangentHalfAngle).sine *
                (1 / 10 - pinnedCutMissingLength tangentHalfAngle),
              (Frame.ofTangentHalfAngle tangentHalfAngle).cosine *
                (1 / 10 - pinnedCutMissingLength tangentHalfAngle)] by
      simp only [PlacedSquare.transform, pinnedSquare_frame]
      rw [map_add]
      abel]
  rw [point_one]
  funext coordinate
  fin_cases coordinate
  · simp [Frame.rotation_apply_zero, canonicalPinnedVerticalCrossing]
    ring
  · simp [Frame.rotation_apply_one, canonicalPinnedVerticalCrossing]
    have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
    field_simp [denominator_ne]
    ring

lemma canonicalPinned_vertical_crossing_coordinates_mem_closure
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle ∈ unitSquareClosure := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have tangent_lt_fourteen_twenty_fifths : tangentHalfAngle < 14 / 25 := by
    by_contra not_lt
    have tangent_at_least : 14 / 25 ≤ tangentHalfAngle := le_of_not_gt not_lt
    nlinarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have cosine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) denominator_positive
  have cosine_gt_half :
      1 / 2 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    rw [lt_div_iff₀ denominator_positive]
    nlinarith
  have sine_nonnegative :
      0 ≤ (Frame.ofTangentHalfAngle tangentHalfAngle).sine := by
    simp only [Frame.ofTangentHalfAngle_sine]
    positivity
  have sine_le_one :=
    (Frame.ofTangentHalfAngle tangentHalfAngle).sine_le_one sine_nonnegative
  have cosine_le_one :=
    (Frame.ofTangentHalfAngle tangentHalfAngle).cosine_le_one cosine_positive.le
  have missing_positive :
      0 < pinnedCutMissingLength tangentHalfAngle := by
    have numerator_positive := pinnedMissingNumerator_positive
      tangent_positive tangent_lt
    have one_minus_square_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
      nlinarith
    dsimp [pinnedCutMissingLength]
    exact div_pos (mul_pos (mul_pos (by norm_num) tangent_positive)
      numerator_positive) (sq_pos_of_pos one_minus_square_positive)
  have missing_lt_tenth := pinnedCutMissingLength_lt_tenth
    tangent_positive tangent_lt
  have vertical_delta_positive :
      0 < 1 / 10 - pinnedCutMissingLength tangentHalfAngle := by linarith
  have vertical_delta_lt_tenth :
      1 / 10 - pinnedCutMissingLength tangentHalfAngle < 1 / 10 := by linarith
  have local_y : canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 1 = 1 / 2 := by
    have margin := canonicalPinned_point_one_local_vertical_margin
      tangent_positive tangent_lt
    change pinnedPointOneCoordinates (Frame.ofTangentHalfAngle tangentHalfAngle) 1 +
        (Frame.ofTangentHalfAngle tangentHalfAngle).cosine *
          (1 / 10 - pinnedCutMissingLength tangentHalfAngle) = 1 / 2
    simp only [pinnedPointOneCoordinates, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    linarith
  intro coordinate coordinate_mem
  fin_cases coordinate
  · have local_x :
        canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 0 =
          1 / 2 - (Frame.ofTangentHalfAngle tangentHalfAngle).cosine +
            (Frame.ofTangentHalfAngle tangentHalfAngle).sine *
              (1 / 10 - pinnedCutMissingLength tangentHalfAngle) := by
        simp [canonicalPinnedVerticalCrossingCoordinates, pinnedPointOneCoordinates]
    change -(1 / 2) ≤ canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 0 ∧
      canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 0 ≤ 1 / 2
    rw [local_x]
    constructor
    · nlinarith
    · have product_lt_tenth :
          (Frame.ofTangentHalfAngle tangentHalfAngle).sine *
              (1 / 10 - pinnedCutMissingLength tangentHalfAngle) < 1 / 10 := by
        nlinarith
      linarith
  · change -(1 / 2) ≤ canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 1 ∧
      canonicalPinnedVerticalCrossingCoordinates tangentHalfAngle 1 ≤ 1 / 2
    rw [local_y]
    norm_num

lemma canonicalPinned_vertical_crossing_mem_closure
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    ![(1 : ℝ), canonicalPinnedVerticalCrossing tangentHalfAngle] ∈
      closure (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  have tangent_lt_one : tangentHalfAngle < 1 := by
    have sqrt_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
    linarith
  rw [← canonicalPinned_vertical_crossing_transform tangent_positive tangent_lt_one]
  exact (canonicalPinnedSquare tangentHalfAngle).transform_mem_closure_interiorRegion
      (canonicalPinned_vertical_crossing_coordinates_mem_closure tangent_positive tangent_lt)

lemma canonicalPinned_vertical_boundary_chord
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    NagamochiResource.HasBoundaryChord size .left
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion
      (1 / 10 - pinnedCutMissingLength tangentHalfAngle) := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have one_minus_square_positive : 0 < 1 - tangentHalfAngle ^ 2 := by nlinarith
  have numerator_positive := pinnedMissingNumerator_positive
    tangent_positive tangent_lt
  have missing_positive : 0 < pinnedCutMissingLength tangentHalfAngle := by
    dsimp [pinnedCutMissingLength]
    exact div_pos (mul_pos (mul_pos (by norm_num) tangent_positive)
      numerator_positive) (sq_pos_of_pos one_minus_square_positive)
  have missing_lt_tenth := pinnedCutMissingLength_lt_tenth
    tangent_positive tangent_lt
  have crossing_gt_bottom :
      9 / 10 < canonicalPinnedVerticalCrossing tangentHalfAngle := by
    dsimp [canonicalPinnedVerticalCrossing]
    linarith
  have crossing_lt_one : canonicalPinnedVerticalCrossing tangentHalfAngle < 1 := by
    dsimp [canonicalPinnedVerticalCrossing]
    linarith
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  refine ⟨9 / 10, canonicalPinnedVerticalCrossing tangentHalfAngle, ?_, ?_, ?_⟩
  · dsimp [canonicalPinnedVerticalCrossing]
    linarith
  · intro coordinate coordinate_mem
    rcases coordinate_mem with ⟨coordinate_gt, coordinate_lt⟩
    constructor <;> linarith
  · exact vertical_openSegment_subset_of_open_convex_closure
      (canonicalPinnedSquare tangentHalfAngle).convex_interiorRegion
      (canonicalPinnedSquare tangentHalfAngle).isOpen_interiorRegion
      crossing_gt_bottom
      (canonicalPinned_point_one_mem tangent_positive tangent_lt)
      (canonicalPinned_vertical_crossing_mem_closure tangent_positive tangent_lt)

lemma canonicalPinned_boundary_corner_bound
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    ENNReal.ofReal (pinnedBoundaryCornerScore tangentHalfAngle) ≤
      NagamochiResource.boundaryLines size
          (canonicalPinnedSquare tangentHalfAngle).interiorRegion +
        NagamochiResource.cornerPoints size
          (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  let region := (canonicalPinnedSquare tangentHalfAngle).interiorRegion
  have region_measurable : MeasurableSet region :=
    (canonicalPinnedSquare tangentHalfAngle).measurableSet_interiorRegion
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have chord_positive : 0 < pinnedCutChord tangentHalfAngle := by
    dsimp [pinnedCutChord]
    positivity
  have one_minus_square_positive : 0 < 1 - tangentHalfAngle ^ 2 := by nlinarith
  have numerator_positive := pinnedMissingNumerator_positive
    tangent_positive tangent_lt
  have missing_positive : 0 < pinnedCutMissingLength tangentHalfAngle := by
    dsimp [pinnedCutMissingLength]
    exact div_pos (mul_pos (mul_pos (by norm_num) tangent_positive)
      numerator_positive) (sq_pos_of_pos one_minus_square_positive)
  have missing_lt_tenth := pinnedCutMissingLength_lt_tenth
    tangent_positive tangent_lt
  have vertical_length_positive :
      0 < 1 / 10 - pinnedCutMissingLength tangentHalfAngle := by linarith
  have horizontal_chord := canonicalPinned_horizontal_boundary_chord
    size_at_least_three tangent_positive tangent_lt
  have vertical_chord := canonicalPinned_vertical_boundary_chord
    size_at_least_three tangent_positive tangent_lt
  have horizontal_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable horizontal_chord
  have vertical_line_bound :=
    NagamochiResource.boundaryLine_lower_bound_of_chord
      region_measurable vertical_chord
  have pair_subset :
      ({NagamochiResource.BoundarySide.bottom,
          NagamochiResource.BoundarySide.left} :
        Finset NagamochiResource.BoundarySide) ⊆
        NagamochiResource.boundarySides := by
    intro side side_mem
    exact NagamochiResource.mem_boundarySides side
  have pair_bound := NagamochiResource.boundaryLines_subset_lower_bound
    (size := size) (region := region) pair_subset
  rw [Finset.sum_pair (by decide :
    NagamochiResource.BoundarySide.bottom ≠
      NagamochiResource.BoundarySide.left)] at pair_bound
  have boundary_bound :
      (1 / 2 : ENNReal) *
          (ENNReal.ofReal (pinnedCutChord tangentHalfAngle) +
            ENNReal.ofReal
              (1 / 10 - pinnedCutMissingLength tangentHalfAngle)) ≤
        NagamochiResource.boundaryLines size region :=
    (mul_le_mul le_rfl
      (add_le_add horizontal_line_bound vertical_line_bound)
      bot_le bot_le).trans pair_bound
  have corner_mem :
      NagamochiResource.cornerPoint size .leftBottom ∈ region := by
    simpa [region, NagamochiResource.cornerPoint] using
      canonicalPinned_point_one_mem tangent_positive tangent_lt
  have corner_bound := NagamochiResource.cornerPoints_lower_bound_of_mem
    (.leftBottom) region_measurable corner_mem
  have encoded_score_eq :
      ENNReal.ofReal (pinnedBoundaryCornerScore tangentHalfAngle) =
        (1 / 2 : ENNReal) *
            (ENNReal.ofReal (pinnedCutChord tangentHalfAngle) +
              ENNReal.ofReal
                (1 / 10 - pinnedCutMissingLength tangentHalfAngle)) +
          9 / 20 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul,
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal chord_positive.le,
      ENNReal.toReal_ofReal vertical_length_positive.le]
    rw [ENNReal.toReal_ofReal]
    · norm_num
      dsimp [pinnedBoundaryCornerScore]
      ring
    · dsimp [pinnedBoundaryCornerScore]
      linarith
  rw [encoded_score_eq]
  exact add_le_add boundary_bound corner_bound

lemma canonicalPinned_score_gt_one
    {size : ℕ} (size_at_least_three : 3 ≤ size)
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    1 < NagamochiResource.measure size
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  have missing_lt_tenth := pinnedCutMissingLength_lt_tenth
    tangent_positive tangent_lt
  have chord_positive : 0 < pinnedCutChord tangentHalfAngle := by
    dsimp [pinnedCutChord]
    have sqrt_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
    positivity
  have boundary_nonnegative :
      0 ≤ pinnedBoundaryCornerScore tangentHalfAngle := by
    dsimp [pinnedBoundaryCornerScore]
    linarith
  exact score_gt_one_of_pinned_cut_witness_and_boundary_bound
    (canonicalPinnedTriangleWitness size_at_least_three
      tangent_positive tangent_lt)
    tangent_positive tangent_lt boundary_nonnegative
    (canonicalPinned_boundary_corner_bound size_at_least_three
      tangent_positive tangent_lt)

end SquarePackingArchive.Nagamochi
