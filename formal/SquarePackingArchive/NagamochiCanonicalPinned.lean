import SquarePackingArchive.NagamochiLemmas

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

noncomputable def pinnedEdgeParameter (frame : Frame) : ℝ :=
  (9 / 10 - frame.sine) / frame.cosine

noncomputable def pinnedNegativeVertex (frame : Frame) : Plane :=
  ![2 - frame.cosine + pinnedEdgeParameter frame * frame.sine, 0]

noncomputable def pinnedSquare (frame : Frame) : PlacedSquare :=
  PlacedSquare.fromNegativeVertex (pinnedNegativeVertex frame) frame

lemma pinnedSquare_frame (frame : Frame) :
    (pinnedSquare frame).frame = frame := by
  rfl

lemma pinnedSquare_transform (frame : Frame) (coordinates : Plane) :
    (pinnedSquare frame).transform coordinates =
      pinnedNegativeVertex frame +
        frame.rotation (coordinates + ![1 / 2, 1 / 2]) := by
  exact PlacedSquare.fromNegativeVertex_transform _ _ _

lemma pinned_point_two_eq
    (frame : Frame) (cosine_nonzero : frame.cosine ≠ 0) :
    (pinnedSquare frame).transform
        ![1 / 2, pinnedEdgeParameter frame - 1 / 2] =
      ![(2 : ℝ), 9 / 10] := by
  funext coordinate
  fin_cases coordinate <;>
    simp [pinnedSquare_transform, pinnedNegativeVertex,
      pinnedEdgeParameter, Frame.rotation_apply_zero,
      Frame.rotation_apply_one] <;>
    field_simp [cosine_nonzero] <;>
    ring

noncomputable def canonicalPinnedSquare
    (tangentHalfAngle : ℝ) : PlacedSquare :=
  pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)

lemma canonicalPinnedSquare_frame (tangentHalfAngle : ℝ) :
    (canonicalPinnedSquare tangentHalfAngle).frame =
      Frame.ofTangentHalfAngle tangentHalfAngle := by
  rfl

lemma canonicalPinnedSquare_center_x (tangentHalfAngle : ℝ) :
    (canonicalPinnedSquare tangentHalfAngle).center.x =
      (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 0 := by
  change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 0 = _
  simp [canonicalPinnedSquare, pinnedSquare]

lemma canonicalPinnedSquare_center_y (tangentHalfAngle : ℝ) :
    (canonicalPinnedSquare tangentHalfAngle).center.y =
      (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1 / 2, 1 / 2]) 1 := by
  change (canonicalPinnedSquare tangentHalfAngle).center.toPlane 1 = _
  simp [canonicalPinnedSquare, pinnedSquare]

lemma canonicalPinned_first_cut_vertex_eq
    (tangentHalfAngle : ℝ) :
    pinnedCutApex (canonicalPinnedSquare tangentHalfAngle) +
        (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame).rotation
          ![pinnedCutFirstLegLength tangentHalfAngle, 0] =
      pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
          ![tangentHalfAngle, 1] := by
  rw [pinnedCut_first_vertex_eq]
  change (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform
      ![tangentHalfAngle - 1 / 2, 1 / 2] = _
  rw [pinnedSquare_transform]
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp <;> ring_nf

lemma canonicalPinned_second_cut_vertex_eq
    {tangentHalfAngle : ℝ} (tangent_ne_neg_one : tangentHalfAngle ≠ -1) :
    pinnedCutApex (canonicalPinnedSquare tangentHalfAngle) +
        (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame).rotation
          ![0, pinnedCutSecondLegLength tangentHalfAngle] =
      pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
          ![1, (1 - tangentHalfAngle) / (1 + tangentHalfAngle)] := by
  rw [pinnedCut_second_vertex_eq]
  change (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform
      ![1 / 2, 1 / 2 - pinnedCutSecondLegLength tangentHalfAngle] = _
  rw [pinnedSquare_transform]
  rw [add_left_cancel_iff]
  congr 1
  have one_add_tangent_ne : 1 + tangentHalfAngle ≠ 0 := by
    intro equality
    apply tangent_ne_neg_one
    linarith
  funext coordinate
  fin_cases coordinate <;> simp [pinnedCutSecondLegLength] <;>
    field_simp [one_add_tangent_ne] <;> ring

lemma canonicalPinned_first_cut_vertex_y
    {tangentHalfAngle : ℝ} :
    (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
          ![tangentHalfAngle, 1]) 1 = 1 := by
  simp [pinnedNegativeVertex, Frame.rotation_apply_one]
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  field_simp [denominator_ne]
  ring

lemma canonicalPinned_second_cut_vertex_y
    {tangentHalfAngle : ℝ} (tangent_ne_neg_one : tangentHalfAngle ≠ -1) :
    (pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
          ![1, (1 - tangentHalfAngle) / (1 + tangentHalfAngle)]) 1 = 1 := by
  simp [pinnedNegativeVertex, Frame.rotation_apply_one]
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have one_add_tangent_ne : 1 + tangentHalfAngle ≠ 0 := by
    intro equality
    apply tangent_ne_neg_one
    linarith
  field_simp [denominator_ne, one_add_tangent_ne]
  ring

noncomputable def canonicalPinnedFirstCutVertex (tangentHalfAngle : ℝ) : Plane :=
  pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
    (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
      ![tangentHalfAngle, 1]

noncomputable def canonicalPinnedSecondCutVertex (tangentHalfAngle : ℝ) : Plane :=
  pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
    (Frame.ofTangentHalfAngle tangentHalfAngle).rotation
      ![1, (1 - tangentHalfAngle) / (1 + tangentHalfAngle)]

lemma pinnedMissingNumerator_positive
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    0 < tangentHalfAngle * (1 - tangentHalfAngle) ^ 2 -
      tangentHalfAngle / 5 := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have one_minus_tangent_gt :
      Real.sqrt (1 / 5) < 1 - tangentHalfAngle := by linarith
  have square_gt : 1 / 5 < (1 - tangentHalfAngle) ^ 2 := by
    nlinarith
  nlinarith

lemma canonicalPinnedFirstCutVertex_x_sub_one
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    canonicalPinnedFirstCutVertex tangentHalfAngle 0 - 1 =
      tangentHalfAngle *
          (5 * tangentHalfAngle ^ 2 - 10 * tangentHalfAngle + 4) /
        (5 * (1 - tangentHalfAngle ^ 2)) := by
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have one_minus_tangent_sq_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  simp [canonicalPinnedFirstCutVertex, pinnedNegativeVertex,
    pinnedEdgeParameter, Frame.rotation_apply_zero]
  field_simp [denominator_ne, one_minus_tangent_sq_ne]
  ring

lemma two_sub_canonicalPinnedSecondCutVertex_x
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    2 - canonicalPinnedSecondCutVertex tangentHalfAngle 0 =
      tangentHalfAngle / (5 * (1 - tangentHalfAngle ^ 2)) := by
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have one_minus_tangent_sq_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  have one_add_tangent_ne : 1 + tangentHalfAngle ≠ 0 := by linarith
  simp [canonicalPinnedSecondCutVertex, pinnedNegativeVertex,
    pinnedEdgeParameter, Frame.rotation_apply_zero]
  field_simp [denominator_ne, one_minus_tangent_sq_ne, one_add_tangent_ne]
  ring

lemma canonicalPinned_cut_vertex_x_bounds
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    1 < canonicalPinnedFirstCutVertex tangentHalfAngle 0 ∧
      canonicalPinnedSecondCutVertex tangentHalfAngle 0 < 2 := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have one_minus_tangent_sq_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
    nlinarith
  have missing_positive := pinnedMissingNumerator_positive
    tangent_positive tangent_lt
  have polynomial_positive :
      0 < 5 * tangentHalfAngle ^ 2 - 10 * tangentHalfAngle + 4 := by
    nlinarith
  constructor
  · rw [← sub_pos, canonicalPinnedFirstCutVertex_x_sub_one tangent_positive tangent_lt_one]
    positivity
  · rw [← sub_pos, two_sub_canonicalPinnedSecondCutVertex_x
      tangent_positive tangent_lt_one]
    positivity

noncomputable def canonicalPinnedApex (tangentHalfAngle : ℝ) : Plane :=
  pinnedCutApex (canonicalPinnedSquare tangentHalfAngle)

lemma canonicalPinnedApex_eq (tangentHalfAngle : ℝ) :
    canonicalPinnedApex tangentHalfAngle =
      pinnedNegativeVertex (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).rotation ![1, 1] := by
  rw [canonicalPinnedApex, pinnedCutApex]
  change (pinnedSquare (Frame.ofTangentHalfAngle tangentHalfAngle)).transform
      ![1 / 2, 1 / 2] = _
  rw [pinnedSquare_transform]
  congr 1
  funext coordinate
  fin_cases coordinate <;> norm_num

lemma canonicalPinned_cut_chord_length
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    canonicalPinnedSecondCutVertex tangentHalfAngle 0 -
        canonicalPinnedFirstCutVertex tangentHalfAngle 0 =
      pinnedCutChord tangentHalfAngle := by
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have one_minus_tangent_sq_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  have one_add_tangent_ne : 1 + tangentHalfAngle ≠ 0 := by linarith
  simp [canonicalPinnedFirstCutVertex, canonicalPinnedSecondCutVertex,
    pinnedNegativeVertex, pinnedEdgeParameter, pinnedCutChord,
    Frame.rotation_apply_zero]
  field_simp [denominator_ne, one_minus_tangent_sq_ne, one_add_tangent_ne]
  ring

lemma canonicalPinned_first_x_lt_second_x
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    canonicalPinnedFirstCutVertex tangentHalfAngle 0 <
      canonicalPinnedSecondCutVertex tangentHalfAngle 0 := by
  rw [← sub_pos, canonicalPinned_cut_chord_length tangent_positive tangent_lt_one]
  simp only [pinnedCutChord]
  positivity

lemma canonicalPinnedApex_x_between
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    canonicalPinnedFirstCutVertex tangentHalfAngle 0 <
        canonicalPinnedApex tangentHalfAngle 0 ∧
      canonicalPinnedApex tangentHalfAngle 0 <
        canonicalPinnedSecondCutVertex tangentHalfAngle 0 := by
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have cosine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) denominator_positive
  have sine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).sine := by
    simp only [Frame.ofTangentHalfAngle_sine]
    exact div_pos (by positivity) denominator_positive
  have one_add_tangent_positive : 0 < 1 + tangentHalfAngle := by linarith
  have first_difference :
      canonicalPinnedApex tangentHalfAngle 0 -
          canonicalPinnedFirstCutVertex tangentHalfAngle 0 =
        pinnedCutFirstLegLength tangentHalfAngle *
          (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    rw [canonicalPinnedApex_eq]
    simp [canonicalPinnedFirstCutVertex, pinnedCutFirstLegLength,
      Frame.rotation_apply_zero]
    ring
  have second_difference :
      canonicalPinnedSecondCutVertex tangentHalfAngle 0 -
          canonicalPinnedApex tangentHalfAngle 0 =
        pinnedCutSecondLegLength tangentHalfAngle *
          (Frame.ofTangentHalfAngle tangentHalfAngle).sine := by
    rw [canonicalPinnedApex_eq]
    simp [canonicalPinnedSecondCutVertex, pinnedCutSecondLegLength,
      Frame.rotation_apply_zero]
    field_simp [one_add_tangent_positive.ne']
    ring
  constructor
  · rw [← sub_pos, first_difference]
    exact mul_pos (by simp [pinnedCutFirstLegLength]; linarith) cosine_positive
  · rw [← sub_pos, second_difference]
    exact mul_pos (by simp [pinnedCutSecondLegLength]; positivity) sine_positive

lemma canonicalPinnedApex_y_bounds
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    1 < canonicalPinnedApex tangentHalfAngle 1 ∧
      canonicalPinnedApex tangentHalfAngle 1 < 2 := by
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have apex_y_eq :
      canonicalPinnedApex tangentHalfAngle 1 =
        (1 + 2 * tangentHalfAngle - tangentHalfAngle ^ 2) /
          (1 + tangentHalfAngle ^ 2) := by
    rw [canonicalPinnedApex_eq]
    simp [pinnedNegativeVertex, Frame.rotation_apply_one]
    ring
  rw [apex_y_eq]
  constructor
  · rw [lt_div_iff₀ denominator_positive]
    nlinarith
  · rw [div_lt_iff₀ denominator_positive]
    nlinarith [sq_nonneg (1 - tangentHalfAngle)]

lemma canonicalPinned_vertices_mem_inner
    {size : ℕ} {tangentHalfAngle : ℝ}
    (size_at_least_three : 3 ≤ size)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    canonicalPinnedApex tangentHalfAngle ∈
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) ∧
      canonicalPinnedFirstCutVertex tangentHalfAngle ∈
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) ∧
      canonicalPinnedSecondCutVertex tangentHalfAngle ∈
        Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have endpoint_bounds := canonicalPinned_cut_vertex_x_bounds
    tangent_positive tangent_lt
  have first_x_lt_second_x := canonicalPinned_first_x_lt_second_x
    tangent_positive tangent_lt_one
  have apex_x_between := canonicalPinnedApex_x_between
    tangent_positive tangent_lt_one
  have apex_y_bounds := canonicalPinnedApex_y_bounds
    tangent_positive tangent_lt_one
  have first_y : canonicalPinnedFirstCutVertex tangentHalfAngle 1 = 1 := by
    exact canonicalPinned_first_cut_vertex_y
  have second_y : canonicalPinnedSecondCutVertex tangentHalfAngle 1 = 1 := by
    exact canonicalPinned_second_cut_vertex_y (by linarith)
  constructor
  · constructor <;> intro coordinate <;> fin_cases coordinate
    · exact apex_x_between.1.le.trans' endpoint_bounds.1.le
    · exact apex_y_bounds.1.le
    · exact apex_x_between.2.le.trans
        (endpoint_bounds.2.le.trans (by linarith))
    · exact apex_y_bounds.2.le.trans (by linarith)
  · constructor
    · constructor <;> intro coordinate <;> fin_cases coordinate
      · exact endpoint_bounds.1.le
      · change 1 ≤ canonicalPinnedFirstCutVertex tangentHalfAngle 1
        exact first_y.ge
      · exact first_x_lt_second_x.le.trans
          (endpoint_bounds.2.le.trans (by linarith))
      · change canonicalPinnedFirstCutVertex tangentHalfAngle 1 ≤
          (size : ℝ) - 1
        rw [first_y]
        linarith
    · constructor <;> intro coordinate <;> fin_cases coordinate
      · exact endpoint_bounds.1.le.trans first_x_lt_second_x.le
      · change 1 ≤ canonicalPinnedSecondCutVertex tangentHalfAngle 1
        exact second_y.ge
      · exact endpoint_bounds.2.le.trans (by linarith)
      · change canonicalPinnedSecondCutVertex tangentHalfAngle 1 ≤
          (size : ℝ) - 1
        rw [second_y]
        linarith

lemma canonicalPinnedCutTriangle_inside_inner
    {size : ℕ} {tangentHalfAngle : ℝ}
    (size_at_least_three : 3 ≤ size)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    pinnedCutTriangleRegion (canonicalPinnedApex tangentHalfAngle)
        (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame)
        tangentHalfAngle ⊆
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have first_leg_positive :
      0 < pinnedCutFirstLegLength tangentHalfAngle := by
    simp only [pinnedCutFirstLegLength]
    linarith
  have second_leg_positive :
      0 < pinnedCutSecondLegLength tangentHalfAngle := by
    simp only [pinnedCutSecondLegLength]
    positivity
  have vertices := canonicalPinned_vertices_mem_inner size_at_least_three
    tangent_positive tangent_lt
  apply interior_subset.trans
  apply orientedTranslatedRightTriangleRegion_subset_of_vertices_mem
    (canonicalPinnedApex tangentHalfAngle)
    (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame)
    first_leg_positive second_leg_positive (convex_Icc _ _) vertices.1
  · rw [canonicalPinnedApex, canonicalPinned_first_cut_vertex_eq]
    exact vertices.2.1
  · rw [canonicalPinnedApex,
      canonicalPinned_second_cut_vertex_eq (tangentHalfAngle := tangentHalfAngle)
        (by linarith)]
    exact vertices.2.2

lemma canonicalPinnedCutTriangle_inside_square
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt_one : tangentHalfAngle < 1) :
    pinnedCutTriangleRegion (canonicalPinnedApex tangentHalfAngle)
        (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame)
        tangentHalfAngle ⊆
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  exact pinnedCutTriangleRegion_subset_interiorRegion
    (canonicalPinnedSquare tangentHalfAngle) tangent_positive tangent_lt_one

lemma canonicalPinnedTriangleWitness
    {size : ℕ} {tangentHalfAngle : ℝ}
    (size_at_least_three : 3 ≤ size)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    PinnedCutTriangleWitness size
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion
      (canonicalPinnedApex tangentHalfAngle)
      (pinnedCutFrame (canonicalPinnedSquare tangentHalfAngle).frame)
      tangentHalfAngle := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have vertices := canonicalPinned_vertices_mem_inner size_at_least_three
    tangent_positive tangent_lt
  refine {
    region_convex := (canonicalPinnedSquare tangentHalfAngle).convex_interiorRegion
    region_open := (canonicalPinnedSquare tangentHalfAngle).isOpen_interiorRegion
    region_nonempty :=
      (canonicalPinnedSquare tangentHalfAngle).nonempty_interiorRegion
    origin_mem_closure := pinnedCutApex_mem_closure_interiorRegion _
    first_vertex_mem_closure :=
      pinnedCut_first_vertex_mem_closure_interiorRegion _
        tangent_positive.le tangent_lt_one.le
    second_vertex_mem_closure :=
      pinnedCut_second_vertex_mem_closure_interiorRegion _
        tangent_positive.le tangent_lt_one.le
    origin_mem_inner := vertices.1
    first_vertex_mem_inner := ?_
    second_vertex_mem_inner := ?_
  }
  · rw [canonicalPinnedApex, canonicalPinned_first_cut_vertex_eq]
    exact vertices.2.1
  · rw [canonicalPinnedApex,
      canonicalPinned_second_cut_vertex_eq (tangentHalfAngle := tangentHalfAngle)
        (by linarith)]
    exact vertices.2.2

lemma canonicalPinned_innerArea_lower_bound
    {size : ℕ} {tangentHalfAngle : ℝ}
    (size_at_least_three : 3 ≤ size)
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    ENNReal.ofReal (pinnedCutArea tangentHalfAngle) ≤
      NagamochiResource.innerArea size
        (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  exact (canonicalPinnedTriangleWitness size_at_least_three tangent_positive
    tangent_lt).innerArea_lower_bound tangent_positive (by linarith)

lemma pinnedCutMissingLength_lt_tenth
    {tangentHalfAngle : ℝ}
    (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    pinnedCutMissingLength tangentHalfAngle < 1 / 10 := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have sqrt_fifth_sq : (Real.sqrt (1 / 5)) ^ 2 = 1 / 5 :=
    Real.sq_sqrt (by norm_num)
  have sqrt_fifth_gt : 11 / 25 < Real.sqrt (1 / 5) := by nlinarith
  have tangent_lt_upper : tangentHalfAngle < 14 / 25 := by linarith
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  let scaledTangent := 25 * tangentHalfAngle / 14
  have scaled_nonnegative : 0 ≤ scaledTangent := by
    dsimp [scaledTangent]
    positivity
  have scaled_lt_one : scaledTangent < 1 := by
    dsimp [scaledTangent]
    linarith
  have polynomial_identity :
      1 - 18 * tangentHalfAngle ^ 2 + 40 * tangentHalfAngle ^ 3 -
          19 * tangentHalfAngle ^ 4 =
        (1 - scaledTangent) ^ 5 +
          5 * scaledTangent * (1 - scaledTangent) ^ 4 +
          (1361 / 3125 : ℝ) * 10 * scaledTangent ^ 2 *
            (1 - scaledTangent) ^ 3 +
          (141 / 15625 : ℝ) * 10 * scaledTangent ^ 3 *
            (1 - scaledTangent) ^ 2 +
          (96221 / 1953125 : ℝ) * 5 * scaledTangent ^ 4 *
            (1 - scaledTangent) +
          (199721 / 390625 : ℝ) * scaledTangent ^ 5 := by
    dsimp [scaledTangent]
    ring
  have polynomial_positive :
      0 < 1 - 18 * tangentHalfAngle ^ 2 + 40 * tangentHalfAngle ^ 3 -
        19 * tangentHalfAngle ^ 4 := by
    rw [polynomial_identity]
    positivity
  have one_minus_tangent_sq_positive : 0 < 1 - tangentHalfAngle ^ 2 := by
    nlinarith
  have denominator_positive : 0 < (1 - tangentHalfAngle ^ 2) ^ 2 := by
    positivity
  have difference_identity :
      1 / 10 - pinnedCutMissingLength tangentHalfAngle =
        (1 - 18 * tangentHalfAngle ^ 2 + 40 * tangentHalfAngle ^ 3 -
          19 * tangentHalfAngle ^ 4) /
            (10 * (1 - tangentHalfAngle ^ 2) ^ 2) := by
    dsimp [pinnedCutMissingLength]
    field_simp [ne_of_gt (sub_pos.mpr (by nlinarith : tangentHalfAngle ^ 2 < 1))]
    ring
  rw [← sub_pos, difference_identity]
  positivity

noncomputable def pinnedPointOneCoordinates (frame : Frame) : Plane :=
  ![1 / 2 - frame.cosine,
    pinnedEdgeParameter frame + frame.sine - 1 / 2]

lemma pinned_point_one_eq
    (frame : Frame) (cosine_nonzero : frame.cosine ≠ 0) :
    (pinnedSquare frame).transform (pinnedPointOneCoordinates frame) =
      ![(1 : ℝ), 9 / 10] := by
  funext coordinate
  fin_cases coordinate
  · simp [pinnedSquare_transform, pinnedNegativeVertex,
      pinnedPointOneCoordinates, pinnedEdgeParameter,
      Frame.rotation_apply_zero]
    field_simp [cosine_nonzero]
    linear_combination -20 * frame.cosine * frame.unit
  · simp [pinnedSquare_transform, pinnedNegativeVertex,
      pinnedPointOneCoordinates, pinnedEdgeParameter,
      Frame.rotation_apply_one]
    field_simp [cosine_nonzero]
    ring_nf

lemma canonicalPinned_point_one_local_vertical_margin
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    1 - (pinnedEdgeParameter (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).sine) =
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine *
        (1 / 10 - pinnedCutMissingLength tangentHalfAngle) := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have denominator_ne : 1 + tangentHalfAngle ^ 2 ≠ 0 := by positivity
  have one_minus_tangent_sq_ne : 1 - tangentHalfAngle ^ 2 ≠ 0 := by
    nlinarith
  simp [pinnedEdgeParameter, pinnedCutMissingLength]
  field_simp [denominator_ne, one_minus_tangent_sq_ne]
  ring

lemma canonicalPinned_point_one_coordinates_mem
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    pinnedPointOneCoordinates (Frame.ofTangentHalfAngle tangentHalfAngle) ∈
      unitSquareInterior := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have denominator_positive : 0 < 1 + tangentHalfAngle ^ 2 := by positivity
  have cosine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) denominator_positive
  have cosine_lt_one :
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine < 1 := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    rw [div_lt_one denominator_positive]
    nlinarith
  have missing_nonnegative :
      0 ≤ pinnedCutMissingLength tangentHalfAngle := by
    dsimp [pinnedCutMissingLength]
    have numerator_positive := pinnedMissingNumerator_positive
      tangent_positive tangent_lt
    positivity
  have missing_lt_tenth := pinnedCutMissingLength_lt_tenth
    tangent_positive tangent_lt
  have vertical_margin_positive :
      0 < 1 - (pinnedEdgeParameter
          (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).sine) := by
    rw [canonicalPinned_point_one_local_vertical_margin tangent_positive
      tangent_lt]
    positivity
  have vertical_margin_lt_one :
      1 - (pinnedEdgeParameter
          (Frame.ofTangentHalfAngle tangentHalfAngle) +
        (Frame.ofTangentHalfAngle tangentHalfAngle).sine) < 1 := by
    rw [canonicalPinned_point_one_local_vertical_margin tangent_positive
      tangent_lt]
    have cosine_at_most_one :
        (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ≤ 1 :=
      cosine_lt_one.le
    have tenth_sub_missing_at_most_one :
        1 / 10 - pinnedCutMissingLength tangentHalfAngle ≤ 1 := by
      linarith
    nlinarith
  intro coordinate _
  fin_cases coordinate
  · change -(1 / 2) < 1 / 2 -
        (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ∧
      1 / 2 - (Frame.ofTangentHalfAngle tangentHalfAngle).cosine < 1 / 2
    constructor <;> linarith
  · change -(1 / 2) <
        pinnedEdgeParameter (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).sine - 1 / 2 ∧
      pinnedEdgeParameter (Frame.ofTangentHalfAngle tangentHalfAngle) +
          (Frame.ofTangentHalfAngle tangentHalfAngle).sine - 1 / 2 < 1 / 2
    constructor <;> linarith

lemma canonicalPinned_point_one_mem
    {tangentHalfAngle : ℝ} (tangent_positive : 0 < tangentHalfAngle)
    (tangent_lt : tangentHalfAngle < 1 - Real.sqrt (1 / 5)) :
    ![(1 : ℝ), 9 / 10] ∈
      (canonicalPinnedSquare tangentHalfAngle).interiorRegion := by
  have sqrt_fifth_nonnegative : 0 ≤ Real.sqrt (1 / 5) := Real.sqrt_nonneg _
  have tangent_lt_one : tangentHalfAngle < 1 := by linarith
  have cosine_positive :
      0 < (Frame.ofTangentHalfAngle tangentHalfAngle).cosine := by
    simp only [Frame.ofTangentHalfAngle_cosine]
    exact div_pos (by nlinarith) (by positivity)
  have cosine_nonzero :
      (Frame.ofTangentHalfAngle tangentHalfAngle).cosine ≠ 0 :=
    cosine_positive.ne'
  refine ⟨pinnedPointOneCoordinates
    (Frame.ofTangentHalfAngle tangentHalfAngle),
    canonicalPinned_point_one_coordinates_mem tangent_positive tangent_lt, ?_⟩
  exact pinned_point_one_eq _ cosine_nonzero

end SquarePackingArchive.Nagamochi
