import SquarePackingArchive.Resource

namespace SquarePackingArchive

open MeasureTheory Set

noncomputable def horizontalSegmentMeasure
    (left right height : ℝ) : Measure Plane :=
  Measure.map (fun coordinate : ℝ => ![coordinate, height])
    (volume.restrict (Icc left right))

noncomputable def verticalSegmentMeasure
    (bottom top horizontal : ℝ) : Measure Plane :=
  Measure.map (fun coordinate : ℝ => ![horizontal, coordinate])
    (volume.restrict (Icc bottom top))

lemma horizontalSegmentMeasure_univ (left right height : ℝ) :
    horizontalSegmentMeasure left right height univ =
      ENNReal.ofReal (right - left) := by
  rw [horizontalSegmentMeasure, Measure.map_apply]
  · simp [Real.volume_Icc]
  · fun_prop
  · exact MeasurableSet.univ

lemma verticalSegmentMeasure_univ (bottom top horizontal : ℝ) :
    verticalSegmentMeasure bottom top horizontal univ =
      ENNReal.ofReal (top - bottom) := by
  rw [verticalSegmentMeasure, Measure.map_apply]
  · simp [Real.volume_Icc]
  · fun_prop
  · exact MeasurableSet.univ

lemma horizontalSegmentMeasure_apply
    {left right height : ℝ} {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    horizontalSegmentMeasure left right height region =
      volume (Icc left right ∩
        (fun coordinate : ℝ => ![coordinate, height]) ⁻¹' region) := by
  have parametrization_measurable :
      Measurable (fun coordinate : ℝ => ![coordinate, height]) := by fun_prop
  rw [horizontalSegmentMeasure,
    Measure.map_apply parametrization_measurable region_measurable,
    Measure.restrict_apply (region_measurable.preimage parametrization_measurable),
    inter_comm]

lemma verticalSegmentMeasure_apply
    {bottom top horizontal : ℝ} {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    verticalSegmentMeasure bottom top horizontal region =
      volume (Icc bottom top ∩
        (fun coordinate : ℝ => ![horizontal, coordinate]) ⁻¹' region) := by
  have parametrization_measurable :
      Measurable (fun coordinate : ℝ => ![horizontal, coordinate]) := by fun_prop
  rw [verticalSegmentMeasure,
    Measure.map_apply parametrization_measurable region_measurable,
    Measure.restrict_apply (region_measurable.preimage parametrization_measurable),
    inter_comm]

lemma horizontalSegmentMeasure_lower_bound
    {left right height chordStart chordEnd : ℝ} {region : Set Plane}
    (region_measurable : MeasurableSet region)
    (chord_inside_segment : Ioo chordStart chordEnd ⊆ Icc left right)
    (chord_inside_region :
      ∀ coordinate ∈ Ioo chordStart chordEnd, ![coordinate, height] ∈ region) :
    ENNReal.ofReal (chordEnd - chordStart) ≤
      horizontalSegmentMeasure left right height region := by
  rw [horizontalSegmentMeasure_apply region_measurable]
  rw [← Real.volume_Ioo]
  apply measure_mono
  intro coordinate coordinate_mem
  exact ⟨chord_inside_segment coordinate_mem,
    chord_inside_region coordinate coordinate_mem⟩

lemma verticalSegmentMeasure_lower_bound
    {bottom top horizontal chordStart chordEnd : ℝ} {region : Set Plane}
    (region_measurable : MeasurableSet region)
    (chord_inside_segment : Ioo chordStart chordEnd ⊆ Icc bottom top)
    (chord_inside_region :
      ∀ coordinate ∈ Ioo chordStart chordEnd, ![horizontal, coordinate] ∈ region) :
    ENNReal.ofReal (chordEnd - chordStart) ≤
      verticalSegmentMeasure bottom top horizontal region := by
  rw [verticalSegmentMeasure_apply region_measurable]
  rw [← Real.volume_Ioo]
  apply measure_mono
  intro coordinate coordinate_mem
  exact ⟨chord_inside_segment coordinate_mem,
    chord_inside_region coordinate coordinate_mem⟩

noncomputable def weightedPointMeasure
    (weight : ENNReal) (point : Plane) : Measure Plane :=
  weight • Measure.dirac point

lemma weightedPointMeasure_univ (weight : ENNReal) (point : Plane) :
    weightedPointMeasure weight point univ = weight := by
  simp [weightedPointMeasure]

lemma weightedPointMeasure_apply
    {weight : ENNReal} {point : Plane} {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    weightedPointMeasure weight point region =
      region.indicator (fun _ => weight) point := by
  by_cases point_mem : point ∈ region <;>
    simp [weightedPointMeasure, Measure.smul_apply,
      Measure.dirac_apply' point region_measurable, point_mem]

noncomputable def NagamochiResource.innerArea (size : ℕ) : Measure Plane :=
  volume.restrict (Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))

inductive NagamochiResource.BoundarySide
  | bottom
  | top
  | left
  | right
  deriving DecidableEq

def NagamochiResource.boundarySides :
    Finset NagamochiResource.BoundarySide :=
  {.bottom, .top, .left, .right}

lemma NagamochiResource.mem_boundarySides
    (side : NagamochiResource.BoundarySide) :
    side ∈ NagamochiResource.boundarySides := by
  cases side <;> simp [NagamochiResource.boundarySides]

noncomputable def NagamochiResource.boundaryLine
    (size : ℕ) : NagamochiResource.BoundarySide → Measure Plane
  | .bottom => horizontalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) 1
  | .top =>
      horizontalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) ((size : ℝ) - 1)
  | .left => verticalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) 1
  | .right =>
      verticalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) ((size : ℝ) - 1)

def NagamochiResource.HasBoundaryChord
    (size : ℕ) (side : NagamochiResource.BoundarySide)
    (region : Set Plane) (minimumLength : ℝ) : Prop :=
  match side with
  | .bottom =>
      ∃ chordStart chordEnd,
        minimumLength ≤ chordEnd - chordStart ∧
          Ioo chordStart chordEnd ⊆ Icc (9 / 10) ((size : ℝ) - 9 / 10) ∧
            ∀ coordinate ∈ Ioo chordStart chordEnd, ![coordinate, 1] ∈ region
  | .top =>
      ∃ chordStart chordEnd,
        minimumLength ≤ chordEnd - chordStart ∧
          Ioo chordStart chordEnd ⊆ Icc (9 / 10) ((size : ℝ) - 9 / 10) ∧
            ∀ coordinate ∈ Ioo chordStart chordEnd,
              ![coordinate, (size : ℝ) - 1] ∈ region
  | .left =>
      ∃ chordStart chordEnd,
        minimumLength ≤ chordEnd - chordStart ∧
          Ioo chordStart chordEnd ⊆ Icc (9 / 10) ((size : ℝ) - 9 / 10) ∧
            ∀ coordinate ∈ Ioo chordStart chordEnd, ![1, coordinate] ∈ region
  | .right =>
      ∃ chordStart chordEnd,
        minimumLength ≤ chordEnd - chordStart ∧
          Ioo chordStart chordEnd ⊆ Icc (9 / 10) ((size : ℝ) - 9 / 10) ∧
            ∀ coordinate ∈ Ioo chordStart chordEnd,
              ![(size : ℝ) - 1, coordinate] ∈ region

lemma NagamochiResource.HasBoundaryChord.mono
    {size : ℕ} {side : NagamochiResource.BoundarySide}
    {region : Set Plane} {longerLength shorterLength : ℝ}
    (chord : NagamochiResource.HasBoundaryChord size side region longerLength)
    (length_le : shorterLength ≤ longerLength) :
    NagamochiResource.HasBoundaryChord size side region shorterLength := by
  cases side <;>
    rcases chord with
      ⟨chordStart, chordEnd, chord_length, inside_segment, inside_region⟩ <;>
    exact ⟨chordStart, chordEnd, length_le.trans chord_length,
      inside_segment, inside_region⟩

noncomputable def NagamochiResource.boundaryLines (size : ℕ) : Measure Plane :=
  (1 / 2 : ENNReal) •
    ∑ side ∈ NagamochiResource.boundarySides,
      NagamochiResource.boundaryLine size side

noncomputable def NagamochiResource.cornerPoints (size : ℕ) : Measure Plane :=
  (9 / 20 : ENNReal) •
    (Measure.dirac ![(9 / 10 : ℝ), 1] +
      Measure.dirac ![(size : ℝ) - 9 / 10, 1] +
        Measure.dirac ![(9 / 10 : ℝ), (size : ℝ) - 1] +
          Measure.dirac ![(size : ℝ) - 9 / 10, (size : ℝ) - 1] +
            Measure.dirac ![1, (9 / 10 : ℝ)] +
              Measure.dirac ![1, (size : ℝ) - 9 / 10] +
                Measure.dirac ![(size : ℝ) - 1, (9 / 10 : ℝ)] +
                  Measure.dirac ![(size : ℝ) - 1, (size : ℝ) - 9 / 10])

noncomputable def NagamochiResource.edgePointCluster
    (size coordinate : ℕ) : Measure Plane :=
  (1 / 2 : ENNReal) •
    (Measure.dirac ![(coordinate : ℝ), (9 / 10 : ℝ)] +
      Measure.dirac ![(coordinate : ℝ), (size : ℝ) - 9 / 10] +
        Measure.dirac ![(9 / 10 : ℝ), (coordinate : ℝ)] +
          Measure.dirac ![(size : ℝ) - 9 / 10, (coordinate : ℝ)])

noncomputable def NagamochiResource.edgePoints (size : ℕ) : Measure Plane :=
  ∑ coordinate ∈ Finset.Icc 2 (size - 2),
    NagamochiResource.edgePointCluster size coordinate

noncomputable def NagamochiResource.measure (size : ℕ) : Measure Plane :=
  NagamochiResource.innerArea size +
    NagamochiResource.boundaryLines size +
      NagamochiResource.cornerPoints size +
        NagamochiResource.edgePoints size

lemma NagamochiResource.innerArea_univ
    {size : ℕ} (size_at_least_two : 2 ≤ size) :
    NagamochiResource.innerArea size univ =
      ENNReal.ofReal (((size : ℝ) - 2) ^ 2) := by
  have difference_nonnegative : 0 ≤ (size : ℝ) - 2 := by
    have size_real : (2 : ℝ) ≤ size := by exact_mod_cast size_at_least_two
    linarith
  rw [NagamochiResource.innerArea, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter]
  rw [Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two]
  have difference_eq : (size : ℝ) - 1 - 1 = (size : ℝ) - 2 := by ring
  rw [difference_eq]
  rw [← pow_two]
  rw [← ENNReal.ofReal_pow difference_nonnegative 2]

lemma NagamochiResource.boundaryLines_univ
    {size : ℕ} (size_at_least_two : 2 ≤ size) :
    NagamochiResource.boundaryLines size univ =
      ENNReal.ofReal (2 * (size : ℝ) - 18 / 5) := by
  have segment_nonnegative : 0 ≤ (size : ℝ) - 9 / 5 := by
    have size_real : (2 : ℝ) ≤ size := by exact_mod_cast size_at_least_two
    linarith
  simp [NagamochiResource.boundaryLines, NagamochiResource.boundarySides,
    NagamochiResource.boundaryLine, horizontalSegmentMeasure_univ,
    verticalSegmentMeasure_univ]
  norm_num
  have segment_eq : (size : ℝ) - 9 / 10 - 9 / 10 = (size : ℝ) - 9 / 5 := by ring
  rw [segment_eq]
  calc
    (2 : ENNReal)⁻¹ * ENNReal.ofReal ((size : ℝ) - 9 / 5) +
        ((2 : ENNReal)⁻¹ * ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ((2 : ENNReal)⁻¹ * ENNReal.ofReal ((size : ℝ) - 9 / 5) +
            (2 : ENNReal)⁻¹ * ENNReal.ofReal ((size : ℝ) - 9 / 5))) =
      (2 : ENNReal)⁻¹ *
        (ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5)) := by ring
    _ = ((2 : ENNReal)⁻¹ * 4) *
        ENNReal.ofReal ((size : ℝ) - 9 / 5) := by ring
    _ = 2 * ENNReal.ofReal ((size : ℝ) - 9 / 5) := by
      have half_times_two : (2 : ENNReal)⁻¹ * 2 = 1 := by
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      rw [show (4 : ENNReal) = 2 + 2 by norm_num, mul_add, half_times_two]
      norm_num
    _ = ENNReal.ofReal (2 * ((size : ℝ) - 9 / 5)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ = ENNReal.ofReal (2 * (size : ℝ) - 18 / 5) := by
      congr 2
      ring

lemma NagamochiResource.boundaryLine_lower_bound_of_chord
    {size : ℕ} {side : NagamochiResource.BoundarySide}
    {region : Set Plane} {minimumLength : ℝ}
    (region_measurable : MeasurableSet region)
    (chord : NagamochiResource.HasBoundaryChord size side region minimumLength) :
    ENNReal.ofReal minimumLength ≤
      NagamochiResource.boundaryLine size side region := by
  cases side with
  | bottom =>
      rcases chord with
        ⟨chordStart, chordEnd, length_bound, inside_segment, inside_region⟩
      exact (ENNReal.ofReal_le_ofReal length_bound).trans
        (horizontalSegmentMeasure_lower_bound region_measurable
          inside_segment inside_region)
  | top =>
      rcases chord with
        ⟨chordStart, chordEnd, length_bound, inside_segment, inside_region⟩
      exact (ENNReal.ofReal_le_ofReal length_bound).trans
        (horizontalSegmentMeasure_lower_bound region_measurable
          inside_segment inside_region)
  | left =>
      rcases chord with
        ⟨chordStart, chordEnd, length_bound, inside_segment, inside_region⟩
      exact (ENNReal.ofReal_le_ofReal length_bound).trans
        (verticalSegmentMeasure_lower_bound region_measurable
          inside_segment inside_region)
  | right =>
      rcases chord with
        ⟨chordStart, chordEnd, length_bound, inside_segment, inside_region⟩
      exact (ENNReal.ofReal_le_ofReal length_bound).trans
        (verticalSegmentMeasure_lower_bound region_measurable
          inside_segment inside_region)

lemma NagamochiResource.boundaryLine_le_boundaryLines
    (size : ℕ) (side : NagamochiResource.BoundarySide) (region : Set Plane) :
    (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size side region ≤
      NagamochiResource.boundaryLines size region := by
  simp only [NagamochiResource.boundaryLines, Measure.smul_apply]
  have component_le :
      NagamochiResource.boundaryLine size side region ≤
        ∑ otherSide ∈ NagamochiResource.boundarySides,
          NagamochiResource.boundaryLine size otherSide region :=
    Finset.single_le_sum
      (f := fun otherSide => NagamochiResource.boundaryLine size otherSide region)
      (fun otherSide _ => bot_le)
      (NagamochiResource.mem_boundarySides side)
  exact mul_le_mul le_rfl component_le bot_le bot_le

lemma NagamochiResource.boundaryLines_lower_bound
    {size : ℕ} {side : NagamochiResource.BoundarySide}
    {region : Set Plane} {length : ENNReal}
    (line_length_lower_bound :
      length ≤ NagamochiResource.boundaryLine size side region) :
    (1 / 2 : ENNReal) * length ≤ NagamochiResource.boundaryLines size region := by
  exact (mul_le_mul le_rfl line_length_lower_bound bot_le bot_le).trans
    (NagamochiResource.boundaryLine_le_boundaryLines size side region)

lemma NagamochiResource.boundaryLines_subset_lower_bound
    {size : ℕ} {selectedSides : Finset NagamochiResource.BoundarySide}
    {region : Set Plane}
    (selected_sides_valid : selectedSides ⊆ NagamochiResource.boundarySides) :
    (1 / 2 : ENNReal) *
        (∑ side ∈ selectedSides, NagamochiResource.boundaryLine size side region) ≤
      NagamochiResource.boundaryLines size region := by
  simp only [NagamochiResource.boundaryLines, Measure.smul_apply]
  exact mul_le_mul le_rfl (Finset.sum_le_sum_of_subset selected_sides_valid) bot_le bot_le

lemma NagamochiResource.boundaryLines_le_measure
    (size : ℕ) (region : Set Plane) :
    NagamochiResource.boundaryLines size region ≤
      NagamochiResource.measure size region := by
  simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
  calc
    NagamochiResource.boundaryLines size region ≤
        NagamochiResource.innerArea size region +
          NagamochiResource.boundaryLines size region :=
      le_add_of_nonneg_left bot_le
    _ ≤ _ + NagamochiResource.cornerPoints size region :=
      le_add_of_nonneg_right bot_le
    _ ≤ _ + NagamochiResource.edgePoints size region :=
      le_add_of_nonneg_right bot_le

lemma NagamochiResource.cornerPoints_univ (size : ℕ) :
    NagamochiResource.cornerPoints size univ = 18 / 5 := by
  simp [NagamochiResource.cornerPoints]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  repeat' rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

lemma NagamochiResource.edgePointCluster_univ (size coordinate : ℕ) :
    NagamochiResource.edgePointCluster size coordinate univ = 2 := by
  simp [NagamochiResource.edgePointCluster]
  have half_times_two : (2 : ENNReal)⁻¹ * 2 = 1 := by
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ =
        (2 : ENNReal)⁻¹ * (1 + 1 + 1 + 1) := by ring
    _ =
        ((2 : ENNReal)⁻¹ * 2) * 2 := by ring
    _ = 2 := by rw [half_times_two, one_mul]

lemma NagamochiResource.edgePoints_univ (size : ℕ) :
    NagamochiResource.edgePoints size univ = (2 * (size - 3) : ℕ) := by
  simp [NagamochiResource.edgePoints,
    NagamochiResource.edgePointCluster_univ, Nat.card_Icc]
  rw [tsub_tsub]
  norm_num [mul_comm]

lemma NagamochiResource.measure_univ
    {size : ℕ} (size_at_least_three : 3 ≤ size) :
    NagamochiResource.measure size univ =
      ENNReal.ofReal ((size : ℝ) ^ 2 - 2) := by
  have size_at_least_two : 2 ≤ size := size_at_least_three.trans' (by omega)
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply]
  rw [NagamochiResource.innerArea_univ size_at_least_two,
    NagamochiResource.boundaryLines_univ size_at_least_two,
    NagamochiResource.cornerPoints_univ,
    NagamochiResource.edgePoints_univ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  repeat' rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal (sq_nonneg ((size : ℝ) - 2))]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * (size : ℝ) - 18 / 5)]
  rw [ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ (size : ℝ) ^ 2 - 2)]
  norm_num
  rw [Nat.cast_sub size_at_least_three]
  push_cast
  ring

lemma NagamochiResource.measure_univ_ne_top
    {size : ℕ} (size_at_least_three : 3 ≤ size) :
    NagamochiResource.measure size univ ≠ ⊤ := by
  rw [NagamochiResource.measure_univ size_at_least_three]
  finiteness

lemma NagamochiResource.measure_univ_nat
    {size : ℕ} (size_at_least_three : 3 ≤ size) :
    NagamochiResource.measure size univ = (size * size - 2 : ℕ) := by
  rw [NagamochiResource.measure_univ size_at_least_three]
  rw [← ENNReal.ofReal_natCast]
  congr 2
  rw [Nat.cast_sub]
  · push_cast
    ring
  · nlinarith

end SquarePackingArchive
