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

noncomputable def weightedPointMeasure
    (weight : ENNReal) (point : Plane) : Measure Plane :=
  weight • Measure.dirac point

lemma weightedPointMeasure_univ (weight : ENNReal) (point : Plane) :
    weightedPointMeasure weight point univ = weight := by
  simp [weightedPointMeasure]

noncomputable def NagamochiResource.innerArea (size : ℕ) : Measure Plane :=
  volume.restrict (Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))

noncomputable def NagamochiResource.boundaryLines (size : ℕ) : Measure Plane :=
  (1 / 2 : ENNReal) •
    (horizontalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) 1 +
      horizontalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) ((size : ℝ) - 1) +
        verticalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) 1 +
          verticalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10) ((size : ℝ) - 1))

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
  simp only [NagamochiResource.boundaryLines, Measure.smul_apply,
    Measure.coe_add, Pi.add_apply, horizontalSegmentMeasure_univ,
    verticalSegmentMeasure_univ]
  norm_num
  have segment_eq : (size : ℝ) - 9 / 10 - 9 / 10 = (size : ℝ) - 9 / 5 := by ring
  rw [segment_eq]
  calc
    (2 : ENNReal)⁻¹ *
        (ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5) +
          ENNReal.ofReal ((size : ℝ) - 9 / 5)) =
        ((2 : ENNReal)⁻¹ * 4) *
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

end SquarePackingArchive
