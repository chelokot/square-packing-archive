import SquarePackingArchive.NagamochiCutSymmetry

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma measurable_swapPlane : Measurable Plane.swap := by
  unfold Plane.swap
  fun_prop

lemma measurable_reflectYPlane (coordinateSum : ℝ) :
    Measurable (Plane.reflectY coordinateSum) := by
  unfold Plane.reflectY
  fun_prop

lemma measurePreserving_reflectYPlane (coordinateSum : ℝ) :
    MeasurePreserving (Plane.reflectY coordinateSum) volume volume := by
  let componentMap : Fin 2 → ℝ → ℝ := ![id, fun value => coordinateSum - value]
  have components_preserving :
      ∀ coordinate, MeasurePreserving (componentMap coordinate) volume volume := by
    intro coordinate
    fin_cases coordinate
    · exact MeasurePreserving.id volume
    · exact volume.measurePreserving_sub_left coordinateSum
  convert volume_preserving_pi components_preserving using 1 <;> try rfl
  funext point coordinate
  fin_cases coordinate <;> simp [Plane.reflectY, componentMap]

lemma horizontalSegmentMeasure_preimage_swap
    (left right height : ℝ) {region : Set Plane} (region_measurable : MeasurableSet region) :
    horizontalSegmentMeasure left right height (Plane.swap ⁻¹' region) =
      verticalSegmentMeasure left right height region := by
  rw [horizontalSegmentMeasure_apply (region_measurable.preimage measurable_swapPlane),
    verticalSegmentMeasure_apply region_measurable]
  congr 1

lemma verticalSegmentMeasure_preimage_swap
    (bottom top horizontal : ℝ) {region : Set Plane} (region_measurable : MeasurableSet region) :
    verticalSegmentMeasure bottom top horizontal (Plane.swap ⁻¹' region) =
      horizontalSegmentMeasure bottom top horizontal region := by
  rw [verticalSegmentMeasure_apply (region_measurable.preimage measurable_swapPlane),
    horizontalSegmentMeasure_apply region_measurable]
  congr 1

lemma innerArea_preimage_swap (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.innerArea size (Plane.swap ⁻¹' region) =
      NagamochiResource.innerArea size region := by
  rw [NagamochiResource.innerArea,
    Measure.restrict_apply (region_measurable.preimage measurable_swapPlane),
    Measure.restrict_apply region_measurable]
  have preimage_identity :
      Plane.swap ⁻¹' (region ∩ Icc (fun _ => (1 : ℝ)) (fun _ => (size : ℝ) - 1)) =
        Plane.swap ⁻¹' region ∩ Icc (fun _ => (1 : ℝ)) (fun _ => (size : ℝ) - 1) := by
    ext point
    simp [Plane.swap, Pi.le_def, Fin.forall_fin_two, and_assoc, and_left_comm, and_comm]
  rw [← preimage_identity]
  exact measurePreserving_swapPlane.measure_preimage
    (region_measurable.inter measurableSet_Icc).nullMeasurableSet

lemma boundaryLines_preimage_swap (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.boundaryLines size (Plane.swap ⁻¹' region) =
      NagamochiResource.boundaryLines size region := by
  classical
  simp [NagamochiResource.boundaryLines, NagamochiResource.boundarySides,
    NagamochiResource.boundaryLine, Measure.smul_apply, Measure.add_apply,
    horizontalSegmentMeasure_preimage_swap _ _ _ region_measurable,
    verticalSegmentMeasure_preimage_swap _ _ _ region_measurable,
    add_comm, add_left_comm, add_assoc]

lemma cornerPoints_preimage_swap (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.cornerPoints size (Plane.swap ⁻¹' region) =
      NagamochiResource.cornerPoints size region := by
  classical
  simp [NagamochiResource.cornerPoints, NagamochiResource.cornerPointKinds,
    NagamochiResource.cornerPoint, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ region_measurable,
    Measure.dirac_apply' _ (region_measurable.preimage measurable_swapPlane),
    Set.indicator_apply, Plane.swap]
  ac_rfl

lemma edgePointCluster_preimage_swap (size coordinate : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.edgePointCluster size coordinate (Plane.swap ⁻¹' region) =
      NagamochiResource.edgePointCluster size coordinate region := by
  classical
  simp [NagamochiResource.edgePointCluster, NagamochiResource.edgePointKinds,
    NagamochiResource.edgePoint, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ region_measurable,
    Measure.dirac_apply' _ (region_measurable.preimage measurable_swapPlane),
    Set.indicator_apply, Plane.swap]
  ac_rfl

lemma edgePoints_preimage_swap (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.edgePoints size (Plane.swap ⁻¹' region) =
      NagamochiResource.edgePoints size region := by
  simp only [NagamochiResource.edgePoints, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro coordinate coordinate_mem
  exact edgePointCluster_preimage_swap size coordinate region_measurable

lemma resourceMeasure_preimage_swap (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.measure size (Plane.swap ⁻¹' region) =
      NagamochiResource.measure size region := by
  simp only [NagamochiResource.measure, Measure.add_apply,
    innerArea_preimage_swap size region_measurable,
    boundaryLines_preimage_swap size region_measurable,
    cornerPoints_preimage_swap size region_measurable,
    edgePoints_preimage_swap size region_measurable]

lemma horizontalSegmentMeasure_preimage_reflectY
    (left right height coordinateSum : ℝ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    horizontalSegmentMeasure left right height (Plane.reflectY coordinateSum ⁻¹' region) =
      horizontalSegmentMeasure left right (coordinateSum - height) region := by
  rw [horizontalSegmentMeasure_apply
      (region_measurable.preimage (measurable_reflectYPlane coordinateSum)),
    horizontalSegmentMeasure_apply region_measurable]
  congr 1

lemma verticalSegmentMeasure_preimage_reflectY
    (offset coordinateSum horizontal : ℝ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    verticalSegmentMeasure offset (coordinateSum - offset) horizontal
        (Plane.reflectY coordinateSum ⁻¹' region) =
      verticalSegmentMeasure offset (coordinateSum - offset) horizontal region := by
  rw [verticalSegmentMeasure_apply
      (region_measurable.preimage (measurable_reflectYPlane coordinateSum)),
    verticalSegmentMeasure_apply region_measurable]
  have interval_identity :
      (fun coordinate : ℝ => coordinateSum - coordinate) ⁻¹'
          Icc offset (coordinateSum - offset) = Icc offset (coordinateSum - offset) := by
    ext coordinate
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨lower, upper⟩ <;> constructor <;> linarith
  have parametrization_measurable :
      Measurable (fun coordinate : ℝ => ![horizontal, coordinate]) := by fun_prop
  have preserved := (volume.measurePreserving_sub_left coordinateSum).measure_preimage
    (s := Icc offset (coordinateSum - offset) ∩
      (fun coordinate : ℝ => ![horizontal, coordinate]) ⁻¹' region)
    (measurableSet_Icc.inter (region_measurable.preimage parametrization_measurable)).nullMeasurableSet
  rw [preimage_inter, interval_identity] at preserved
  exact preserved

lemma innerArea_preimage_reflectY (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.innerArea size (Plane.reflectY size ⁻¹' region) =
      NagamochiResource.innerArea size region := by
  rw [NagamochiResource.innerArea,
    Measure.restrict_apply (region_measurable.preimage (measurable_reflectYPlane size)),
    Measure.restrict_apply region_measurable]
  have inner_identity :
      Plane.reflectY size ⁻¹' Icc (fun _ => (1 : ℝ)) (fun _ => (size : ℝ) - 1) =
        Icc (fun _ => (1 : ℝ)) (fun _ => (size : ℝ) - 1) := by
    ext point
    simp only [mem_preimage, mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Plane.reflectY, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;>
      rintro ⟨⟨horizontal_lower, vertical_lower⟩, ⟨horizontal_upper, vertical_upper⟩⟩ <;>
      constructor <;> constructor <;> linarith
  have preserved := (measurePreserving_reflectYPlane size).measure_preimage
    (s := region ∩ Icc (fun _ => (1 : ℝ)) (fun _ => (size : ℝ) - 1))
    (region_measurable.inter measurableSet_Icc).nullMeasurableSet
  rw [preimage_inter, inner_identity] at preserved
  exact preserved

lemma boundaryLines_preimage_reflectY (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.boundaryLines size (Plane.reflectY size ⁻¹' region) =
      NagamochiResource.boundaryLines size region := by
  classical
  simp [NagamochiResource.boundaryLines, NagamochiResource.boundarySides,
    NagamochiResource.boundaryLine, Measure.smul_apply, Measure.add_apply,
    horizontalSegmentMeasure_preimage_reflectY _ _ _ _ region_measurable,
    verticalSegmentMeasure_preimage_reflectY _ _ _ region_measurable]
  ac_rfl

lemma cornerPoints_preimage_reflectY (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.cornerPoints size (Plane.reflectY size ⁻¹' region) =
      NagamochiResource.cornerPoints size region := by
  classical
  simp [NagamochiResource.cornerPoints, NagamochiResource.cornerPointKinds,
    NagamochiResource.cornerPoint, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ region_measurable,
    Measure.dirac_apply' _ (region_measurable.preimage (measurable_reflectYPlane size)),
    Set.indicator_apply, Plane.reflectY]
  ac_rfl

lemma sum_edgeCoordinates_reflect (size : ℕ) (contribution : ℕ → ENNReal) :
    ∑ coordinate ∈ Finset.Icc 2 (size - 2), contribution (size - coordinate) =
      ∑ coordinate ∈ Finset.Icc 2 (size - 2), contribution coordinate := by
  apply Finset.sum_bij (fun coordinate _ => size - coordinate)
  · intro coordinate coordinate_mem
    simp only [Finset.mem_Icc] at coordinate_mem ⊢
    omega
  · intro first first_mem second second_mem reflected_eq
    simp only [Finset.mem_Icc] at first_mem second_mem
    omega
  · intro coordinate coordinate_mem
    refine ⟨size - coordinate, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at coordinate_mem ⊢
      omega
    · simp only [Finset.mem_Icc] at coordinate_mem
      omega
  · intro coordinate coordinate_mem
    rfl

lemma edgePoints_apply_eq (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.edgePoints size region = (1 / 2 : ENNReal) *
      ((∑ coordinate ∈ Finset.Icc 2 (size - 2),
          region.indicator 1 ![(coordinate : ℝ), (9 / 10 : ℝ)]) +
        (∑ coordinate ∈ Finset.Icc 2 (size - 2),
          region.indicator 1 ![(coordinate : ℝ), (size : ℝ) - 9 / 10]) +
        (∑ coordinate ∈ Finset.Icc 2 (size - 2),
          region.indicator 1 ![(9 / 10 : ℝ), (coordinate : ℝ)]) +
        (∑ coordinate ∈ Finset.Icc 2 (size - 2),
          region.indicator 1 ![(size : ℝ) - 9 / 10, (coordinate : ℝ)])) := by
  classical
  simp [NagamochiResource.edgePoints, NagamochiResource.edgePointCluster,
    NagamochiResource.edgePointKinds, NagamochiResource.edgePoint,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ region_measurable, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, add_assoc]

lemma sum_edgePoints_reflect_coordinate (size : ℕ) (horizontal : ℝ)
    (region : Set Plane) :
    ∑ coordinate ∈ Finset.Icc 2 (size - 2),
        region.indicator (1 : Plane → ENNReal)
          ![horizontal, (size : ℝ) - (coordinate : ℝ)] =
      ∑ coordinate ∈ Finset.Icc 2 (size - 2),
        region.indicator 1 ![horizontal, (coordinate : ℝ)] := by
  rw [← sum_edgeCoordinates_reflect size
    (fun coordinate => region.indicator 1 ![horizontal, (coordinate : ℝ)])]
  apply Finset.sum_congr rfl
  intro coordinate coordinate_mem
  have coordinate_le : coordinate ≤ size := by
    have bounds := Finset.mem_Icc.mp coordinate_mem
    omega
  rw [Nat.cast_sub coordinate_le]

lemma edgePoints_preimage_reflectY (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.edgePoints size (Plane.reflectY size ⁻¹' region) =
      NagamochiResource.edgePoints size region := by
  rw [edgePoints_apply_eq size
    (region_measurable.preimage (measurable_reflectYPlane size)),
    edgePoints_apply_eq size region_measurable]
  have indicator_identity (horizontal vertical : ℝ) :
      (Plane.reflectY size ⁻¹' region).indicator (1 : Plane → ENNReal)
          ![horizontal, vertical] =
        region.indicator 1 ![horizontal, (size : ℝ) - vertical] := by
    rfl
  simp only [indicator_identity, sub_sub_cancel,
    sum_edgePoints_reflect_coordinate]
  ac_rfl

lemma resourceMeasure_preimage_reflectY (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.measure size (Plane.reflectY size ⁻¹' region) =
      NagamochiResource.measure size region := by
  simp only [NagamochiResource.measure, Measure.add_apply,
    innerArea_preimage_reflectY size region_measurable,
    boundaryLines_preimage_reflectY size region_measurable,
    cornerPoints_preimage_reflectY size region_measurable,
    edgePoints_preimage_reflectY size region_measurable]

lemma preimage_reflectX_eq (coordinateSum : ℝ) (region : Set Plane) :
    Plane.reflectX coordinateSum ⁻¹' region =
      Plane.swap ⁻¹' (Plane.reflectY coordinateSum ⁻¹' (Plane.swap ⁻¹' region)) := by
  rfl

lemma cornerPoints_preimage_reflectX (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.cornerPoints size (Plane.reflectX size ⁻¹' region) =
      NagamochiResource.cornerPoints size region := by
  rw [preimage_reflectX_eq,
    cornerPoints_preimage_swap size
      ((region_measurable.preimage measurable_swapPlane).preimage (measurable_reflectYPlane size)),
    cornerPoints_preimage_reflectY size (region_measurable.preimage measurable_swapPlane),
    cornerPoints_preimage_swap size region_measurable]

lemma resourceMeasure_preimage_reflectX (size : ℕ) {region : Set Plane}
    (region_measurable : MeasurableSet region) :
    NagamochiResource.measure size (Plane.reflectX size ⁻¹' region) =
      NagamochiResource.measure size region := by
  rw [preimage_reflectX_eq,
    resourceMeasure_preimage_swap size
      ((region_measurable.preimage measurable_swapPlane).preimage (measurable_reflectYPlane size)),
    resourceMeasure_preimage_reflectY size (region_measurable.preimage measurable_swapPlane),
    resourceMeasure_preimage_swap size region_measurable]

end SquarePackingArchive.Nagamochi
