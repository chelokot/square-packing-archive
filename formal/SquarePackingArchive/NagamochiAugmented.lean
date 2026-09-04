import SquarePackingArchive.NagamochiAugmentedResource
import SquarePackingArchive.NagamochiResourceSymmetry

namespace SquarePackingArchive.NagamochiAugmentedResource

open MeasureTheory Set

lemma measure_preimage_swap (size : ℕ) {region : Set Plane}
    (measurable : MeasurableSet region) :
    measure size (Plane.swap ⁻¹' region) = measure size region := by
  simp [measure, cornerPoints, Nagamochi.innerArea_preimage_swap size measurable,
    Nagamochi.boundaryLines_preimage_swap size measurable,
    Nagamochi.cornerPoints_preimage_swap size measurable,
    Nagamochi.edgePoints_preimage_swap size measurable]

lemma measure_preimage_reflectY (size : ℕ) {region : Set Plane}
    (measurable : MeasurableSet region) :
    measure size (Plane.reflectY size ⁻¹' region) = measure size region := by
  simp [measure, cornerPoints, Nagamochi.innerArea_preimage_reflectY size measurable,
    Nagamochi.boundaryLines_preimage_reflectY size measurable,
    Nagamochi.cornerPoints_preimage_reflectY size measurable,
    Nagamochi.edgePoints_preimage_reflectY size measurable]

lemma score_swap (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    measure size (square.swap.dilatedInteriorRegion factor) =
      measure size (square.dilatedInteriorRegion factor) := by
  have region_eq : square.swap.dilatedInteriorRegion factor =
      Plane.swap ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa using square.mem_swap_dilatedInteriorRegion_iff factor_positive point.swap
  rw [region_eq]
  exact measure_preimage_swap size (square.measurableSet_dilatedInteriorRegion factor_positive.ne')

lemma score_reflectY (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    measure size ((square.reflectY (size / factor)).dilatedInteriorRegion factor) =
      measure size (square.dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have region_eq : (square.reflectY (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectY size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [identity] using square.mem_reflectY_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectY size)
  rw [region_eq]
  exact measure_preimage_reflectY size (square.measurableSet_dilatedInteriorRegion factor_positive.ne')

theorem score_gt_one_of_top_strip
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_above : (size : ℝ) - 1 ≤ factor * square.center.y) :
    1 < measure size (square.dilatedInteriorRegion factor) := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have reflected_inside := square.reflectY_dilatedInteriorRegion_subset_containerRegion
    positive identity inside_container
  have reflected_below : factor * (square.reflectY (size / factor)).center.y ≤ 1 := by
    change factor * ((size : ℝ) / factor - square.center.y) ≤ 1
    rw [mul_sub, identity]
    linarith
  have bound := score_gt_one_of_bottom_strip (square.reflectY (size / factor))
    ((square.reflectY_fits_iff _).2 fits) size_at_least_three factor_gt_one factor_at_most
    reflected_inside (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_horizontal)
    reflected_below
  rwa [score_reflectY square size positive] at bound

theorem score_gt_one_of_left_strip
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1))
    (center_left : factor * square.center.x ≤ 1) :
    1 < measure size (square.dilatedInteriorRegion factor) := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bound := score_gt_one_of_bottom_strip square.swap ((square.swap_fits_iff side).2 fits)
    size_at_least_three factor_gt_one factor_at_most
    (square.swap_dilatedInteriorRegion_subset_containerRegion positive inside_container)
    (by simpa [PlacedSquare.swap, Point.swap] using center_vertical)
    (by simpa [PlacedSquare.swap, Point.swap] using center_left)
  rwa [score_swap square size positive] at bound

theorem score_gt_one_of_right_strip
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1))
    (center_right : (size : ℝ) - 1 ≤ factor * square.center.x) :
    1 < measure size (square.dilatedInteriorRegion factor) := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have bound := score_gt_one_of_top_strip square.swap ((square.swap_fits_iff _).2 fits)
    size_at_least_three factor_gt_one factor_at_most
    (square.swap_dilatedInteriorRegion_subset_containerRegion positive inside_container)
    (by simpa [PlacedSquare.swap, Point.swap] using center_vertical)
    (by simpa [PlacedSquare.swap, Point.swap] using center_right)
  rwa [score_swap square size positive] at bound

theorem score_gt_one_of_fits
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size) :
    1 < measure size (square.dilatedInteriorRegion factor) := by
  have outside {coordinate : ℝ} (not_inner : coordinate ∉ Icc 1 ((size : ℝ) - 1)) :
      coordinate ≤ 1 ∨ (size : ℝ) - 1 ≤ coordinate := by
    by_cases lower : coordinate ≤ 1
    · exact Or.inl lower
    · exact Or.inr (le_of_not_gt fun upper => not_inner ⟨(lt_of_not_ge lower).le, upper.le⟩)
  by_cases horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1)
  · by_cases vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1)
    · apply (Nagamochi.score_gt_one_of_center_inner square factor_gt_one factor_at_most
        inside_container ?_).trans_le (original_le _ _)
      simp [Point.toPlane, Pi.le_def, Fin.forall_fin_two, horizontal.1, horizontal.2,
        vertical.1, vertical.2]
    · rcases outside vertical with below | above
      · exact score_gt_one_of_bottom_strip square fits size_at_least_three factor_gt_one
          factor_at_most inside_container horizontal below
      · exact score_gt_one_of_top_strip square fits size_at_least_three factor_gt_one
          factor_at_most inside_container horizontal above
  · by_cases vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1)
    · rcases outside horizontal with left | right
      · exact score_gt_one_of_left_strip square fits size_at_least_three factor_gt_one
          factor_at_most inside_container vertical left
      · exact score_gt_one_of_right_strip square fits size_at_least_three factor_gt_one
          factor_at_most inside_container vertical right
    · exact (Nagamochi.score_gt_one_of_case5 square size_at_least_three factor_gt_one
        inside_container (outside horizontal) (outside vertical)).trans_le (original_le _ _)

end SquarePackingArchive.NagamochiAugmentedResource

namespace SquarePackingArchive

open Function MeasureTheory Set

theorem Packing.squareCount_lt_squareMinusOne_of_side_lt
    {squareCount size : ℕ} {side : ℝ}
    (packing : Packing squareCount side)
    (squareCount_positive : 0 < squareCount)
    (size_at_least_three : 3 ≤ size)
    (side_lt_size : side < size) :
    squareCount < size * size - 1 := by
  have side_positive := packing.side_positive squareCount_positive
  have ratio_gt_one : 1 < (size : ℝ) / side := by
    rw [lt_div_iff₀ side_positive]
    simpa using side_lt_size
  have upper_gt_one : 1 < min (101 / 100 : ℝ) ((size : ℝ) / side) := by
    exact lt_min (by norm_num) ratio_gt_one
  obtain ⟨factor, factor_gt_one, factor_lt_upper⟩ := exists_between upper_gt_one
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have factor_at_most : factor ≤ 101 / 100 :=
    (factor_lt_upper.trans_le (min_le_left _ _)).le
  have scaled_side_lt : factor * side < size := by
    rw [← lt_div_iff₀ side_positive]
    exact factor_lt_upper.trans_le (min_le_right _ _)
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ factor_positive]
    nlinarith
  let regions : Fin squareCount → Set Plane :=
    fun index => (packing.squares index).dilatedInteriorRegion factor
  have regions_measurable : ∀ index, MeasurableSet (regions index) :=
    fun index => (packing.squares index).measurableSet_dilatedInteriorRegion factor_positive.ne'
  have regions_disjoint : Pairwise (Disjoint on regions) := by
    intro first second different
    exact PlacedSquare.disjoint_dilatedInteriorRegion
      (packing.disjoint first second different) factor_positive.ne'
  have scores : ∀ index, 1 < NagamochiAugmentedResource.measure size (regions index) := by
    intro index
    have fits : (packing.squares index).Fits ((size : ℝ) / factor) := by
      intro point contained
      have bounds := packing.fits index contained
      exact ⟨bounds.1, bounds.2.1.trans side_bound, bounds.2.2.1, bounds.2.2.2.trans side_bound⟩
    exact NagamochiAugmentedResource.score_gt_one_of_fits (packing.squares index) fits
      size_at_least_three factor_gt_one factor_at_most
      ((packing.squares index).dilatedInteriorRegion_subset_containerRegion
        (packing.fits index) factor_positive.le scaled_side_lt.le)
  have mass_finite : NagamochiAugmentedResource.measure size univ ≠ ⊤ := by
    rw [NagamochiAugmentedResource.measure_univ size_at_least_three]
    finiteness
  have bound := finiteFamily_card_lt_resourceMass (NagamochiAugmentedResource.measure size)
    squareCount_positive mass_finite regions regions_measurable regions_disjoint scores
  rw [NagamochiAugmentedResource.measure_univ size_at_least_three,
    ← ENNReal.ofReal_natCast] at bound
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  have real_bound : (squareCount : ℝ) < (size : ℝ) ^ 2 - 8 / 5 :=
    (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mp bound
  have count_bound : (squareCount : ℝ) < (size * size - 1 : ℕ) := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ size * size)]
    push_cast
    nlinarith
  exact_mod_cast count_bound

theorem Records.NearSquare.squareMinusOne_isMinimumSide
    {size : ℕ} (size_at_least_two : 2 ≤ size) :
    IsMinimumSide (size * size - 1) size := by
  by_cases size_is_two : size = 2
  · subst size
    exact Records.NearSquare.s3_eq_two
  have size_at_least_three : 3 ≤ size := by omega
  constructor
  · exact Records.NearSquare.squareMinusOne_hasPacking size
  · intro candidateSide hasPacking
    by_contra smaller
    have square_lower : 9 ≤ size * size := Nat.mul_le_mul size_at_least_three size_at_least_three
    have contradiction := hasPacking.some.squareCount_lt_squareMinusOne_of_side_lt
      (by omega : 0 < size * size - 1) size_at_least_three (lt_of_not_ge smaller)
    omega

theorem Records.NearSquare.s63_eq_eight : IsMinimumSide 63 8 := by
  simpa using (Records.NearSquare.squareMinusOne_isMinimumSide (size := 8) (by norm_num))

theorem Records.NearSquare.s80_eq_nine : IsMinimumSide 80 9 := by
  simpa using (Records.NearSquare.squareMinusOne_isMinimumSide (size := 9) (by norm_num))

theorem Records.NearSquare.s99_eq_ten : IsMinimumSide 99 10 := by
  simpa using (Records.NearSquare.squareMinusOne_isMinimumSide (size := 10) (by norm_num))

end SquarePackingArchive
