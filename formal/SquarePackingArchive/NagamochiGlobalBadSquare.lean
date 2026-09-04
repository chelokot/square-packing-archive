import SquarePackingArchive.NagamochiBadSquare
import SquarePackingArchive.NagamochiResourceSymmetry
import SquarePackingArchive.NagamochiInnerCorners

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma original_components_swap (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.measure size (square.swap.dilatedInteriorRegion factor) =
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.cornerPoints size (square.swap.dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size (square.swap.dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by
  have region_eq : square.swap.dilatedInteriorRegion factor =
      Plane.swap ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa using square.mem_swap_dilatedInteriorRegion_iff factor_positive point.swap
  rw [region_eq]
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  exact ⟨resourceMeasure_preimage_swap size measurable,
    cornerPoints_preimage_swap size measurable, edgePoints_preimage_swap size measurable⟩

lemma original_components_reflectY (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.measure size ((square.reflectY (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.cornerPoints size ((square.reflectY (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) ∧
    NagamochiResource.edgePoints size ((square.reflectY (size / factor)).dilatedInteriorRegion factor) =
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have region_eq : (square.reflectY (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectY size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [identity] using square.mem_reflectY_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectY size)
  rw [region_eq]
  have measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  exact ⟨resourceMeasure_preimage_reflectY size measurable,
    cornerPoints_preimage_reflectY size measurable, edgePoints_preimage_reflectY size measurable⟩

lemma marked_masses_of_unique_corner_and_no_edges
    {size : ℕ} {region : Set Plane} (measurable : MeasurableSet region)
    (unique_corner : ∃ kind, ∀ candidate,
      NagamochiResource.cornerPoint size candidate ∈ region ↔ candidate = kind)
    (no_edges : ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
      NagamochiResource.edgePoint size coordinate kind ∉ region) :
    NagamochiResource.cornerPoints size region = 9 / 20 ∧
      NagamochiResource.edgePoints size region = 0 := by
  classical
  obtain ⟨kind, unique_corner⟩ := unique_corner
  constructor
  · simp only [NagamochiResource.cornerPoints, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurable, Set.indicator_apply, Pi.one_apply, unique_corner]
    simp [NagamochiResource.mem_cornerPointKinds]
  · simp only [NagamochiResource.edgePoints, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro coordinate coordinate_mem
    simp [NagamochiResource.edgePointCluster, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ measurable, no_edges coordinate coordinate_mem]

lemma bottom_bad_square_marked_masses
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) = 9 / 20 ∧
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) = 0 := by
  obtain ⟨kind, _, unique_corner⟩ := bottom_bad_square_has_exactly_one_corner_point square fits
    size_at_least_four factor_gt_one factor_at_most inside_container center_horizontal center_below bad
  exact marked_masses_of_unique_corner_and_no_edges
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne')
    ⟨kind, unique_corner⟩ ((bottom_bad_square_location square fits size_at_least_four factor_gt_one
      factor_at_most inside_container center_horizontal center_below bad).1)

lemma top_bad_square_marked_masses
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_above : (size : ℝ) - 1 ≤ factor * square.center.y)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) = 9 / 20 ∧
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) = 0 := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have components := original_components_reflectY square size positive
  have reflected_below : factor * (square.reflectY (size / factor)).center.y ≤ 1 := by
    change factor * ((size : ℝ) / factor - square.center.y) ≤ 1
    rw [mul_sub, identity]
    linarith
  have result := bottom_bad_square_marked_masses (square.reflectY (size / factor))
    ((square.reflectY_fits_iff _).2 fits) size_at_least_four factor_gt_one factor_at_most
    (square.reflectY_dilatedInteriorRegion_subset_containerRegion positive identity inside_container)
    (by simpa [PlacedSquare.reflectY, Point.reflectY] using center_horizontal) reflected_below
    (by rwa [components.1])
  rwa [components.2.1, components.2.2] at result

theorem bad_square_marked_masses
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    NagamochiResource.cornerPoints size (square.dilatedInteriorRegion factor) = 9 / 20 ∧
      NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) = 0 := by
  have outside {coordinate : ℝ} (not_inner : coordinate ∉ Icc 1 ((size : ℝ) - 1)) :
      coordinate ≤ 1 ∨ (size : ℝ) - 1 ≤ coordinate := by
    by_cases lower : coordinate ≤ 1
    · exact Or.inl lower
    · exact Or.inr (le_of_not_gt fun upper => not_inner ⟨(lt_of_not_ge lower).le, upper.le⟩)
  by_cases horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1)
  · by_cases vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1)
    · exfalso
      apply (not_lt_of_ge bad) (score_gt_one_of_center_inner square factor_gt_one factor_at_most
        inside_container ?_)
      simp [Point.toPlane, Pi.le_def, Fin.forall_fin_two, horizontal.1, horizontal.2,
        vertical.1, vertical.2]
    · rcases outside vertical with below | above
      · exact bottom_bad_square_marked_masses square fits size_at_least_four factor_gt_one
          factor_at_most inside_container horizontal below bad
      · exact top_bad_square_marked_masses square fits size_at_least_four factor_gt_one
          factor_at_most inside_container horizontal above bad
  · by_cases vertical : factor * square.center.y ∈ Icc 1 ((size : ℝ) - 1)
    · have positive : 0 < factor := zero_lt_one.trans factor_gt_one
      have components := original_components_swap square size positive
      have swapped_fits := (square.swap_fits_iff _).2 fits
      have swapped_inside := square.swap_dilatedInteriorRegion_subset_containerRegion positive inside_container
      have swapped_horizontal : factor * square.swap.center.x ∈ Icc 1 ((size : ℝ) - 1) := by
        simpa [PlacedSquare.swap, Point.swap] using vertical
      have swapped_bad : NagamochiResource.measure size (square.swap.dilatedInteriorRegion factor) ≤ 1 := by
        rwa [components.1]
      rcases outside horizontal with left | right
      · have result := bottom_bad_square_marked_masses square.swap swapped_fits size_at_least_four
          factor_gt_one factor_at_most swapped_inside swapped_horizontal
          (by simpa [PlacedSquare.swap, Point.swap] using left) swapped_bad
        rwa [components.2.1, components.2.2] at result
      · have result := top_bad_square_marked_masses square.swap swapped_fits size_at_least_four
          factor_gt_one factor_at_most swapped_inside swapped_horizontal
          (by simpa [PlacedSquare.swap, Point.swap] using right) swapped_bad
        rwa [components.2.1, components.2.2] at result
    · exact False.elim ((not_lt_of_ge bad) (score_gt_one_of_case5 square (by omega)
        factor_gt_one inside_container (outside horizontal) (outside vertical)))

lemma unique_corner_and_no_edges_of_marked_masses
    {size : ℕ} {region : Set Plane} (measurable : MeasurableSet region)
    (corner_mass : NagamochiResource.cornerPoints size region = 9 / 20)
    (edge_mass : NagamochiResource.edgePoints size region = 0) :
    (∃! kind, NagamochiResource.cornerPoint size kind ∈ region) ∧
      ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
        NagamochiResource.edgePoint size coordinate kind ∉ region := by
  classical
  have some_corner : ∃ kind, NagamochiResource.cornerPoint size kind ∈ region := by
    by_contra! no_corner
    have zero_mass : NagamochiResource.cornerPoints size region = 0 := by
      simp [NagamochiResource.cornerPoints, Measure.smul_apply, Measure.finsetSum_apply,
        Measure.dirac_apply' _ measurable, no_corner]
    rw [zero_mass] at corner_mass
    have real_mass := congrArg ENNReal.toReal corner_mass
    norm_num at real_mass
  constructor
  · obtain ⟨kind, kind_mem⟩ := some_corner
    refine ⟨kind, kind_mem, ?_⟩
    intro candidate candidate_mem
    by_contra different
    have double_bound := NagamochiResource.cornerPoints_lower_bound_of_two_mem measurable
      different candidate_mem kind_mem
    rw [corner_mass] at double_bound
    have real_bound := ENNReal.toReal_mono (by finiteness) double_bound
    norm_num at real_bound
  · intro coordinate coordinate_mem kind point_mem
    have positive_bound := NagamochiResource.edgePoints_lower_bound_of_mem kind coordinate_mem
      measurable point_mem
    rw [edge_mass] at positive_bound
    norm_num at positive_bound

theorem bad_square_has_exactly_one_corner_and_no_edge_points
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (bad : NagamochiResource.measure size (square.dilatedInteriorRegion factor) ≤ 1) :
    (∃! kind, NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor) ∧
      ∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind,
        NagamochiResource.edgePoint size coordinate kind ∉ square.dilatedInteriorRegion factor := by
  have masses := bad_square_marked_masses square fits size_at_least_four factor_gt_one
    factor_at_most inside_container bad
  exact unique_corner_and_no_edges_of_marked_masses
    (square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne') masses.1 masses.2

end SquarePackingArchive.Nagamochi
