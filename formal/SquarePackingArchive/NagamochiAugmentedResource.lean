import SquarePackingArchive.NagamochiEdgeStripWithCorners
import SquarePackingArchive.NagamochiInnerCorners

namespace SquarePackingArchive.NagamochiAugmentedResource

open MeasureTheory Set

noncomputable def cornerPoints (size : ℕ) : Measure Plane :=
  (10 / 9 : ENNReal) • NagamochiResource.cornerPoints size

noncomputable def measure (size : ℕ) : Measure Plane :=
  NagamochiResource.innerArea size + NagamochiResource.boundaryLines size +
    cornerPoints size + NagamochiResource.edgePoints size

lemma measure_apply (size : ℕ) (region : Set Plane) :
    measure size region = NagamochiResource.innerArea size region +
      NagamochiResource.boundaryLines size region + cornerPoints size region +
      NagamochiResource.edgePoints size region := by
  simp [measure]

lemma cornerPoints_lower_bound_of_mem
    {size : ℕ} {region : Set Plane} (kind : NagamochiResource.CornerPoint)
    (measurable : MeasurableSet region)
    (contained : NagamochiResource.cornerPoint size kind ∈ region) :
    (1 / 2 : ENNReal) ≤ cornerPoints size region := by
  have bound := mul_le_mul (a := (10 / 9 : ENNReal)) le_rfl
    (NagamochiResource.cornerPoints_lower_bound_of_mem kind measurable contained) bot_le bot_le
  have weight : (10 / 9 : ENNReal) * (9 / 20) = 1 / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul]
  simpa [cornerPoints, weight] using bound

lemma cornerPoints_lower_bound_of_two_mem
    {size : ℕ} {region : Set Plane} {first second : NagamochiResource.CornerPoint}
    (measurable : MeasurableSet region) (different : first ≠ second)
    (first_contained : NagamochiResource.cornerPoint size first ∈ region)
    (second_contained : NagamochiResource.cornerPoint size second ∈ region) :
    1 ≤ cornerPoints size region := by
  have bound := mul_le_mul (a := (10 / 9 : ENNReal)) le_rfl
    (NagamochiResource.cornerPoints_lower_bound_of_two_mem measurable different
      first_contained second_contained) bot_le bot_le
  have weight : (10 / 9 : ENNReal) * (9 / 10) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul]
  simpa [cornerPoints, weight] using bound

lemma original_le (size : ℕ) (region : Set Plane) :
    NagamochiResource.measure size region ≤ measure size region := by
  have weight : (1 : ENNReal) ≤ 10 / 9 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  have bound := mul_le_mul weight (le_rfl : NagamochiResource.cornerPoints size region ≤ _)
    bot_le bot_le
  simp only [one_mul] at bound
  simpa [NagamochiResource.measure, measure, cornerPoints] using
    add_le_add (add_le_add le_rfl bound) le_rfl

lemma measure_univ {size : ℕ} (size_at_least_three : 3 ≤ size) :
    measure size univ = ENNReal.ofReal ((size : ℝ) ^ 2 - 8 / 5) := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_at_least_three
  rw [measure_apply, NagamochiResource.innerArea_univ (by omega),
    NagamochiResource.boundaryLines_univ (by omega), cornerPoints, Measure.smul_apply,
    NagamochiResource.cornerPoints_univ, NagamochiResource.edgePoints_univ]
  simp only [smul_eq_mul]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  repeat' rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal (sq_nonneg ((size : ℝ) - 2)),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * (size : ℝ) - 18 / 5),
    ENNReal.toReal_ofReal (by nlinarith : 0 ≤ (size : ℝ) ^ 2 - 8 / 5)]
  rw [ENNReal.toReal_natCast]
  norm_num [ENNReal.toReal_mul]
  rw [Nat.cast_sub size_at_least_three]
  push_cast
  ring

lemma marked_points_ge_half_of_bottom_grid_witness
    {size : ℕ} {region : Set Plane} (measurable : MeasurableSet region)
    (witness : Nagamochi.GridPointWitness size region .bottom) :
    (1 / 2 : ENNReal) ≤ cornerPoints size region + NagamochiResource.edgePoints size region := by
  cases witness with
  | firstCorner contained =>
    exact (cornerPoints_lower_bound_of_mem _ measurable contained).trans (le_add_of_nonneg_right bot_le)
  | secondCorner contained =>
    exact (cornerPoints_lower_bound_of_mem _ measurable contained).trans (le_add_of_nonneg_right bot_le)
  | edge coordinate coordinate_mem contained =>
    exact (NagamochiResource.edgePoints_lower_bound_of_mem .bottom coordinate_mem
      measurable contained).trans (le_add_of_nonneg_left bot_le)

lemma marked_points_ge_one_of_horizontal_corner_and_bottom_grid_witness
    {size : ℕ} {region : Set Plane} {kind : NagamochiResource.CornerPoint}
    (measurable : MeasurableSet region)
    (horizontal_kind : kind = .bottomLeft ∨ kind = .bottomRight)
    (contained : NagamochiResource.cornerPoint size kind ∈ region)
    (witness : Nagamochi.GridPointWitness size region .bottom) :
    1 ≤ cornerPoints size region + NagamochiResource.edgePoints size region := by
  have different_first : kind ≠ NagamochiResource.EdgePoint.bottom.firstCornerPoint := by
    rcases horizontal_kind with rfl | rfl <;> decide
  have different_second : kind ≠ NagamochiResource.EdgePoint.bottom.secondCornerPoint := by
    rcases horizontal_kind with rfl | rfl <;> decide
  cases witness with
  | firstCorner second_contained =>
    exact (cornerPoints_lower_bound_of_two_mem measurable different_first contained
      second_contained).trans (le_add_of_nonneg_right bot_le)
  | secondCorner second_contained =>
    exact (cornerPoints_lower_bound_of_two_mem measurable different_second contained
      second_contained).trans (le_add_of_nonneg_right bot_le)
  | edge coordinate coordinate_mem edge_contained =>
    have bound := add_le_add (cornerPoints_lower_bound_of_mem kind measurable contained)
      (NagamochiResource.edgePoints_lower_bound_of_mem .bottom coordinate_mem measurable edge_contained)
    have halves : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]
    rwa [halves] at bound

theorem score_gt_one_of_bottom_strip
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_three : 3 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1))
    (center_below : factor * square.center.y ≤ 1) :
    1 < measure size (square.dilatedInteriorRegion factor) := by
  let region := square.dilatedInteriorRegion factor
  have measurable : MeasurableSet region :=
    square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne'
  have grid := Nagamochi.bottomGridPointWitness_of_center_in_bottom_strip_geometry square
    size_at_least_three factor_gt_one inside_container center_below
  have continuous_positive : 0 < NagamochiResource.innerArea size region +
      NagamochiResource.boundaryLines size region :=
    (Nagamochi.innerArea_positive_of_bottom_edge_strip_geometry square size_at_least_three
      factor_gt_one inside_container center_horizontal.1 center_horizontal.2 center_below).trans_le
        (le_add_of_nonneg_right bot_le)
  rw [measure_apply, add_assoc]
  by_cases horizontal_corner : ∃ kind : NagamochiResource.CornerPoint,
      (kind = .bottomLeft ∨ kind = .bottomRight) ∧ NagamochiResource.cornerPoint size kind ∈ region
  · obtain ⟨kind, horizontal_kind, contained⟩ := horizontal_corner
    have points_bound := marked_points_ge_one_of_horizontal_corner_and_bottom_grid_witness
      measurable horizontal_kind contained grid
    have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 : ENNReal) ≠ ⊤)).2
      continuous_positive
    simpa using strict.trans_le (add_le_add le_rfl points_bound)
  · have first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ region :=
      fun contained => horizontal_corner ⟨.bottomLeft, Or.inl rfl, contained⟩
    have second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ region :=
      fun contained => horizontal_corner ⟨.bottomRight, Or.inr rfl, contained⟩
    have continuous_bound := Nagamochi.continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners
      square fits size_at_least_three factor_gt_one factor_at_most inside_container
      center_horizontal center_below first_missing second_missing
    have points_bound := marked_points_ge_half_of_bottom_grid_witness measurable grid
    have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 / 2 : ENNReal) ≠ ⊤)).2
      continuous_bound
    have halves : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]
    rw [halves] at strict
    exact strict.trans_le (add_le_add le_rfl points_bound)

end SquarePackingArchive.NagamochiAugmentedResource
