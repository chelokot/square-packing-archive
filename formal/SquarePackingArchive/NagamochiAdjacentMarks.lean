import SquarePackingArchive.NagamochiAugmentedResource
import SquarePackingArchive.NagamochiBadSquare
import SquarePackingArchive.NagamochiPackingConstraints

namespace SquarePackingArchive.NagamochiAugmentedResource

open MeasureTheory Set

lemma measure_preimage_reflectX (size : ℕ) {region : Set Plane}
    (measurable : MeasurableSet region) :
    measure size (Plane.reflectX size ⁻¹' region) = measure size region := by
  rw [Nagamochi.preimage_reflectX_eq,
    measure_preimage_swap size ((measurable.preimage Nagamochi.measurable_swapPlane).preimage
      (Nagamochi.measurable_reflectYPlane size)),
    measure_preimage_reflectY size (measurable.preimage Nagamochi.measurable_swapPlane),
    measure_preimage_swap size measurable]

lemma score_reflectX (square : PlacedSquare) (size : ℕ) {factor : ℝ}
    (factor_positive : 0 < factor) :
    measure size ((square.reflectX (size / factor)).dilatedInteriorRegion factor) =
      measure size (square.dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have region_eq : (square.reflectX (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectX size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [identity] using square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectX size)
  rw [region_eq]
  exact measure_preimage_reflectX size (square.measurableSet_dilatedInteriorRegion factor_positive.ne')

end SquarePackingArchive.NagamochiAugmentedResource

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma dilated_square_point_center_coordinate_distance_lt_one
    (square : PlacedSquare) {factor : ℝ} {point : Plane}
    (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (point_mem : point ∈ square.dilatedInteriorRegion factor) :
    |point 0 - factor * square.center.x| < 1 ∧
      |point 1 - factor * square.center.y| < 1 := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ :=
    (square.mem_dilatedInteriorRegion_iff factor_positive point).1 point_mem
  have horizontal_eq := congrArg Point.x point_eq
  have vertical_eq := congrArg Point.y point_eq
  simp only [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place] at horizontal_eq vertical_eq
  have norm_identity : (point 0 - factor * square.center.x) ^ 2 +
      (point 1 - factor * square.center.y) ^ 2 = localX ^ 2 + localY ^ 2 := by
    rw [horizontal_eq, vertical_eq]
    linear_combination (localX ^ 2 + localY ^ 2) * square.frame.unit
  have norm_bound : (point 0 - factor * square.center.x) ^ 2 +
      (point 1 - factor * square.center.y) ^ 2 < 1 := by
    nlinarith [sq_abs localX, sq_abs localY, abs_nonneg localX, abs_nonneg localY]
  constructor <;> rw [abs_lt] <;> constructor <;>
    nlinarith [sq_nonneg (point 0 - factor * square.center.x),
      sq_nonneg (point 1 - factor * square.center.y)]

theorem augmentedScore_gt_three_halves_of_center_inner_and_edge_point
    (square : PlacedSquare) {size coordinate : ℕ} {factor : ℝ}
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (center_inside : factor • square.center.toPlane ∈
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint)
    (point_mem : NagamochiResource.edgePoint size coordinate kind ∈ square.dilatedInteriorRegion factor) :
    (3 / 2 : ENNReal) < NagamochiAugmentedResource.measure size (square.dilatedInteriorRegion factor) := by
  have measurable := square.measurableSet_dilatedInteriorRegion (zero_lt_one.trans factor_gt_one).ne'
  have continuous_corner := continuous_corner_score_gt_one_of_center_inner square
    factor_gt_one factor_at_most inside_container center_inside
  have edge_bound := NagamochiResource.edgePoints_lower_bound_of_mem kind coordinate_mem measurable point_mem
  have strict := (ENNReal.add_lt_add_iff_right (by finiteness : (1 / 2 : ENNReal) ≠ ⊤)).2 continuous_corner
  have halves : (1 : ENNReal) + 1 / 2 = 3 / 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]
  rw [halves] at strict
  exact (strict.trans_le (by
    simpa only [NagamochiResource.measure, Measure.add_apply] using add_le_add le_rfl edge_bound)).trans_le
    (NagamochiAugmentedResource.original_le size _)

theorem augmentedScore_gt_three_halves_of_adjacent_corner_and_bottom_point
    (square : PlacedSquare) {size : ℕ} {side factor : ℝ}
    (fits : square.Fits side) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (edge_mem : ![(2 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor) :
    (3 / 2 : ENNReal) < NagamochiAugmentedResource.measure size (square.dilatedInteriorRegion factor) := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have measurable := square.measurableSet_dilatedInteriorRegion positive.ne'
  have size_real : (4 : ℝ) ≤ size := by exact_mod_cast size_at_least_four
  have first_distance := dilated_square_point_center_coordinate_distance_lt_one square
    positive factor_at_most corner_mem
  have second_distance := dilated_square_point_center_coordinate_distance_lt_one square
    positive factor_at_most edge_mem
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at first_distance second_distance
  rw [abs_lt, abs_lt] at first_distance second_distance
  have center_horizontal : factor * square.center.x ∈ Icc 1 ((size : ℝ) - 1) := by
    constructor <;> linarith
  have coordinate_mem : 2 ∈ Finset.Icc 2 (size - 2) := by simp only [Finset.mem_Icc]; omega
  have edge_bound := NagamochiResource.edgePoints_lower_bound_of_mem (size := size) .bottom coordinate_mem
    measurable (by simpa [NagamochiResource.edgePoint] using edge_mem)
  have corner_bound := NagamochiAugmentedResource.cornerPoints_lower_bound_of_mem (size := size) .leftBottom
    measurable (by simpa [NagamochiResource.cornerPoint] using corner_mem)
  by_cases center_below : factor * square.center.y ≤ 1
  · have continuous_positive := innerArea_positive_of_bottom_edge_strip_geometry square (by omega)
      factor_gt_one inside_container center_horizontal.1 center_horizontal.2 center_below
    by_cases horizontal_corner : ∃ kind : NagamochiResource.CornerPoint,
        (kind = .bottomLeft ∨ kind = .bottomRight) ∧
          NagamochiResource.cornerPoint size kind ∈ square.dilatedInteriorRegion factor
    · obtain ⟨kind, horizontal_kind, horizontal_mem⟩ := horizontal_corner
      have different : kind ≠ NagamochiResource.CornerPoint.leftBottom := by
        rcases horizontal_kind with rfl | rfl <;> decide
      have two_corners := NagamochiAugmentedResource.cornerPoints_lower_bound_of_two_mem measurable different
        horizontal_mem (by simpa [NagamochiResource.cornerPoint] using corner_mem)
      have strict := (ENNReal.add_lt_add_iff_right
        (by finiteness : (1 + 1 / 2 : ENNReal) ≠ ⊤)).2 continuous_positive
      have combined := strict.trans_le (add_le_add le_rfl (add_le_add two_corners edge_bound))
      have constant_eq : (0 : ENNReal) + (1 + 1 / 2) = 3 / 2 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add]
      rw [constant_eq] at combined
      apply combined.trans_le
      rw [NagamochiAugmentedResource.measure_apply]
      calc
        _ = NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
            NagamochiAugmentedResource.cornerPoints size (square.dilatedInteriorRegion factor) +
              NagamochiResource.edgePoints size (square.dilatedInteriorRegion factor) := by ac_rfl
        _ ≤ _ := add_le_add (add_le_add (le_add_of_nonneg_right bot_le) le_rfl) le_rfl
    · have first_missing : NagamochiResource.cornerPoint size .bottomLeft ∉ square.dilatedInteriorRegion factor :=
        fun contained => horizontal_corner ⟨.bottomLeft, Or.inl rfl, contained⟩
      have second_missing : NagamochiResource.cornerPoint size .bottomRight ∉ square.dilatedInteriorRegion factor :=
        fun contained => horizontal_corner ⟨.bottomRight, Or.inr rfl, contained⟩
      have continuous_bound := continuous_score_gt_half_of_bottom_strip_missing_horizontal_corners square fits
        (by omega) factor_gt_one factor_at_most inside_container center_horizontal center_below
        first_missing second_missing
      have strict := (ENNReal.add_lt_add_iff_right
        (by finiteness : (1 / 2 + 1 / 2 : ENNReal) ≠ ⊤)).2 continuous_bound
      have combined := strict.trans_le (add_le_add le_rfl (add_le_add corner_bound edge_bound))
      have constant_eq : (1 / 2 : ENNReal) + (1 / 2 + 1 / 2) = 3 / 2 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add]
      rw [constant_eq] at combined
      simpa only [NagamochiAugmentedResource.measure_apply, add_assoc] using combined
  · apply augmentedScore_gt_three_halves_of_center_inner_and_edge_point square factor_gt_one
      factor_at_most inside_container ?_ coordinate_mem .bottom
      (by simpa [NagamochiResource.edgePoint] using edge_mem)
    simp only [Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, Point.toPlane,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨⟨center_horizontal.1, by linarith⟩, ⟨center_horizontal.2, by linarith⟩⟩

theorem augmentedScore_gt_three_halves_of_adjacent_right_corner_and_bottom_point
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (fits : square.Fits (size / factor)) (size_at_least_four : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (inside_container : square.dilatedInteriorRegion factor ⊆ containerRegion size)
    (corner_mem : ![(size : ℝ) - 1, 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (edge_mem : ![(size : ℝ) - 2, 9 / 10] ∈ square.dilatedInteriorRegion factor) :
    (3 / 2 : ENNReal) < NagamochiAugmentedResource.measure size (square.dilatedInteriorRegion factor) := by
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  have reflected_corner := (square.mem_reflectX_dilatedInteriorRegion_iff
    (coordinateSum := size / factor) positive _).2 corner_mem
  have reflected_edge := (square.mem_reflectX_dilatedInteriorRegion_iff
    (coordinateSum := size / factor) positive _).2 edge_mem
  have bound := augmentedScore_gt_three_halves_of_adjacent_corner_and_bottom_point
    (square.reflectX (size / factor)) ((square.reflectX_fits_iff _).2 fits)
    size_at_least_four factor_gt_one factor_at_most
    (square.reflectX_dilatedInteriorRegion_subset_containerRegion positive identity inside_container)
    (by simpa [Plane.reflectX, identity] using reflected_corner)
    (by simpa [Plane.reflectX, identity] using reflected_edge)
  rwa [NagamochiAugmentedResource.score_reflectX square size positive] at bound

end SquarePackingArchive.Nagamochi

namespace SquarePackingArchive

theorem Packing.squareMinusTwo_not_adjacent_bottom_corner_and_edge
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (owner : Fin (size * size - 2)) :
    ¬(![(1 : ℝ), 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor ∧
      ![(2 : ℝ), 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor) := by
  rintro ⟨corner_mem, edge_mem⟩
  have score_lower := Nagamochi.augmentedScore_gt_three_halves_of_adjacent_corner_and_bottom_point
    (packing.squares owner) (packing.fits owner) size_lower factor_gt_one factor_at_most
    ((packing.squares owner).dilatedInteriorRegion_subset_containerRegion
      (packing.fits owner) (zero_lt_one.trans factor_gt_one).le scaled_side_le) corner_mem edge_mem
  have score_upper := packing.squareMinusTwo_augmentedScore_lt_seven_fifths (by omega)
    factor_gt_one factor_at_most scaled_side_le owner
  have contradiction : (3 / 2 : ENNReal) < 7 / 5 := score_lower.trans score_upper
  have real_contradiction := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr contradiction
  norm_num at real_contradiction

theorem Packing.squareMinusTwo_not_adjacent_right_bottom_corner_and_edge
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (owner : Fin (size * size - 2)) :
    ¬(![(size : ℝ) - 1, 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor ∧
      ![(size : ℝ) - 2, 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor) := by
  rintro ⟨corner_mem, edge_mem⟩
  have positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ positive]
    nlinarith
  have fits : (packing.squares owner).Fits ((size : ℝ) / factor) := by
    intro point point_mem
    have bounds := packing.fits owner point_mem
    exact ⟨bounds.1, bounds.2.1.trans side_bound, bounds.2.2.1, bounds.2.2.2.trans side_bound⟩
  have score_lower := Nagamochi.augmentedScore_gt_three_halves_of_adjacent_right_corner_and_bottom_point
    (packing.squares owner) fits size_lower factor_gt_one factor_at_most
    ((packing.squares owner).dilatedInteriorRegion_subset_containerRegion
      (packing.fits owner) positive.le scaled_side_le) corner_mem edge_mem
  have score_upper := packing.squareMinusTwo_augmentedScore_lt_seven_fifths (by omega)
    factor_gt_one factor_at_most scaled_side_le owner
  have contradiction : (3 / 2 : ENNReal) < 7 / 5 := score_lower.trans score_upper
  have real_contradiction := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr contradiction
  norm_num at real_contradiction

end SquarePackingArchive
