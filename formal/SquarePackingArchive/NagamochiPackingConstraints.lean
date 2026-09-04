import SquarePackingArchive.NagamochiAugmented
import SquarePackingArchive.NagamochiDoublePoint

namespace SquarePackingArchive

open Function MeasureTheory Set

noncomputable def Packing.augmentedScore
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (size : ℕ) (factor : ℝ) (index : Fin squareCount) : ENNReal :=
  NagamochiAugmentedResource.measure size ((packing.squares index).dilatedInteriorRegion factor)

def Packing.dilatedUnion
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) (factor : ℝ) : Set Plane :=
  ⋃ index, (packing.squares index).dilatedInteriorRegion factor

lemma Packing.augmentedScore_finite
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 3 ≤ size) (index : Fin squareCount) :
    packing.augmentedScore size factor index ≠ ⊤ := by
  have mass_finite : NagamochiAugmentedResource.measure size univ ≠ ⊤ := by
    rw [NagamochiAugmentedResource.measure_univ size_lower]
    finiteness
  exact ne_top_of_le_ne_top mass_finite (measure_mono (subset_univ _))

lemma Packing.augmentedScore_gt_one
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (index : Fin squareCount) :
    1 < packing.augmentedScore size factor index := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ factor_positive]
    nlinarith
  have fits : (packing.squares index).Fits ((size : ℝ) / factor) := by
    intro point contained
    have bounds := packing.fits index contained
    exact ⟨bounds.1, bounds.2.1.trans side_bound, bounds.2.2.1, bounds.2.2.2.trans side_bound⟩
  exact NagamochiAugmentedResource.score_gt_one_of_fits (packing.squares index) fits
    size_lower factor_gt_one factor_at_most
    ((packing.squares index).dilatedInteriorRegion_subset_containerRegion
      (packing.fits index) factor_positive.le scaled_side_le)

lemma Packing.augmentedScore_sum_eq_union
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (factor_positive : 0 < factor) :
    ∑ index, packing.augmentedScore size factor index =
      NagamochiAugmentedResource.measure size (packing.dilatedUnion factor) := by
  classical
  have disjoint_regions : Pairwise
      (Disjoint on fun index => (packing.squares index).dilatedInteriorRegion factor) := by
    intro first second different
    exact PlacedSquare.disjoint_dilatedInteriorRegion
      (packing.disjoint first second different) factor_positive.ne'
  have union_eq : packing.dilatedUnion factor =
      ⋃ index ∈ (Finset.univ : Finset (Fin squareCount)),
        (packing.squares index).dilatedInteriorRegion factor := by simp [Packing.dilatedUnion]
  rw [union_eq, measure_biUnion_finset]
  · rfl
  · intro first first_mem second second_mem different
    exact disjoint_regions different
  · intro index index_mem
    exact (packing.squares index).measurableSet_dilatedInteriorRegion factor_positive.ne'

lemma NagamochiAugmentedResource.mass_toReal_squareMinusTwo
    {size : ℕ} (size_lower : 3 ≤ size) :
    (NagamochiAugmentedResource.measure size univ).toReal = ((size * size - 2 : ℕ) : ℝ) + 2 / 5 := by
  have size_real : (3 : ℝ) ≤ size := by exact_mod_cast size_lower
  rw [NagamochiAugmentedResource.measure_univ size_lower,
    ENNReal.toReal_ofReal (by nlinarith : 0 ≤ (size : ℝ) ^ 2 - 8 / 5),
    Nat.cast_sub (by nlinarith : 2 ≤ size * size)]
  push_cast
  ring

lemma Packing.squareMinusTwo_augmentedScore_budget
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size) :
    ((size * size - 2 : ℕ) : ℝ) < ∑ index, (packing.augmentedScore size factor index).toReal ∧
      (∑ index, (packing.augmentedScore size factor index).toReal) ≤
        ((size * size - 2 : ℕ) : ℝ) + 2 / 5 := by
  classical
  have count_positive : 0 < size * size - 2 := by
    have square_lower := Nat.mul_le_mul size_lower size_lower
    omega
  have score_gt_one : ∀ index, 1 < (packing.augmentedScore size factor index).toReal := by
    intro index
    simpa using (ENNReal.toReal_lt_toReal (by simp)
      (packing.augmentedScore_finite size_lower index)).mpr
        (packing.augmentedScore_gt_one size_lower factor_gt_one factor_at_most scaled_side_le index)
  constructor
  · calc
      ((size * size - 2 : ℕ) : ℝ) = ∑ index : Fin (size * size - 2), (1 : ℝ) := by simp
      _ < _ := Finset.sum_lt_sum (fun index _ => (score_gt_one index).le)
        ⟨⟨0, count_positive⟩, Finset.mem_univ _, score_gt_one _⟩
  · have sum_bound : ∑ index, packing.augmentedScore size factor index ≤
        NagamochiAugmentedResource.measure size univ := by
      rw [packing.augmentedScore_sum_eq_union (zero_lt_one.trans factor_gt_one)]
      exact measure_mono (subset_univ _)
    have mass_finite : NagamochiAugmentedResource.measure size univ ≠ ⊤ := by
      rw [NagamochiAugmentedResource.measure_univ size_lower]
      finiteness
    have real_bound := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top mass_finite sum_bound) mass_finite).mpr sum_bound
    rw [ENNReal.toReal_sum (fun index _ => packing.augmentedScore_finite size_lower index),
      NagamochiAugmentedResource.mass_toReal_squareMinusTwo size_lower] at real_bound
    exact real_bound

theorem Packing.squareMinusTwo_heavyPoint_has_owner
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (point : Plane)
    (point_mass : (1 / 2 : ENNReal) ≤ NagamochiAugmentedResource.measure size {point}) :
    ∃ index, point ∈ (packing.squares index).dilatedInteriorRegion factor := by
  classical
  by_contra unowned
  have point_outside : point ∉ packing.dilatedUnion factor := by
    simpa [Packing.dilatedUnion] using unowned
  have separated : Disjoint (packing.dilatedUnion factor) {point} :=
    Set.disjoint_singleton_right.mpr point_outside
  have mass_finite : NagamochiAugmentedResource.measure size univ ≠ ⊤ := by
    rw [NagamochiAugmentedResource.measure_univ size_lower]
    finiteness
  have singleton_finite : NagamochiAugmentedResource.measure size {point} ≠ ⊤ :=
    ne_top_of_le_ne_top mass_finite (measure_mono (subset_univ _))
  have sum_finite : ∑ index, packing.augmentedScore size factor index ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro index index_mem
    exact packing.augmentedScore_finite size_lower index
  have sum_point_bound : (∑ index, packing.augmentedScore size factor index) +
      NagamochiAugmentedResource.measure size {point} ≤
        NagamochiAugmentedResource.measure size univ := by
    rw [packing.augmentedScore_sum_eq_union (zero_lt_one.trans factor_gt_one),
      ← measure_union separated (measurableSet_singleton point)]
    exact measure_mono (subset_univ _)
  have real_bound := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top mass_finite sum_point_bound) mass_finite).mpr sum_point_bound
  rw [ENNReal.toReal_add sum_finite singleton_finite,
    ENNReal.toReal_sum (fun index _ => packing.augmentedScore_finite size_lower index),
    NagamochiAugmentedResource.mass_toReal_squareMinusTwo size_lower] at real_bound
  have point_real := (ENNReal.toReal_le_toReal (by finiteness) singleton_finite).mpr point_mass
  norm_num at point_real
  have score_lower := (packing.squareMinusTwo_augmentedScore_budget size_lower
    factor_gt_one factor_at_most scaled_side_le).1
  linarith

theorem Packing.squareMinusTwo_cornerPoint_has_owner
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (kind : NagamochiResource.CornerPoint) :
    ∃ index, NagamochiResource.cornerPoint size kind ∈
      (packing.squares index).dilatedInteriorRegion factor := by
  apply packing.squareMinusTwo_heavyPoint_has_owner size_lower factor_gt_one factor_at_most
    scaled_side_le (NagamochiResource.cornerPoint size kind)
  have bound := NagamochiAugmentedResource.cornerPoints_lower_bound_of_mem
    (size := size) kind (measurableSet_singleton _) (mem_singleton _)
  rw [NagamochiAugmentedResource.measure_apply]
  exact (bound.trans (le_add_of_nonneg_left bot_le)).trans (le_add_of_nonneg_right bot_le)

theorem Packing.squareMinusTwo_edgePoint_has_owner
    {size coordinate : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint) :
    ∃ index, NagamochiResource.edgePoint size coordinate kind ∈
      (packing.squares index).dilatedInteriorRegion factor := by
  apply packing.squareMinusTwo_heavyPoint_has_owner size_lower factor_gt_one factor_at_most
    scaled_side_le (NagamochiResource.edgePoint size coordinate kind)
  have bound := NagamochiResource.edgePoints_lower_bound_of_mem
    kind coordinate_mem (measurableSet_singleton _) (mem_singleton _)
  rw [NagamochiAugmentedResource.measure_apply]
  exact bound.trans (le_add_of_nonneg_left bot_le)

theorem Packing.squareMinusTwo_augmentedScore_lt_seven_fifths
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (owner : Fin (size * size - 2)) :
    packing.augmentedScore size factor owner < 7 / 5 := by
  classical
  have count_lower : 2 ≤ size * size - 2 := by
    have square_lower := Nat.mul_le_mul size_lower size_lower
    omega
  have other_nonempty : ((Finset.univ : Finset (Fin (size * size - 2))).erase owner).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have score_gt_one : ∀ index, 1 < (packing.augmentedScore size factor index).toReal := by
    intro index
    simpa using (ENNReal.toReal_lt_toReal (by simp)
      (packing.augmentedScore_finite size_lower index)).mpr
        (packing.augmentedScore_gt_one size_lower factor_gt_one factor_at_most scaled_side_le index)
  have others_lower : ((size * size - 2 : ℕ) : ℝ) - 1 <
      ∑ index ∈ (Finset.univ : Finset (Fin (size * size - 2))).erase owner,
        (packing.augmentedScore size factor index).toReal := by
    calc
      ((size * size - 2 : ℕ) : ℝ) - 1 =
          ∑ index ∈ (Finset.univ : Finset (Fin (size * size - 2))).erase owner, (1 : ℝ) := by
        simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ size * size - 2)]
      _ < _ := Finset.sum_lt_sum (fun index _ => (score_gt_one index).le)
        ⟨other_nonempty.choose, other_nonempty.choose_spec, score_gt_one _⟩
  have sum_identity := Finset.sum_erase_add Finset.univ
    (fun index => (packing.augmentedScore size factor index).toReal) (Finset.mem_univ owner)
  have total_upper := (packing.squareMinusTwo_augmentedScore_budget size_lower
    factor_gt_one factor_at_most scaled_side_le).2
  apply (ENNReal.toReal_lt_toReal (packing.augmentedScore_finite size_lower owner) (by finiteness)).mp
  norm_num
  linarith

theorem Packing.squareMinusTwo_not_two_bottom_points
    {size coordinate : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (coordinate_lower : 2 ≤ coordinate) (coordinate_upper : coordinate + 1 ≤ size - 2)
    (owner : Fin (size * size - 2)) :
    ¬(![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ (packing.squares owner).dilatedInteriorRegion factor ∧
      ![((coordinate + 1 : ℕ) : ℝ), (9 / 10 : ℝ)] ∈ (packing.squares owner).dilatedInteriorRegion factor) := by
  rintro ⟨first_mem, second_mem⟩
  have score_lower := Nagamochi.augmentedScore_gt_three_halves_of_two_bottom_points
    (packing.squares owner) (packing.fits owner) factor_gt_one factor_at_most
    ((packing.squares owner).dilatedInteriorRegion_subset_containerRegion
      (packing.fits owner) (zero_lt_one.trans factor_gt_one).le scaled_side_le)
    coordinate_lower coordinate_upper first_mem second_mem
  have score_upper := packing.squareMinusTwo_augmentedScore_lt_seven_fifths size_lower
    factor_gt_one factor_at_most scaled_side_le owner
  have contradiction : (3 / 2 : ENNReal) < 7 / 5 := score_lower.trans score_upper
  have real_contradiction := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr contradiction
  norm_num at real_contradiction

lemma Packing.dilatedPoint_owner_unique
    {squareCount : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (factor_positive : 0 < factor) {point : Plane} {first second : Fin squareCount}
    (first_mem : point ∈ (packing.squares first).dilatedInteriorRegion factor)
    (second_mem : point ∈ (packing.squares second).dilatedInteriorRegion factor) :
    first = second := by
  by_contra different
  exact Set.disjoint_left.mp
    (PlacedSquare.disjoint_dilatedInteriorRegion
      (packing.disjoint first second different) factor_positive.ne') first_mem second_mem

theorem Packing.squareMinusTwo_cornerPoint_has_unique_owner
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (kind : NagamochiResource.CornerPoint) :
    ∃! index, NagamochiResource.cornerPoint size kind ∈
      (packing.squares index).dilatedInteriorRegion factor := by
  obtain ⟨owner, contained⟩ := packing.squareMinusTwo_cornerPoint_has_owner size_lower
    factor_gt_one factor_at_most scaled_side_le kind
  exact ⟨owner, contained, fun other other_contained =>
    packing.dilatedPoint_owner_unique (zero_lt_one.trans factor_gt_one) other_contained contained⟩

theorem Packing.squareMinusTwo_edgePoint_has_unique_owner
    {size coordinate : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (kind : NagamochiResource.EdgePoint) :
    ∃! index, NagamochiResource.edgePoint size coordinate kind ∈
      (packing.squares index).dilatedInteriorRegion factor := by
  obtain ⟨owner, contained⟩ := packing.squareMinusTwo_edgePoint_has_owner size_lower
    factor_gt_one factor_at_most scaled_side_le coordinate_mem kind
  exact ⟨owner, contained, fun other other_contained =>
    packing.dilatedPoint_owner_unique (zero_lt_one.trans factor_gt_one) other_contained contained⟩

theorem Packing.exists_squareMinusTwo_markedPoint_ownership
    {size : ℕ} {side : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (side_lt_size : side < size) :
    ∃ factor : ℝ, 1 < factor ∧ factor ≤ 101 / 100 ∧ factor * side ≤ size ∧
      (∀ kind : NagamochiResource.CornerPoint,
        ∃! index, NagamochiResource.cornerPoint size kind ∈
          (packing.squares index).dilatedInteriorRegion factor) ∧
      (∀ coordinate ∈ Finset.Icc 2 (size - 2), ∀ kind : NagamochiResource.EdgePoint,
        ∃! index, NagamochiResource.edgePoint size coordinate kind ∈
          (packing.squares index).dilatedInteriorRegion factor) ∧
      (∀ index, packing.augmentedScore size factor index < 7 / 5) := by
  have count_positive : 0 < size * size - 2 := by
    have square_lower := Nat.mul_le_mul size_lower size_lower
    omega
  have side_positive := packing.side_positive count_positive
  have ratio_gt_one : 1 < (size : ℝ) / side := by
    rw [lt_div_iff₀ side_positive]
    simpa using side_lt_size
  have upper_gt_one : 1 < min (101 / 100 : ℝ) ((size : ℝ) / side) :=
    lt_min (by norm_num) ratio_gt_one
  obtain ⟨factor, factor_gt_one, factor_lt_upper⟩ := exists_between upper_gt_one
  have factor_at_most : factor ≤ 101 / 100 :=
    (factor_lt_upper.trans_le (min_le_left _ _)).le
  have scaled_side_lt : factor * side < size := by
    rw [← lt_div_iff₀ side_positive]
    exact factor_lt_upper.trans_le (min_le_right _ _)
  refine ⟨factor, factor_gt_one, factor_at_most, scaled_side_lt.le, ?_, ?_, ?_⟩
  · exact fun kind => packing.squareMinusTwo_cornerPoint_has_unique_owner size_lower
      factor_gt_one factor_at_most scaled_side_lt.le kind
  · exact fun coordinate coordinate_mem kind => packing.squareMinusTwo_edgePoint_has_unique_owner
      size_lower factor_gt_one factor_at_most scaled_side_lt.le coordinate_mem kind
  · exact fun index => packing.squareMinusTwo_augmentedScore_lt_seven_fifths size_lower
      factor_gt_one factor_at_most scaled_side_lt.le index

end SquarePackingArchive
