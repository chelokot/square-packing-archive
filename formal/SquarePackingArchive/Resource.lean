import SquarePackingArchive.Area

namespace SquarePackingArchive

open Function MeasureTheory Set

lemma sum_scores_eq_sum_transferred_scores
    {elementCount : ℕ} (scores : Fin elementCount → ℝ)
    (transfers : Fin elementCount → Fin elementCount → ℝ) :
    ∑ index, (scores index + ∑ source, transfers source index - ∑ target, transfers index target) =
      ∑ index, scores index := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := transfers)]
  ring

theorem finite_scores_sum_gt_card_of_balanced_transfers
    {elementCount : ℕ} (elementCount_positive : 0 < elementCount)
    (scores : Fin elementCount → ℝ) (transfers : Fin elementCount → Fin elementCount → ℝ)
    (compensated_scores : ∀ index,
      1 < scores index + ∑ source, transfers source index - ∑ target, transfers index target) :
    (elementCount : ℝ) < ∑ index, scores index := by
  rw [← sum_scores_eq_sum_transferred_scores scores transfers]
  calc
    (elementCount : ℝ) = ∑ _index : Fin elementCount, (1 : ℝ) := by simp
    _ < _ := Finset.sum_lt_sum (fun index _ => (compensated_scores index).le)
      ⟨⟨0, elementCount_positive⟩, Finset.mem_univ _, compensated_scores _⟩

lemma finiteFamily_sum_resource_le_mass
    {elementCount : ℕ} (resource : Measure Plane)
    (regions : Fin elementCount → Set Plane)
    (regions_measurable : ∀ index, MeasurableSet (regions index))
    (regions_disjoint : Pairwise (Disjoint on regions)) :
    ∑ index, resource (regions index) ≤ resource univ := by
  have union_identity :
      ∑ index, resource (regions index) =
        resource (⋃ index ∈ (Finset.univ : Finset (Fin elementCount)), regions index) := by
    symm
    apply measure_biUnion_finset
    · intro left _ right _ different
      exact regions_disjoint different
    · intro index _
      exact regions_measurable index
  rw [union_identity]
  exact measure_mono (subset_univ _)

theorem finiteFamily_real_score_sum_le_mass
    {elementCount : ℕ} (resource : Measure Plane)
    (resource_finite : resource univ ≠ ⊤)
    (regions : Fin elementCount → Set Plane)
    (regions_measurable : ∀ index, MeasurableSet (regions index))
    (regions_disjoint : Pairwise (Disjoint on regions)) :
    ∑ index, (resource (regions index)).toReal ≤ (resource univ).toReal := by
  have score_finite : ∀ index, resource (regions index) ≠ ⊤ :=
    fun _ => ne_top_of_le_ne_top resource_finite (measure_mono (subset_univ _))
  have sum_bound := finiteFamily_sum_resource_le_mass resource regions regions_measurable regions_disjoint
  have sum_finite := ne_top_of_le_ne_top resource_finite sum_bound
  have real_bound := (ENNReal.toReal_le_toReal sum_finite resource_finite).mpr sum_bound
  rwa [ENNReal.toReal_sum (fun index _ => score_finite index)] at real_bound

theorem finiteFamily_card_lt_resourceMass_of_balanced_transfers
    {elementCount : ℕ} (resource : Measure Plane)
    (elementCount_positive : 0 < elementCount)
    (resource_finite : resource univ ≠ ⊤)
    (regions : Fin elementCount → Set Plane)
    (regions_measurable : ∀ index, MeasurableSet (regions index))
    (regions_disjoint : Pairwise (Disjoint on regions))
    (transfers : Fin elementCount → Fin elementCount → ℝ)
    (compensated_scores : ∀ index,
      1 < (resource (regions index)).toReal +
        ∑ source, transfers source index - ∑ target, transfers index target) :
    (elementCount : ENNReal) < resource univ := by
  have score_sum_strict := finite_scores_sum_gt_card_of_balanced_transfers elementCount_positive
    (fun index => (resource (regions index)).toReal) transfers compensated_scores
  have score_sum_bound := finiteFamily_real_score_sum_le_mass resource resource_finite regions
    regions_measurable regions_disjoint
  apply (ENNReal.toReal_lt_toReal (by simp) resource_finite).mp
  rw [ENNReal.toReal_natCast]
  exact score_sum_strict.trans_le score_sum_bound

theorem finiteFamily_card_lt_resourceMass
    {elementCount : ℕ} (resource : Measure Plane)
    (elementCount_positive : 0 < elementCount)
    (resource_finite : resource univ ≠ ⊤)
    (regions : Fin elementCount → Set Plane)
    (regions_measurable : ∀ index, MeasurableSet (regions index))
    (regions_disjoint : Pairwise (Disjoint on regions))
    (score : ∀ index, 1 < resource (regions index)) :
    (elementCount : ENNReal) < resource univ := by
  have score_finite : ∀ index, resource (regions index) ≠ ⊤ := by
    intro index
    exact ne_top_of_le_ne_top resource_finite (measure_mono (subset_univ _))
  have score_real : ∀ index, 1 < (resource (regions index)).toReal := by
    intro index
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by simp) (score_finite index)).mpr (score index)
  have score_sum_real :
      (elementCount : ℝ) <
        ∑ index ∈ (Finset.univ : Finset (Fin elementCount)),
          (resource (regions index)).toReal := by
    calc
      (elementCount : ℝ) =
          ∑ index ∈ (Finset.univ : Finset (Fin elementCount)), (1 : ℝ) := by simp
      _ < ∑ index ∈ (Finset.univ : Finset (Fin elementCount)),
          (resource (regions index)).toReal := by
        apply Finset.sum_lt_sum
        · intro index index_mem
          exact (score_real index).le
        · exact ⟨⟨0, elementCount_positive⟩, Finset.mem_univ _, score_real _⟩
  have sum_measure_le := finiteFamily_sum_resource_le_mass resource regions regions_measurable regions_disjoint
  have sum_finite :
      ∑ index ∈ (Finset.univ : Finset (Fin elementCount)), resource (regions index) ≠
        ⊤ := ne_top_of_le_ne_top resource_finite sum_measure_le
  have sum_real_le := (ENNReal.toReal_le_toReal sum_finite resource_finite).mpr sum_measure_le
  rw [ENNReal.toReal_sum (fun index index_mem => score_finite index)] at sum_real_le
  apply (ENNReal.toReal_lt_toReal (by simp) resource_finite).mp
  rw [ENNReal.toReal_natCast]
  exact score_sum_real.trans_le sum_real_le

theorem Packing.squareCount_lt_resourceMass
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (resource : Measure Plane) (squareCount_positive : 0 < squareCount)
    (resource_finite : resource univ ≠ ⊤)
    (score : ∀ index, 1 < resource (packing.squares index).interiorRegion) :
    (squareCount : ENNReal) < resource univ := by
  apply finiteFamily_card_lt_resourceMass resource squareCount_positive resource_finite
    (fun index => (packing.squares index).interiorRegion)
  · exact fun index => (packing.squares index).measurableSet_interiorRegion
  · intro left right different
    exact PlacedSquare.disjoint_interiorRegion
      (packing.disjoint left right different)
  · exact score

end SquarePackingArchive
