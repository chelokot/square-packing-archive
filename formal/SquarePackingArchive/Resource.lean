import SquarePackingArchive.Area

namespace SquarePackingArchive

open Function MeasureTheory Set

theorem Packing.squareCount_lt_resourceMass
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (resource : Measure Plane) (squareCount_positive : 0 < squareCount)
    (resource_finite : resource univ ≠ ⊤)
    (score : ∀ index, 1 < resource (packing.squares index).interiorRegion) :
    (squareCount : ENNReal) < resource univ := by
  let regions : Fin squareCount → Set Plane :=
    fun index => (packing.squares index).interiorRegion
  have regions_measurable : ∀ index, MeasurableSet (regions index) :=
    fun index => (packing.squares index).measurableSet_interiorRegion
  have regions_disjoint : Pairwise (Disjoint on regions) := by
    intro left right different
    exact PlacedSquare.disjoint_interiorRegion
      (packing.disjoint left right different)
  have score_finite : ∀ index, resource (regions index) ≠ ⊤ := by
    intro index
    exact ne_top_of_le_ne_top resource_finite (measure_mono (subset_univ _))
  have score_real : ∀ index, 1 < (resource (regions index)).toReal := by
    intro index
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by simp) (score_finite index)).mpr (score index)
  have score_sum_real :
      (squareCount : ℝ) <
        ∑ index ∈ (Finset.univ : Finset (Fin squareCount)),
          (resource (regions index)).toReal := by
    calc
      (squareCount : ℝ) =
          ∑ index ∈ (Finset.univ : Finset (Fin squareCount)), (1 : ℝ) := by simp
      _ < ∑ index ∈ (Finset.univ : Finset (Fin squareCount)),
          (resource (regions index)).toReal := by
        apply Finset.sum_lt_sum
        · intro index index_mem
          exact (score_real index).le
        · exact ⟨⟨0, squareCount_positive⟩, Finset.mem_univ _, score_real _⟩
  have sum_measure_le :
      ∑ index ∈ (Finset.univ : Finset (Fin squareCount)), resource (regions index) ≤
        resource univ := by
    calc
      _ = resource (⋃ index ∈ (Finset.univ : Finset (Fin squareCount)),
          regions index) := by
        symm
        apply measure_biUnion_finset
        · intro left left_mem right right_mem different
          exact regions_disjoint different
        · intro index index_mem
          exact regions_measurable index
      _ ≤ resource univ := measure_mono (subset_univ _)
  have sum_finite :
      ∑ index ∈ (Finset.univ : Finset (Fin squareCount)), resource (regions index) ≠
        ⊤ := ne_top_of_le_ne_top resource_finite sum_measure_le
  have sum_real_le := (ENNReal.toReal_le_toReal sum_finite resource_finite).mpr sum_measure_le
  rw [ENNReal.toReal_sum (fun index index_mem => score_finite index)] at sum_real_le
  apply (ENNReal.toReal_lt_toReal (by simp) resource_finite).mp
  rw [ENNReal.toReal_natCast]
  exact score_sum_real.trans_le sum_real_le

end SquarePackingArchive
