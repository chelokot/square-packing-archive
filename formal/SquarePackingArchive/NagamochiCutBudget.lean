import SquarePackingArchive.NagamochiCutSymmetry

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma innerArea_add_selectedCuts_covers_square
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (selected : Finset NagamochiResource.BoundarySide)
    (factor_positive : 0 < factor)
    (cover : ∀ point ∈ square.dilatedInteriorRegion factor,
      point ∉ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) →
      ∃ side ∈ selected,
        (boundarySideToInner side).inwardNormal point <
          (boundarySideToInner side).inwardThreshold size) :
    ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ∑ side ∈ selected, volume (boundaryCutRegion (boundarySideToInner side) size
          (square.dilatedInteriorRegion factor)) := by
  let region := square.dilatedInteriorRegion factor
  have covered : region ⊆
      (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        ⋃ side ∈ selected, boundaryCutRegion (boundarySideToInner side) size region := by
    intro point point_mem
    by_cases inner : point ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)
    · exact Or.inl ⟨point_mem, inner⟩
    · obtain ⟨side, selected_side, violated⟩ := cover point point_mem inner
      exact Or.inr (mem_iUnion.2 ⟨side, mem_iUnion.2 ⟨selected_side, point_mem, violated⟩⟩)
  rw [← square.volume_dilatedInteriorRegion factor_positive.le,
    NagamochiResource.innerArea, Measure.restrict_apply
      (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact (measure_mono covered).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _)))

lemma innerHalfArea_add_selectedCuts_covers_square
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (selected : Finset NagamochiResource.BoundarySide)
    (exceptionalSide : NagamochiResource.BoundarySide)
    (factor_positive : 0 < factor)
    (center_inside :
      (boundarySideToInner exceptionalSide).inwardThreshold size ≤
        (boundarySideToInner exceptionalSide).inwardNormal (factor • square.center.toPlane))
    (cover : ∀ point ∈ square.dilatedInteriorRegion factor,
      point ∉ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) →
      ∃ side ∈ selected,
        (boundarySideToInner side).inwardNormal point <
          (boundarySideToInner side).inwardThreshold size) :
    (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ∑ side ∈ selected.erase exceptionalSide,
          volume (boundaryCutRegion (boundarySideToInner side) size
            (square.dilatedInteriorRegion factor)) := by
  classical
  let region := square.dilatedInteriorRegion factor
  let halfSpace := {point : Plane |
    (boundarySideToInner exceptionalSide).inwardThreshold size ≤
      (boundarySideToInner exceptionalSide).inwardNormal point}
  have covered : region ∩ halfSpace ⊆
      (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        ⋃ side ∈ selected.erase exceptionalSide,
          boundaryCutRegion (boundarySideToInner side) size region := by
    rintro point ⟨point_mem, half_mem⟩
    by_cases inner : point ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)
    · exact Or.inl ⟨point_mem, inner⟩
    · obtain ⟨side, selected_side, violated⟩ := cover point point_mem inner
      have different : side ≠ exceptionalSide := by
        rintro rfl
        exact not_lt_of_ge half_mem violated
      exact Or.inr (mem_iUnion.2 ⟨side,
        mem_iUnion.2 ⟨Finset.mem_erase.mpr ⟨different, selected_side⟩, point_mem, violated⟩⟩)
  have half_bound := square.half_volume_le_volume_innerHalfSpace
    (boundarySideToInner exceptionalSide).inwardNormal factor_positive center_inside
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact half_bound.trans ((measure_mono covered).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))))

lemma score_gt_one_of_center_inner_cut_budgets
    {size : ℕ} (square : PlacedSquare) {factor : ℝ} {score : ENNReal}
    (selected : Finset NagamochiResource.BoundarySide)
    (budget : NagamochiResource.BoundarySide → ENNReal)
    (factor_gt_one : 1 < factor)
    (center_inside : factor • square.center.toPlane ∈
      Icc (fun _ => 1) (fun _ => (size : ℝ) - 1))
    (cover : ∀ point ∈ square.dilatedInteriorRegion factor,
      point ∉ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1) →
      ∃ side ∈ selected,
        (boundarySideToInner side).inwardNormal point <
          (boundarySideToInner side).inwardThreshold size)
    (available : NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
      ∑ side ∈ selected, budget side ≤ score)
    (classification : ∀ side ∈ selected,
      volume (boundaryCutRegion (boundarySideToInner side) size
        (square.dilatedInteriorRegion factor)) ≤ budget side ∨
      (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤ budget side) :
    1 < score := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have half_twice : (1 / 2 : ENNReal) * 2 = 1 := by
    rw [one_div]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have two_halves : (1 / 2 : ENNReal) * ENNReal.ofReal factor +
      (1 / 2 : ENNReal) * ENNReal.ofReal factor = ENNReal.ofReal factor := by
    calc
      _ = ((1 / 2 : ENNReal) * 2) * ENNReal.ofReal factor := by ring
      _ = _ := by rw [half_twice, one_mul]
  by_cases exists_long : ∃ side ∈ selected,
      (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤ budget side
  · obtain ⟨long_side, long_selected, long_bound⟩ := exists_long
    by_cases another_long : ∃ side ∈ selected, side ≠ long_side ∧
        (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤ budget side
    · obtain ⟨other_side, other_selected, different, other_bound⟩ := another_long
      have pair_subset : ({other_side, long_side} : Finset _) ⊆ selected := by
        intro side side_mem
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using side_mem :
          side = other_side ∨ side = long_side) with rfl | rfl
        · exact other_selected
        · exact long_selected
      have pair_bound : budget other_side + budget long_side ≤ ∑ side ∈ selected, budget side := by
        rw [← Finset.sum_pair different]
        exact Finset.sum_le_sum_of_subset_of_nonneg pair_subset (by intros; exact bot_le)
      apply (ENNReal.one_lt_ofReal.mpr factor_gt_one).trans_le
      rw [← two_halves]
      exact (add_le_add other_bound long_bound).trans
        (pair_bound.trans ((le_add_self).trans available))
    · have cuts_bound :
          (∑ side ∈ selected.erase long_side,
            volume (boundaryCutRegion (boundarySideToInner side) size
              (square.dilatedInteriorRegion factor))) ≤
          ∑ side ∈ selected.erase long_side, budget side := by
        apply Finset.sum_le_sum
        intro side side_mem
        obtain ⟨different, selected_side⟩ := Finset.mem_erase.mp side_mem
        rcases classification side selected_side with compensated | long
        · exact compensated
        · exact False.elim (another_long ⟨side, selected_side, different, long⟩)
      have half_bound := innerHalfArea_add_selectedCuts_covers_square square selected
        long_side factor_positive
        ((mem_innerRectangle_iff_inward_bounds size _).1 center_inside _) cover
      have half_factor_bound : (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤
          NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
            ∑ side ∈ selected.erase long_side, budget side :=
        (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by nlinarith)) bot_le bot_le).trans
          (half_bound.trans (add_le_add le_rfl cuts_bound))
      apply (ENNReal.one_lt_ofReal.mpr factor_gt_one).trans_le
      rw [← two_halves]
      refine (add_le_add half_factor_bound long_bound).trans ?_
      rw [add_assoc, Finset.sum_erase_add _ _ long_selected]
      exact available
  · have cuts_bound :
        (∑ side ∈ selected, volume (boundaryCutRegion (boundarySideToInner side) size
          (square.dilatedInteriorRegion factor))) ≤ ∑ side ∈ selected, budget side := by
      apply Finset.sum_le_sum
      intro side selected_side
      rcases classification side selected_side with compensated | long
      · exact compensated
      · exact False.elim (exists_long ⟨side, selected_side, long⟩)
    have area_bound := innerArea_add_selectedCuts_covers_square square selected factor_positive cover
    have square_gt_one : 1 < ENNReal.ofReal (factor ^ 2) :=
      ENNReal.one_lt_ofReal.mpr (by nlinarith)
    exact square_gt_one.trans_le (area_bound.trans ((add_le_add le_rfl cuts_bound).trans available))

end SquarePackingArchive.Nagamochi
