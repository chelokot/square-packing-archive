import SquarePackingArchive.Area

namespace SquarePackingArchive.Nagamochi

open Set

theorem disjoint_convex_regions_cannot_cross_above_baseline
    {firstRegion secondRegion : Set Plane} {left right baseline firstHeight secondHeight : ℝ}
    (first_convex : Convex ℝ firstRegion) (second_convex : Convex ℝ secondRegion)
    (regions_disjoint : Disjoint firstRegion secondRegion)
    (first_anchor : ![left, baseline] ∈ firstRegion)
    (first_crossing : ![right, firstHeight] ∈ firstRegion)
    (second_anchor : ![right, baseline] ∈ secondRegion)
    (second_crossing : ![left, secondHeight] ∈ secondRegion)
    (first_above : baseline ≤ firstHeight) (second_above : baseline ≤ secondHeight) :
    False := by
  by_cases first_on_baseline : firstHeight = baseline
  · subst firstHeight
    exact Set.disjoint_left.mp regions_disjoint first_crossing second_anchor
  have denominator_positive : 0 < (firstHeight - baseline) + (secondHeight - baseline) := by
    have first_strict : baseline < firstHeight := lt_of_le_of_ne first_above (Ne.symm first_on_baseline)
    linarith
  let firstWeight := (firstHeight - baseline) / ((firstHeight - baseline) + (secondHeight - baseline))
  let secondWeight := (secondHeight - baseline) / ((firstHeight - baseline) + (secondHeight - baseline))
  have first_nonnegative : 0 ≤ firstWeight := div_nonneg (sub_nonneg.mpr first_above) denominator_positive.le
  have second_nonnegative : 0 ≤ secondWeight := div_nonneg (sub_nonneg.mpr second_above) denominator_positive.le
  have weights_sum : firstWeight + secondWeight = 1 := by
    dsimp [firstWeight, secondWeight]
    rw [← add_div, div_self denominator_positive.ne']
  have first_intersection := first_convex first_anchor first_crossing first_nonnegative
    second_nonnegative weights_sum
  have second_intersection := second_convex second_anchor second_crossing second_nonnegative
    first_nonnegative (by linarith : secondWeight + firstWeight = 1)
  have same_intersection :
      firstWeight • ![left, baseline] + secondWeight • ![right, firstHeight] =
        secondWeight • ![right, baseline] + firstWeight • ![left, secondHeight] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [firstWeight, secondWeight, Pi.add_apply, smul_eq_mul] <;>
      field_simp <;> ring
  rw [same_intersection] at first_intersection
  exact Set.disjoint_left.mp regions_disjoint first_intersection second_intersection

theorem finite_boundary_chain_has_reversal
    {length : ℕ} (pointsRight : Fin (length + 1) → Prop)
    (first_right : pointsRight 0) (last_left : ¬pointsRight (Fin.last length)) :
    ∃ index : Fin length, pointsRight index.castSucc ∧ ¬pointsRight index.succ := by
  classical
  by_contra no_reversal
  have all_right : ∀ index, pointsRight index := by
    intro index
    induction index using Fin.induction with
    | zero => exact first_right
    | succ index preceding =>
      by_contra following
      exact no_reversal ⟨index, preceding, following⟩
  exact last_left (all_right _)

theorem adjacent_neighbor_has_two_cycle
    {length : ℕ} (neighbor : Fin (length + 1) → Fin (length + 1))
    (adjacent : ∀ index, (neighbor index).val + 1 = index.val ∨
      index.val + 1 = (neighbor index).val) :
    ∃ index : Fin length, neighbor index.castSucc = index.succ ∧
      neighbor index.succ = index.castSucc := by
  have first_right : (0 : Fin (length + 1)).val < (neighbor 0).val := by
    have first_adjacent := adjacent 0
    simp only [Fin.val_zero] at first_adjacent ⊢
    omega
  have last_left : ¬(Fin.last length).val < (neighbor (Fin.last length)).val := by
    have neighbor_bound := (neighbor (Fin.last length)).isLt
    simp only [Fin.val_last]
    omega
  obtain ⟨index, moves_right, moves_left⟩ := finite_boundary_chain_has_reversal
    (fun index => index.val < (neighbor index).val) first_right last_left
  refine ⟨index, ?_, ?_⟩
  · apply Fin.ext
    have neighbor_adjacent := adjacent index.castSucc
    simp only [Fin.val_castSucc, Fin.val_succ] at moves_right neighbor_adjacent ⊢
    omega
  · apply Fin.ext
    have neighbor_adjacent := adjacent index.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at moves_left neighbor_adjacent ⊢
    omega

theorem no_finite_disjoint_convex_neighbor_chain
    {length : ℕ} (regions : Fin (length + 1) → Set Plane)
    (positions : Fin (length + 1) → ℝ) (baseline : ℝ)
    (regions_convex : ∀ index, Convex ℝ (regions index))
    (adjacent_disjoint : ∀ index : Fin length,
      Disjoint (regions index.castSucc) (regions index.succ))
    (anchors : ∀ index, ![positions index, baseline] ∈ regions index)
    (crosses_neighbor : ∀ index, ∃ neighbor : Fin (length + 1),
      (neighbor.val + 1 = index.val ∨ index.val + 1 = neighbor.val) ∧
        ∃ height : ℝ, baseline ≤ height ∧ ![positions neighbor, height] ∈ regions index) :
    False := by
  classical
  let neighbor := fun index => (crosses_neighbor index).choose
  have adjacent : ∀ index, (neighbor index).val + 1 = index.val ∨
      index.val + 1 = (neighbor index).val := fun index => (crosses_neighbor index).choose_spec.1
  obtain ⟨index, first_neighbor, second_neighbor⟩ := adjacent_neighbor_has_two_cycle neighbor adjacent
  obtain ⟨firstHeight, first_above, first_crossing⟩ := (crosses_neighbor index.castSucc).choose_spec.2
  obtain ⟨secondHeight, second_above, second_crossing⟩ := (crosses_neighbor index.succ).choose_spec.2
  change ![positions (neighbor index.castSucc), firstHeight] ∈ regions index.castSucc at first_crossing
  change ![positions (neighbor index.succ), secondHeight] ∈ regions index.succ at second_crossing
  rw [first_neighbor] at first_crossing
  rw [second_neighbor] at second_crossing
  exact disjoint_convex_regions_cannot_cross_above_baseline
    (regions_convex index.castSucc) (regions_convex index.succ) (adjacent_disjoint index)
    (anchors index.castSucc) first_crossing (anchors index.succ) second_crossing first_above second_above

end SquarePackingArchive.Nagamochi
