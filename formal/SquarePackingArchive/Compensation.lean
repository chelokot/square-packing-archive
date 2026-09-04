import SquarePackingArchive.Resource

namespace SquarePackingArchive

theorem finite_scores_sum_gt_card_of_compensation
    {elementCount : ℕ} (elementCount_positive : 0 < elementCount)
    (scores : Fin elementCount → ℝ) (bad : Finset (Fin elementCount))
    (assigned : bad → Fin elementCount) (credit : bad → ℝ)
    (assigned_not_bad : ∀ origin, assigned origin ∉ bad)
    (bad_repaid : ∀ origin, 1 < scores origin.val + credit origin)
    (others_repaid : ∀ index, index ∉ bad →
      1 + ∑ origin : bad, (if assigned origin = index then credit origin else 0) < scores index) :
    (elementCount : ℝ) < ∑ index, scores index := by
  classical
  let incoming := fun index => ∑ origin : bad, if origin.val = index then credit origin else 0
  let outgoing := fun index => ∑ origin : bad, if assigned origin = index then credit origin else 0
  have incoming_at_origin (origin : bad) : incoming origin.val = credit origin := by
    dsimp [incoming]
    simp only [show ∀ other : bad, other.val = origin.val ↔ other = origin from
      fun _ => Subtype.ext_iff.symm]
    simp
  have outgoing_at_origin (origin : bad) : outgoing origin.val = 0 := by
    apply Finset.sum_eq_zero
    intro other _
    rw [if_neg]
    intro same
    exact assigned_not_bad other (same.symm ▸ origin.property)
  have incoming_at_other {index : Fin elementCount} (not_bad : index ∉ bad) : incoming index = 0 := by
    apply Finset.sum_eq_zero
    intro origin _
    rw [if_neg]
    intro same
    exact not_bad (same ▸ origin.property)
  have compensated : ∀ index, 1 < scores index + incoming index - outgoing index := by
    intro index
    by_cases index_bad : index ∈ bad
    · let origin : bad := ⟨index, index_bad⟩
      have incoming_eq := incoming_at_origin origin
      have outgoing_eq := outgoing_at_origin origin
      have score_bound := bad_repaid origin
      change incoming index = credit origin at incoming_eq
      change outgoing index = 0 at outgoing_eq
      rw [incoming_eq, outgoing_eq, sub_zero]
      exact score_bound
    · rw [incoming_at_other index_bad, add_zero]
      have score_bound := others_repaid index index_bad
      change 1 + outgoing index < scores index at score_bound
      linarith
  have incoming_sum : ∑ index, incoming index = ∑ origin : bad, credit origin := by
    dsimp [incoming]
    rw [Finset.sum_comm]
    simp
  have outgoing_sum : ∑ index, outgoing index = ∑ origin : bad, credit origin := by
    dsimp [outgoing]
    rw [Finset.sum_comm]
    simp
  have sum_identity : ∑ index, (scores index + incoming index - outgoing index) =
      ∑ index, scores index := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, incoming_sum, outgoing_sum]
    ring
  rw [← sum_identity]
  calc
    (elementCount : ℝ) = ∑ _index : Fin elementCount, (1 : ℝ) := by simp
    _ < _ := Finset.sum_lt_sum (fun index _ => (compensated index).le)
      ⟨⟨0, elementCount_positive⟩, Finset.mem_univ _, compensated _⟩

theorem finite_scores_sum_gt_card_of_capacity_compensation
    {elementCount : ℕ} (elementCount_positive : 0 < elementCount)
    (scores : Fin elementCount → ℝ) (bad : Finset (Fin elementCount))
    (assigned : bad → Fin elementCount) (credit : bad → ℝ)
    (capacity : Fin elementCount → ℕ)
    (assigned_not_bad : ∀ origin, assigned origin ∉ bad)
    (credit_nonnegative : ∀ origin, 0 ≤ credit origin)
    (bad_repaid : ∀ origin, 1 < scores origin.val + credit origin)
    (fiber_capacity : ∀ target,
      (Finset.univ.filter (fun origin : bad => assigned origin = target)).card ≤ capacity target)
    (target_repaid : ∀ origin,
      1 + (capacity (assigned origin) : ℝ) * credit origin < scores (assigned origin))
    (others_baseline : ∀ target, target ∉ bad → 1 < scores target) :
    (elementCount : ℝ) < ∑ index, scores index := by
  classical
  apply finite_scores_sum_gt_card_of_compensation elementCount_positive scores bad assigned credit
    assigned_not_bad bad_repaid
  intro target target_not_bad
  let fiber := Finset.univ.filter (fun origin : bad => assigned origin = target)
  rw [← Finset.sum_filter]
  change 1 + ∑ origin ∈ fiber, credit origin < scores target
  by_cases fiber_nonempty : fiber.Nonempty
  · obtain ⟨largest, largest_mem, maximal⟩ := fiber.exists_max_image credit fiber_nonempty
    have assigned_largest : assigned largest = target := (Finset.mem_filter.mp largest_mem).2
    have sum_bound : ∑ origin ∈ fiber, credit origin ≤ (fiber.card : ℝ) * credit largest := by
      simpa only [nsmul_eq_mul] using fiber.sum_le_card_nsmul credit (credit largest) maximal
    have capacity_bound : (fiber.card : ℝ) ≤ capacity target := by
      exact_mod_cast fiber_capacity target
    have total_bound := sum_bound.trans
      (mul_le_mul_of_nonneg_right capacity_bound (credit_nonnegative largest))
    have target_bound := target_repaid largest
    rw [assigned_largest] at target_bound
    linarith
  · have fiber_empty := Finset.not_nonempty_iff_eq_empty.mp fiber_nonempty
    simpa only [fiber_empty, Finset.sum_empty, add_zero] using others_baseline target target_not_bad

end SquarePackingArchive
