import Mathlib.Topology.Connected.Clopen

namespace SquarePackingArchive

theorem moving_unavoidable_preserves_assignment
    {Parameter Space PointIndex BoxIndex : Type*}
    [TopologicalSpace Parameter] [PreconnectedSpace Parameter]
    [TopologicalSpace Space] [Finite PointIndex] [Finite BoxIndex]
    (paths : PointIndex → Parameter → Space)
    (boxes : BoxIndex → Set Space)
    (initial : Parameter)
    (paths_continuous : ∀ pointIndex, Continuous (paths pointIndex))
    (boxes_open : ∀ boxIndex, IsOpen (boxes boxIndex))
    (boxes_disjoint : Pairwise fun first second => Disjoint (boxes first) (boxes second))
    (unavoidable : ∀ parameter boxIndex,
      ∃ pointIndex, paths pointIndex parameter ∈ boxes boxIndex)
    (unassigned_stationary : ∀ pointIndex,
      (∀ boxIndex, paths pointIndex initial ∉ boxes boxIndex) →
      ∀ parameter, paths pointIndex parameter = paths pointIndex initial)
    (duplicates_stationary : ∀ pointIndex otherIndex boxIndex,
      pointIndex ≠ otherIndex →
      paths pointIndex initial ∈ boxes boxIndex →
      paths otherIndex initial ∈ boxes boxIndex →
      ∀ parameter, paths pointIndex parameter = paths pointIndex initial) :
    ∀ pointIndex boxIndex,
      paths pointIndex initial ∈ boxes boxIndex →
      ∀ parameter, paths pointIndex parameter ∈ boxes boxIndex := by
  classical
  let preserved : Set Parameter := {parameter | ∀ pointIndex boxIndex,
    paths pointIndex initial ∈ boxes boxIndex →
      paths pointIndex parameter ∈ boxes boxIndex}
  have preserved_open : IsOpen preserved := by
    have preserved_as_intersection : preserved =
        ⋂ pointIndex, ⋂ boxIndex,
          if paths pointIndex initial ∈ boxes boxIndex
          then (paths pointIndex) ⁻¹' boxes boxIndex else Set.univ := by
      ext parameter
      simp only [preserved, Set.mem_ofPred_eq, Set.mem_iInter]
      apply forall_congr'
      intro pointIndex
      apply forall_congr'
      intro boxIndex
      split_ifs <;> simp_all
    rw [preserved_as_intersection]
    apply isOpen_iInter_of_finite
    intro pointIndex
    apply isOpen_iInter_of_finite
    intro boxIndex
    split_ifs
    · exact (boxes_open boxIndex).preimage (paths_continuous pointIndex)
    · exact isOpen_univ
  have complement_open : IsOpen preservedᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro parameter not_preserved
    change ¬ (∀ pointIndex boxIndex,
      paths pointIndex initial ∈ boxes boxIndex →
        paths pointIndex parameter ∈ boxes boxIndex) at not_preserved
    push Not at not_preserved
    obtain ⟨pointIndex, boxIndex, initially_inside, now_outside⟩ := not_preserved
    obtain ⟨replacement, replacement_inside⟩ := unavoidable parameter boxIndex
    have replacement_different : pointIndex ≠ replacement := by
      intro equality
      subst replacement
      exact now_outside replacement_inside
    have replacement_initially_outside :
        paths replacement initial ∉ boxes boxIndex := by
      intro replacement_initially_inside
      have stationary := duplicates_stationary pointIndex replacement boxIndex
        replacement_different initially_inside replacement_initially_inside parameter
      exact now_outside (stationary ▸ initially_inside)
    have replacement_assigned :
        ∃ otherBox, paths replacement initial ∈ boxes otherBox := by
      by_contra no_assignment
      push Not at no_assignment
      have stationary := unassigned_stationary replacement no_assignment parameter
      exact replacement_initially_outside (stationary ▸ replacement_inside)
    obtain ⟨otherBox, replacement_initially_assigned⟩ := replacement_assigned
    have boxes_different : boxIndex ≠ otherBox := by
      intro equality
      subst otherBox
      exact replacement_initially_outside replacement_initially_assigned
    refine ⟨(paths replacement) ⁻¹' boxes boxIndex, ?_,
      (boxes_open boxIndex).preimage (paths_continuous replacement), replacement_inside⟩
    intro neighbor replacement_in_box neighbor_preserved
    have replacement_in_other : paths replacement neighbor ∈ boxes otherBox :=
      neighbor_preserved replacement otherBox replacement_initially_assigned
    exact Set.disjoint_left.mp (boxes_disjoint boxes_different)
      replacement_in_box replacement_in_other
  have preserved_all : preserved = Set.univ :=
    (show IsClopen preserved from ⟨isOpen_compl_iff.mp complement_open, preserved_open⟩).eq_univ
      ⟨initial, fun _ _ initially_inside => initially_inside⟩
  intro pointIndex boxIndex initially_inside parameter
  have parameter_preserved : parameter ∈ preserved := by rw [preserved_all]; trivial
  exact parameter_preserved pointIndex boxIndex initially_inside

end SquarePackingArchive
