import SquarePackingArchive.Unavoidable

namespace SquarePackingArchive

theorem Packing.interiorUnavoidable_one_extra_assignment
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (unavoidable : InteriorUnavoidable points side) :
    ∃ extra : Fin (count + 1), ∃ assigned : Fin count → Fin (count + 1),
      Function.Bijective (Fin.cons extra assigned) ∧
        ∀ owner, (packing.squares owner).InteriorContains (points (assigned owner)) := by
  classical
  have some_point (owner : Fin count) := unavoidable (packing.squares owner) (packing.fits owner)
  let assigned := fun owner => (some_point owner).choose
  have contained (owner : Fin count) :
      (packing.squares owner).InteriorContains (points (assigned owner)) := (some_point owner).choose_spec
  have injective : Function.Injective assigned := by
    intro first second same
    by_contra different
    exact packing.disjoint first second different (points (assigned first))
      ⟨contained first, by rw [same]; exact contained second⟩
  have not_surjective : ¬ Function.Surjective assigned := by
    intro surjective
    have cardinality := Fintype.card_le_of_surjective assigned surjective
    simp only [Fintype.card_fin] at cardinality
    omega
  simp only [Function.Surjective, not_forall, not_exists] at not_surjective
  obtain ⟨extra, missing⟩ := not_surjective
  have extra_not_in_range : extra ∉ Set.range assigned := by
    rintro ⟨owner, equality⟩
    exact missing owner equality
  have extension_injective := Fin.cons_injective_of_injective extra_not_in_range injective
  exact ⟨extra, assigned,
    ⟨extension_injective, Finite.surjective_of_injective extension_injective⟩, contained⟩

theorem Packing.one_extra_assignment_unique_nonextra
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point)
    (extra : Fin (count + 1)) (assigned : Fin count → Fin (count + 1))
    (assignment_bijective : Function.Bijective (Fin.cons extra assigned))
    (assigned_inside : ∀ owner, (packing.squares owner).InteriorContains (points (assigned owner)))
    (owner : Fin count) (index : Fin (count + 1)) (not_extra : index ≠ extra)
    (inside : (packing.squares owner).InteriorContains (points index)) :
    index = assigned owner := by
  obtain ⟨source, source_eq⟩ := assignment_bijective.2 index
  refine Fin.cases ?_ (fun selected => ?_) source source_eq
  · intro extra_eq
    exact False.elim (not_extra extra_eq.symm)
  · intro selected_eq
    change assigned selected = index at selected_eq
    have owner_eq : selected = owner := by
      by_contra different
      exact packing.disjoint selected owner different (points index)
        ⟨by rw [← selected_eq]; exact assigned_inside selected, inside⟩
    simpa [owner_eq] using selected_eq.symm

theorem Packing.interiorUnavoidable_one_extra_exceptions
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (unavoidable : InteriorUnavoidable points side) :
    ∃ extra : Fin (count + 1),
      (∀ index, (∀ owner, ¬ (packing.squares owner).InteriorContains (points index)) → index = extra) ∧
      (∀ owner first second, first ≠ second →
        (packing.squares owner).InteriorContains (points first) →
        (packing.squares owner).InteriorContains (points second) →
        first = extra ∨ second = extra) := by
  obtain ⟨extra, assigned, bijective, inside⟩ :=
    packing.interiorUnavoidable_one_extra_assignment points unavoidable
  refine ⟨extra, ?_, ?_⟩
  · intro index unassigned
    obtain ⟨source, source_eq⟩ := bijective.2 index
    refine Fin.cases ?_ (fun owner => ?_) source source_eq
    · intro extra_eq
      exact extra_eq.symm
    · intro assigned_eq
      change assigned owner = index at assigned_eq
      exact False.elim (unassigned owner (by rw [← assigned_eq]; exact inside owner))
  · intro owner first second different first_inside second_inside
    by_cases first_extra : first = extra
    · exact Or.inl first_extra
    by_cases second_extra : second = extra
    · exact Or.inr second_extra
    apply False.elim
    apply different
    exact (packing.one_extra_assignment_unique_nonextra points extra assigned bijective inside owner
      first first_extra first_inside).trans
      (packing.one_extra_assignment_unique_nonextra points extra assigned bijective inside owner
        second second_extra second_inside).symm

end SquarePackingArchive
