import SquarePackingArchive.MovingPacking

namespace SquarePackingArchive

theorem Packing.moving_interiorUnavoidable_preserves_unique_active
    {Parameter : Type*} [TopologicalSpace Parameter] [PreconnectedSpace Parameter]
    {count pointCount : ℕ} {side : ℝ} (packing : Packing count side)
    (paths : Fin pointCount → Parameter → Point) (initial : Parameter)
    (paths_continuous : ∀ index, Continuous fun parameter => (paths index parameter).toPlane)
    (unavoidable : ∀ parameter, InteriorUnavoidable (fun index => paths index parameter) side)
    (active : Fin pointCount → Prop)
    (inactive_stationary : ∀ index, ¬ active index → ∀ parameter, paths index parameter = paths index initial)
    (active_unique : ∀ index, active index → ∃ owner,
      (packing.squares owner).InteriorContains (paths index initial) ∧
        ∀ other, (packing.squares owner).InteriorContains (paths other initial) → other = index) :
    ∀ index owner,
      (packing.squares owner).InteriorContains (paths index initial) →
      ∀ parameter, (packing.squares owner).InteriorContains (paths index parameter) := by
  classical
  have preserved := moving_unavoidable_preserves_assignment
    (fun index parameter => (paths index parameter).toPlane)
    (fun owner => (packing.squares owner).interiorRegion) initial paths_continuous
    (fun owner => (packing.squares owner).isOpen_interiorRegion)
    (fun first second different => PlacedSquare.disjoint_interiorRegion
      (packing.disjoint first second different))
    (by
      intro parameter owner
      obtain ⟨index, contained⟩ := unavoidable parameter (packing.squares owner) (packing.fits owner)
      exact ⟨index, ((packing.squares owner).mem_interiorRegion_iff _).2 contained⟩)
    (by
      intro index unassigned parameter
      by_cases is_active : active index
      · obtain ⟨owner, contained, unique⟩ := active_unique index is_active
        exact False.elim (unassigned owner (((packing.squares owner).mem_interiorRegion_iff _).2 contained))
      · exact congrArg Point.toPlane (inactive_stationary index is_active parameter))
    (by
      intro index other owner different index_mem other_mem parameter
      by_cases is_active : active index
      · obtain ⟨actualOwner, contained, unique⟩ := active_unique index is_active
        have owner_eq : actualOwner = owner := by
          by_contra owners_different
          exact packing.disjoint _ _ owners_different _
            ⟨contained, ((packing.squares owner).mem_interiorRegion_iff _).1 index_mem⟩
        subst actualOwner
        exact False.elim (different (unique other
          (((packing.squares owner).mem_interiorRegion_iff _).1 other_mem)).symm)
      · exact congrArg Point.toPlane (inactive_stationary index is_active parameter))
  intro index owner initially_inside parameter
  apply ((packing.squares owner).mem_interiorRegion_iff (paths index parameter).toPlane).1
  exact preserved index owner
    (((packing.squares owner).mem_interiorRegion_iff _).2 initially_inside) parameter

end SquarePackingArchive
