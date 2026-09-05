import SquarePackingArchive.MovingUnavoidable
import SquarePackingArchive.BoundaryUnavoidable
import SquarePackingArchive.Records.Square7

namespace SquarePackingArchive

theorem Packing.moving_interiorUnavoidable_preserves_assignment
    {Parameter : Type*} [TopologicalSpace Parameter] [PreconnectedSpace Parameter]
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (paths : Fin count → Parameter → Point) (initial : Parameter)
    (paths_continuous : ∀ index, Continuous fun parameter => (paths index parameter).toPlane)
    (unavoidable : ∀ parameter, InteriorUnavoidable (fun index => paths index parameter) side) :
    ∀ pointIndex owner,
      (packing.squares owner).InteriorContains (paths pointIndex initial) →
      ∀ parameter, (packing.squares owner).InteriorContains (paths pointIndex parameter) := by
  have assignment := packing.interiorUnavoidable_bijective_assignment
    (fun index => paths index initial) (unavoidable initial)
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
      intro index unassigned
      obtain ⟨assigned, bijective, contained⟩ := assignment
      obtain ⟨owner, owner_eq⟩ := bijective.2 index
      apply False.elim
      apply unassigned owner
      apply ((packing.squares owner).mem_interiorRegion_iff _).2
      simpa [owner_eq] using contained owner)
    (by
      intro index other owner different first_mem second_mem
      apply False.elim
      apply different
      exact packing.interiorUnavoidable_same_owner_same_point_index
        (fun index => paths index initial) (unavoidable initial) owner index other
        (((packing.squares owner).mem_interiorRegion_iff _).1 first_mem)
        (((packing.squares owner).mem_interiorRegion_iff _).1 second_mem))
  intro index owner initially_inside parameter
  apply ((packing.squares owner).mem_interiorRegion_iff (paths index parameter).toPlane).1
  exact preserved index owner
    (((packing.squares owner).mem_interiorRegion_iff _).2 initially_inside) parameter

theorem Packing.moving_interiorUnavoidable_bijective_assignment
    {Parameter : Type*} [TopologicalSpace Parameter] [PreconnectedSpace Parameter]
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (paths : Fin count → Parameter → Point) (initial : Parameter)
    (paths_continuous : ∀ index, Continuous fun parameter => (paths index parameter).toPlane)
    (unavoidable : ∀ parameter, InteriorUnavoidable (fun index => paths index parameter) side) :
    ∃ assigned : Fin count → Fin count, Function.Bijective assigned ∧
      ∀ owner parameter, (packing.squares owner).InteriorContains (paths (assigned owner) parameter) := by
  obtain ⟨assigned, bijective, contained⟩ := packing.interiorUnavoidable_bijective_assignment
    (fun index => paths index initial) (unavoidable initial)
  exact ⟨assigned, bijective, fun owner =>
    packing.moving_interiorUnavoidable_preserves_assignment paths initial paths_continuous
      unavoidable (assigned owner) owner (contained owner)⟩

theorem strictUnavoidable_interior_scaled
    {count : ℕ} {points : Fin count → Point} {side candidateSide : ℝ}
    (candidate_positive : 0 < candidateSide) (candidate_lt_side : candidateSide < side)
    (unavoidable : ∀ square : PlacedSquare, square.StrictFits side →
      ∃ index, square.Contains (points index)) :
    InteriorUnavoidable (fun index => (points index).scale (candidateSide / side)) candidateSide := by
  have factor_gt_one : 1 < side / candidateSide :=
    (lt_div_iff₀ candidate_positive).2 (by simpa using candidate_lt_side)
  intro square fits
  have strict : (square.scaleCenter (side / candidateSide)).StrictFits side := by
    simpa [candidate_positive.ne'] using square.scaleCenter_strictFits fits factor_gt_one
  obtain ⟨index, contained⟩ := unavoidable _ strict
  refine ⟨index, ?_⟩
  have scaled := square.interiorContains_scaled_of_scaleCenter_contains factor_gt_one contained
  simpa [one_div_div] using scaled

end SquarePackingArchive
