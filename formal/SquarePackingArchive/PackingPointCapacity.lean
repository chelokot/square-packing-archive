import SquarePackingArchive.Unavoidable

namespace SquarePackingArchive

theorem Packing.scaleCenter_closed_disjoint
    {count : ℕ} {side factor : ℝ} (packing : Packing count side)
    (factor_gt_one : 1 < factor) (first second : Fin count) (different : first ≠ second)
    (point : Point) :
    ¬ (((packing.squares first).scaleCenter factor).Contains point ∧
      ((packing.squares second).scaleCenter factor).Contains point) := by
  rintro ⟨first_mem, second_mem⟩
  exact packing.disjoint first second different (point.scale (1 / factor))
    ⟨PlacedSquare.interiorContains_scaled_of_scaleCenter_contains factor_gt_one first_mem,
      PlacedSquare.interiorContains_scaled_of_scaleCenter_contains factor_gt_one second_mem⟩

theorem Packing.exists_closed_disjoint_family_in_larger_container
    {count : ℕ} {side target : ℝ} (packing : Packing count side)
    (count_positive : 0 < count) (larger : side < target) :
    ∃ squares : Fin count → PlacedSquare,
      (∀ owner, (squares owner).Fits target) ∧
      (∀ first second, first ≠ second → ∀ point,
        ¬ ((squares first).Contains point ∧ (squares second).Contains point)) := by
  have side_positive := packing.side_positive count_positive
  have factor_gt_one : 1 < target / side :=
    (lt_div_iff₀ side_positive).2 (by simpa using larger)
  refine ⟨fun owner => (packing.squares owner).scaleCenter (target / side), ?_, ?_⟩
  · intro owner
    simpa [side_positive.ne'] using
      (packing.squares owner).scaleCenter_fits (packing.fits owner) factor_gt_one.le
  · exact packing.scaleCenter_closed_disjoint factor_gt_one

theorem disjoint_incidence_assignment
    {count : ℕ} (contains : Fin count → Fin count → Prop)
    (disjoint : ∀ first second, first ≠ second → ∀ index,
      ¬ (contains first index ∧ contains second index))
    (each_square_hit : ∀ owner, ∃ index, contains owner index) :
    ∃ assigned : Fin count → Fin count, Function.Bijective assigned ∧
      ∀ owner, contains owner (assigned owner) := by
  classical
  let assigned := fun owner => (each_square_hit owner).choose
  have contained (owner : Fin count) : contains owner (assigned owner) :=
    (each_square_hit owner).choose_spec
  have injective : Function.Injective assigned := by
    intro first second same
    by_contra different
    exact disjoint first second different (assigned first)
      ⟨contained first, by rw [same]; exact contained second⟩
  exact ⟨assigned, ⟨injective, Finite.surjective_of_injective injective⟩, contained⟩

theorem deleted_incidence_saturation
    {count : ℕ} (contains : Fin count → Fin (count + 1) → Prop)
    (disjoint : ∀ first second, first ≠ second → ∀ index,
      ¬ (contains first index ∧ contains second index))
    (deleted : Fin (count + 1))
    (each_square_hit : ∀ owner, ∃ index, index ≠ deleted ∧ contains owner index) :
    (∀ index, index ≠ deleted → ∃! owner, contains owner index) ∧
    (∀ owner first second, first ≠ deleted → second ≠ deleted →
      contains owner first → contains owner second → first = second) := by
  let remaining := fun owner index => contains owner (deleted.succAbove index)
  have remaining_hit : ∀ owner, ∃ index, remaining owner index := by
    intro owner
    obtain ⟨index, different, contained⟩ := each_square_hit owner
    obtain ⟨remaining_index, index_eq⟩ := Fin.exists_succAbove_eq different
    exact ⟨remaining_index, by simpa [remaining, index_eq] using contained⟩
  obtain ⟨assigned, bijective, contained⟩ := disjoint_incidence_assignment remaining
    (fun first second different index => disjoint first second different (deleted.succAbove index)) remaining_hit
  have owner_unique (index : Fin (count + 1)) (first second : Fin count)
      (first_mem : contains first index) (second_mem : contains second index) : first = second := by
    by_contra different
    exact disjoint first second different index ⟨first_mem, second_mem⟩
  have index_assignment (owner : Fin count) (index : Fin (count + 1))
      (different : index ≠ deleted)
      (point_mem : contains owner index) :
      index = deleted.succAbove (assigned owner) := by
    obtain ⟨remaining_index, index_eq⟩ := Fin.exists_succAbove_eq different
    obtain ⟨selected, selected_eq⟩ := bijective.2 remaining_index
    have selected_mem : contains selected index := by
      simpa [remaining, selected_eq, index_eq] using contained selected
    have owner_eq := owner_unique index selected owner selected_mem point_mem
    rw [← owner_eq, selected_eq, index_eq]
  constructor
  · intro index different
    obtain ⟨remaining_index, index_eq⟩ := Fin.exists_succAbove_eq different
    obtain ⟨owner, assigned_eq⟩ := bijective.2 remaining_index
    refine ⟨owner, ?_, ?_⟩
    · simpa [remaining, assigned_eq, index_eq] using contained owner
    · intro other other_mem
      apply owner_unique index other owner other_mem
      simpa [remaining, assigned_eq, index_eq] using contained owner
  · intro owner first second first_ne second_ne first_mem second_mem
    exact (index_assignment owner first first_ne first_mem).trans
      (index_assignment owner second second_ne second_mem).symm

theorem Packing.point_assignment_bijective
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin count → Point)
    (each_square_hit : ∀ owner, ∃ index,
      (packing.squares owner).InteriorContains (points index)) :
    ∃ assigned : Fin count → Fin count, Function.Bijective assigned ∧
      ∀ owner, (packing.squares owner).InteriorContains (points (assigned owner)) :=
  disjoint_incidence_assignment (fun owner index => (packing.squares owner).InteriorContains (points index))
    (fun first second different index => packing.disjoint first second different (points index)) each_square_hit

theorem Packing.deleted_point_saturation
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (deleted : Fin (count + 1))
    (each_square_hit : ∀ owner, ∃ index, index ≠ deleted ∧
      (packing.squares owner).InteriorContains (points index)) :
    (∀ index, index ≠ deleted → ∃! owner,
      (packing.squares owner).InteriorContains (points index)) ∧
    (∀ owner first second, first ≠ deleted → second ≠ deleted →
      (packing.squares owner).InteriorContains (points first) →
      (packing.squares owner).InteriorContains (points second) → first = second) :=
  deleted_incidence_saturation (fun owner index => (packing.squares owner).InteriorContains (points index))
    (fun first second different index => packing.disjoint first second different (points index))
    deleted each_square_hit

theorem Packing.deleted_point_saturation_of_uncovered
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (deleted : Fin (count + 1))
    (unavoidable : InteriorUnavoidable points side)
    (uncovered : ∀ owner, ¬ (packing.squares owner).InteriorContains (points deleted)) :
    (∀ index, index ≠ deleted → ∃! owner,
      (packing.squares owner).InteriorContains (points index)) ∧
    (∀ owner first second, first ≠ deleted → second ≠ deleted →
      (packing.squares owner).InteriorContains (points first) →
      (packing.squares owner).InteriorContains (points second) → first = second) := by
  apply packing.deleted_point_saturation points deleted
  intro owner
  obtain ⟨index, contained⟩ := unavoidable (packing.squares owner) (packing.fits owner)
  refine ⟨index, ?_, contained⟩
  intro equality
  exact uncovered owner (equality ▸ contained)

theorem Packing.deleted_point_saturation_of_double_coverage
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (deleted retained : Fin (count + 1))
    (unavoidable : InteriorUnavoidable points side)
    (owner : Fin count) (different : retained ≠ deleted)
    (deleted_mem : (packing.squares owner).InteriorContains (points deleted))
    (retained_mem : (packing.squares owner).InteriorContains (points retained)) :
    (∀ index, index ≠ deleted → ∃! other,
      (packing.squares other).InteriorContains (points index)) ∧
    (∀ other first second, first ≠ deleted → second ≠ deleted →
      (packing.squares other).InteriorContains (points first) →
      (packing.squares other).InteriorContains (points second) → first = second) := by
  apply packing.deleted_point_saturation points deleted
  intro other
  by_cases same : other = owner
  · exact ⟨retained, different, by simpa [same] using retained_mem⟩
  obtain ⟨index, contained⟩ := unavoidable (packing.squares other) (packing.fits other)
  refine ⟨index, ?_, contained⟩
  intro equality
  exact packing.disjoint other owner same (points deleted)
    ⟨equality ▸ contained, deleted_mem⟩

end SquarePackingArchive
