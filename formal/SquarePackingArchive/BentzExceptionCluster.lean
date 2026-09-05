import SquarePackingArchive.BentzExtraPoint

namespace SquarePackingArchive

def Packing.PointUnique
    {count pointCount : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin pointCount → Point) (index : Fin pointCount) : Prop :=
  ∃ owner, (packing.squares owner).InteriorContains (points index) ∧
    ∀ other, (packing.squares owner).InteriorContains (points other) → other = index

theorem Packing.interiorUnavoidable_exception_cluster
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin (count + 1) → Point) (unavoidable : InteriorUnavoidable points side) :
    (∃ extra, ∀ index, ¬ packing.PointUnique points index → index = extra) ∨
      (∃ owner, ∀ index, ¬ packing.PointUnique points index →
        (packing.squares owner).InteriorContains (points index)) := by
  classical
  obtain ⟨extra, unassigned_extra, pairs_extra⟩ :=
    packing.interiorUnavoidable_one_extra_exceptions points unavoidable
  have assigned_of_ne (index : Fin (count + 1)) (different : index ≠ extra) :
      ∃ owner, (packing.squares owner).InteriorContains (points index) := by
    by_contra unassigned
    push Not at unassigned
    exact different (unassigned_extra index unassigned)
  have unique_of_extra_absent (owner : Fin count) (index : Fin (count + 1))
      (inside : (packing.squares owner).InteriorContains (points index))
      (extra_absent : ¬ (packing.squares owner).InteriorContains (points extra)) :
      packing.PointUnique points index := by
    refine ⟨owner, inside, ?_⟩
    intro other other_inside
    by_contra different
    rcases pairs_extra owner other index different other_inside inside with other_extra | index_extra
    · exact extra_absent (other_extra ▸ other_inside)
    · exact extra_absent (index_extra ▸ inside)
  by_cases extra_assigned : ∃ owner, (packing.squares owner).InteriorContains (points extra)
  · obtain ⟨exceptionOwner, extra_inside⟩ := extra_assigned
    refine Or.inr ⟨exceptionOwner, ?_⟩
    intro index not_unique
    by_cases index_extra : index = extra
    · exact index_extra ▸ extra_inside
    obtain ⟨owner, inside⟩ := assigned_of_ne index index_extra
    by_cases same_owner : owner = exceptionOwner
    · exact same_owner ▸ inside
    apply False.elim
    apply not_unique
    apply unique_of_extra_absent owner index inside
    intro other_inside
    exact packing.disjoint owner exceptionOwner same_owner (points extra) ⟨other_inside, extra_inside⟩
  · refine Or.inl ⟨extra, ?_⟩
    intro index not_unique
    by_contra different
    obtain ⟨owner, inside⟩ := assigned_of_ne index different
    exact not_unique (unique_of_extra_absent owner index inside
      (fun extra_inside => extra_assigned ⟨owner, extra_inside⟩))

end SquarePackingArchive
