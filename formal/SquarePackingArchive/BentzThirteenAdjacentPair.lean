import SquarePackingArchive.BentzThirteenSymmetry

namespace SquarePackingArchive.BentzThirteen

structure AdjacentPair (family : Family) where
  first : Fin 13
  second : Fin 13
  first_restricted : family.Restricted first 0
  second_restricted : family.Restricted second 1
  second_corner_missing : ¬ (family.squares second).Contains ⟨1, 1⟩

namespace AdjacentPair

theorem different {family : Family} (pair : AdjacentPair family) : pair.first ≠ pair.second :=
  family.restricted_owner_ne pair.first_restricted pair.second_restricted (by decide)

theorem first_anchor {family : Family} (pair : AdjacentPair family) :
    (family.squares pair.first).Contains ⟨1, 457 / 500⟩ :=
  (pair.first_restricted 0).mpr rfl

theorem second_anchor {family : Family} (pair : AdjacentPair family) :
    (family.squares pair.second).Contains ⟨457 / 500, 1⟩ :=
  (pair.second_restricted 1).mpr rfl

theorem first_segment {family : Family} (pair : AdjacentPair family) {horizontal : ℝ}
    (bounds : 28 / 25 ≤ horizontal ∧ horizontal ≤ 87 / 50) :
    (family.squares pair.first).Contains ⟨horizontal, 1⟩ :=
  corner_restricted_horizontal_segment (family.fits pair.first) pair.first_restricted bounds

theorem first_lower {family : Family} (pair : AdjacentPair family) :
    (family.squares pair.first).Contains ⟨187 / 100, 19 / 25⟩ :=
  corner_restricted_lower_point (family.fits pair.first) pair.first_restricted

theorem second_segment {family : Family} (pair : AdjacentPair family) {vertical : ℝ}
    (bounds : 28 / 25 ≤ vertical ∧ vertical ≤ 87 / 50) :
    (family.squares pair.second).Contains ⟨1, vertical⟩ := by
  have restricted : family.swap.Restricted pair.second 0 := pair.second_restricted.swap
  have inside := corner_restricted_horizontal_segment (family.swap.fits pair.second) restricted bounds
  simpa [Point.swap] using inside

theorem second_extended {family : Family} (pair : AdjacentPair family) :
    (family.squares pair.second).Contains ⟨1, 91 / 50⟩ ∧
      (family.squares pair.second).Contains ⟨19 / 25, 49 / 25⟩ := by
  have restricted : family.swap.Restricted pair.second 0 := pair.second_restricted.swap
  have missing : ¬ (family.swap.squares pair.second).Contains ⟨1, 1⟩ := by
    simpa [Point.swap] using pair.second_corner_missing
  have inside := lemma11_replacements (family.swap.fits pair.second) restricted missing
  simpa [Point.swap] using inside

theorem exists_uncovered {family : Family} (pair : AdjacentPair family)
    {count : ℕ} (points : Fin count → Point) (small : count < 21)
    (first_six : 6 ≤ (family.covered points pair.first).card)
    (second_four : 4 ≤ (family.covered points pair.second).card) :
    ∃ owner, owner ≠ pair.first ∧ owner ≠ pair.second ∧
      ∀ index, ¬ (family.squares owner).Contains (points index) := by
  classical
  obtain ⟨owner, missing⟩ := family.exists_uncovered_of_weights points
    (fun owner => 1 + (if owner = pair.first then 5 else 0) + (if owner = pair.second then 3 else 0))
    (by simpa [Finset.sum_add_distrib] using small) (by
      intro owner nonempty
      by_cases first_eq : owner = pair.first
      · subst owner
        simpa [pair.different] using first_six
      by_cases second_eq : owner = pair.second
      · subst owner
        simpa [Ne.symm pair.different] using second_four
      simpa [first_eq, second_eq] using Finset.card_pos.mpr nonempty)
  have empty : (family.covered points owner).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro index member
    exact missing index ((family.mem_covered points owner index).mp member)
  refine ⟨owner, ?_, ?_, missing⟩
  · intro same; rw [same] at empty; omega
  · intro same; rw [same] at empty; omega

theorem capacity_contradiction {family : Family} (pair : AdjacentPair family)
    {count selected : ℕ} (points : Fin count → Point)
    (unavoidable : Unavoidable points 4) (small : count < 20 + selected)
    (selected_positive : 0 < selected) (third : Fin 13)
    (third_first : third ≠ pair.first) (third_second : third ≠ pair.second)
    (first_six : 6 ≤ (family.covered points pair.first).card)
    (second_four : 4 ≤ (family.covered points pair.second).card)
    (third_selected : selected ≤ (family.covered points third).card) : False := by
  classical
  have lower (owner : Fin 13) :
      1 + (if owner = pair.first then 5 else 0) + (if owner = pair.second then 3 else 0) +
        (if owner = third then selected - 1 else 0) ≤ (family.covered points owner).card := by
    by_cases first_eq : owner = pair.first
    · subst owner
      simpa [pair.different, Ne.symm third_first] using first_six
    by_cases second_eq : owner = pair.second
    · subst owner
      simpa [Ne.symm pair.different, Ne.symm third_second] using second_four
    by_cases third_eq : owner = third
    · subst owner
      simp only [third_first, third_second, ↓reduceIte, add_zero]
      omega
    simpa [first_eq, second_eq, third_eq] using family.covered_positive points unavoidable owner
  have bound := family.capacity points _ lower
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at bound
  omega

end AdjacentPair

theorem adjacent_pair_exists (family : Family) (first second : Fin 13)
    (first_restricted : family.Restricted first 0)
    (second_restricted : family.Restricted second 1) :
    ∃ oriented : Family, Nonempty (AdjacentPair oriented) := by
  by_cases missing : ¬ (family.squares second).Contains ⟨1, 1⟩
  · exact ⟨family, ⟨first, second, first_restricted, second_restricted, missing⟩⟩
  have first_missing : ¬ (family.squares first).Contains ⟨1, 1⟩ := by
    intro inside
    exact family.disjoint first second
      (family.restricted_owner_ne first_restricted second_restricted (by decide)) _
      ⟨inside, not_not.mp missing⟩
  refine ⟨family.swap, ⟨second, first, second_restricted.swap, first_restricted.swap, ?_⟩⟩
  simpa [Point.swap] using first_missing

end SquarePackingArchive.BentzThirteen
