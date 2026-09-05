import SquarePackingArchive.Records.Square13
import SquarePackingArchive.PackingPointCapacity

namespace SquarePackingArchive.BentzThirteen

structure Family where
  squares : Fin 13 → PlacedSquare
  fits : ∀ owner, (squares owner).Fits 4
  disjoint : ∀ first second, first ≠ second → ∀ point,
    ¬ ((squares first).Contains point ∧ (squares second).Contains point)

namespace Family

noncomputable def covered {count : ℕ} (family : Family)
    (points : Fin count → Point) (owner : Fin 13) : Finset (Fin count) := by
  classical
  exact Finset.univ.filter fun index => (family.squares owner).Contains (points index)

@[simp] theorem mem_covered {count : ℕ} (family : Family) (points : Fin count → Point)
    (owner : Fin 13) (index : Fin count) :
    index ∈ family.covered points owner ↔ (family.squares owner).Contains (points index) := by
  classical
  simp [covered]

theorem covered_total_le {count : ℕ} (family : Family) (points : Fin count → Point) :
    ∑ owner, (family.covered points owner).card ≤ count := by
  classical
  rw [← Finset.card_biUnion (show (↑(Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint
      (family.covered points) from by
    intro first _ second _ different
    apply Finset.disjoint_left.mpr
    intro index first_mem second_mem
    exact family.disjoint first second different (points index)
      ⟨(family.mem_covered points first index).mp first_mem,
       (family.mem_covered points second index).mp second_mem⟩)]
  exact (Finset.card_le_univ _).trans (by simp)

theorem capacity {count : ℕ} (family : Family) (points : Fin count → Point)
    (weights : Fin 13 → ℕ)
    (lower : ∀ owner, weights owner ≤ (family.covered points owner).card) :
    ∑ owner, weights owner ≤ count :=
  (Finset.sum_le_sum (fun owner _ => lower owner)).trans (family.covered_total_le points)

theorem covered_positive {count : ℕ} (family : Family) (points : Fin count → Point)
    (unavoidable : Unavoidable points 4) (owner : Fin 13) :
    1 ≤ (family.covered points owner).card := by
  obtain ⟨index, inside⟩ := unavoidable (family.squares owner) (family.fits owner)
  exact Finset.card_pos.mpr ⟨index, (family.mem_covered points owner index).mpr inside⟩

theorem exists_uncovered_of_weights {count : ℕ} (family : Family) (points : Fin count → Point)
    (weights : Fin 13 → ℕ) (large : count < ∑ owner, weights owner)
    (lower : ∀ owner, (family.covered points owner).Nonempty →
      weights owner ≤ (family.covered points owner).card) :
    ∃ owner, ∀ index, ¬ (family.squares owner).Contains (points index) := by
  classical
  by_contra! all_hit
  apply (not_lt_of_ge (family.capacity points weights ?_)) large
  intro owner
  obtain ⟨index, inside⟩ := all_hit owner
  exact lower owner ⟨index, (family.mem_covered points owner index).mpr inside⟩

def Restricted (family : Family) (owner : Fin 13) (anchor : Fin 16) : Prop :=
  ∀ index, (family.squares owner).Contains (Records.Square13.initialPoints index) ↔ index = anchor

theorem covered_card_lower {count : ℕ} (family : Family) (points : Fin count → Point)
    (owner : Fin 13) (indices : Finset (Fin count))
    (inside : ∀ index ∈ indices, (family.squares owner).Contains (points index)) :
    indices.card ≤ (family.covered points owner).card := by
  apply Finset.card_le_card
  intro index member
  exact (family.mem_covered points owner index).mpr (inside index member)

theorem covered_card_of_embedding {count selected : ℕ} (family : Family) (points : Fin count → Point)
    (owner : Fin 13) (indices : Fin selected ↪ Fin count)
    (inside : ∀ index, (family.squares owner).Contains (points (indices index))) :
    selected ≤ (family.covered points owner).card := by
  classical
  have lower := family.covered_card_lower points owner (Finset.univ.image indices) (by
    intro index member
    obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp member
    exact inside source)
  simpa [Finset.card_image_of_injective _ indices.injective] using lower

theorem exists_uncovered_of_two_doubletons {count : ℕ} (family : Family)
    (points : Fin count → Point) (small : count < 15)
    (first second : Fin 13) (different : first ≠ second)
    (first_double : 2 ≤ (family.covered points first).card)
    (second_double : 2 ≤ (family.covered points second).card) :
    ∃ owner, owner ≠ first ∧ owner ≠ second ∧
      ∀ index, ¬ (family.squares owner).Contains (points index) := by
  classical
  have empty_exists : ∃ owner, (family.covered points owner).card = 0 := by
    by_contra! all_positive
    have lower (owner : Fin 13) :
        1 + (if owner = first then 1 else 0) + (if owner = second then 1 else 0) ≤
          (family.covered points owner).card := by
      have positive := all_positive owner
      split_ifs with first_eq second_eq second_eq
      · exact (different (first_eq.symm.trans second_eq)).elim
      · simpa [first_eq] using first_double
      · simpa [second_eq] using second_double
      · omega
    have bound := family.capacity points _ lower
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at bound
    omega
  obtain ⟨owner, empty⟩ := empty_exists
  refine ⟨owner, ?_, ?_, ?_⟩
  · intro same; rw [same] at empty; omega
  · intro same; rw [same] at empty; omega
  · intro index inside
    have positive := Finset.card_pos.mpr ⟨index, (family.mem_covered points owner index).mpr inside⟩
    omega

theorem contradiction_of_three_doubletons {count : ℕ} (family : Family)
    (points : Fin count → Point) (small : count < 16) (unavoidable : Unavoidable points 4)
    (first second third : Fin 13) (first_second : first ≠ second)
    (first_third : first ≠ third) (second_third : second ≠ third)
    (first_double : 2 ≤ (family.covered points first).card)
    (second_double : 2 ≤ (family.covered points second).card)
    (third_double : 2 ≤ (family.covered points third).card) : False := by
  classical
  have lower (owner : Fin 13) :
      1 + (if owner = first then 1 else 0) + (if owner = second then 1 else 0) +
        (if owner = third then 1 else 0) ≤ (family.covered points owner).card := by
    have positive := family.covered_positive points unavoidable owner
    by_cases owner_first : owner = first
    · subst owner
      simpa [first_second, first_third] using first_double
    by_cases owner_second : owner = second
    · subst owner
      simpa [Ne.symm first_second, second_third] using second_double
    by_cases owner_third : owner = third
    · subst owner
      simpa [Ne.symm first_third, Ne.symm second_third] using third_double
    simpa [owner_first, owner_second, owner_third] using positive
  have bound := family.capacity points _ lower
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at bound
  omega

theorem restricted_owner_ne (family : Family) {first second : Fin 13} {left right : Fin 16}
    (first_restricted : family.Restricted first left)
    (second_restricted : family.Restricted second right) (different : left ≠ right) : first ≠ second := by
  intro same
  have inside := (first_restricted left).mpr rfl
  rw [same] at inside
  exact different ((second_restricted left).mp inside)

theorem two_restricted_corners (family : Family) :
    ∃ first second : Fin 13, ∃ left right : Fin 16,
      left.val < 8 ∧ right.val < 8 ∧ left ≠ right ∧
        family.Restricted first left ∧ family.Restricted second right := by
  classical
  let points := Records.Square13.initialPoints
  let singles := Finset.univ.filter fun owner => (family.covered points owner).card = 1
  let singletonPoints := singles.biUnion (family.covered points)
  have singleton_card : singletonPoints.card = singles.card := by
    rw [Finset.card_biUnion (show (↑singles : Set (Fin 13)).PairwiseDisjoint (family.covered points) from by
      intro first _ second _ different
      apply Finset.disjoint_left.mpr
      intro index first_mem second_mem
      exact family.disjoint first second different (points index)
        ⟨(family.mem_covered points first index).mp first_mem,
         (family.mem_covered points second index).mp second_mem⟩)]
    calc
      _ = ∑ _owner ∈ singles, 1 := by
        apply Finset.sum_congr rfl
        intro owner member
        exact (Finset.mem_filter.mp member).2
      _ = _ := by simp
  have singles_lower : 10 ≤ singles.card := by
    have lower (owner : Fin 13) :
        2 ≤ (family.covered points owner).card +
          if (family.covered points owner).card = 1 then 1 else 0 := by
      have positive := family.covered_positive points Records.Square13.initialPoints_unavoidable owner
      split_ifs <;> omega
    have sum_lower := Finset.sum_le_sum (s := Finset.univ) (fun owner _ => lower owner)
    have sum_upper := family.covered_total_le points
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.reduceMul] at sum_lower
    have indicator : (∑ owner : Fin 13,
        if (family.covered points owner).card = 1 then 1 else 0) = singles.card := by simp [singles]
    rw [indicator] at sum_lower
    omega
  let cornerPoints := Finset.univ.filter fun index : Fin 16 => index.val < 8
  have corner_count : cornerPoints.card = 8 := by decide +kernel
  have union_count : (singletonPoints ∪ cornerPoints).card ≤ 16 :=
    (Finset.card_le_univ _).trans (by norm_num)
  have intersection_count := Finset.card_union_add_card_inter singletonPoints cornerPoints
  have two_points : 1 < (singletonPoints ∩ cornerPoints).card := by omega
  obtain ⟨left, left_mem, right, right_mem, different⟩ := Finset.one_lt_card.mp two_points
  have restricted (index : Fin 16) (member : index ∈ singletonPoints ∩ cornerPoints) :
      index.val < 8 ∧ ∃ owner, family.Restricted owner index := by
    obtain ⟨singleton_mem, corner_mem⟩ := Finset.mem_inter.mp member
    refine ⟨(Finset.mem_filter.mp corner_mem).2, ?_⟩
    obtain ⟨owner, owner_mem, index_mem⟩ := Finset.mem_biUnion.mp singleton_mem
    obtain ⟨unique, unique_eq⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp owner_mem).2
    have index_eq : index = unique := by simpa [unique_eq] using index_mem
    refine ⟨owner, fun other => ?_⟩
    rw [← family.mem_covered points owner other, unique_eq, Finset.mem_singleton, index_eq]
  obtain ⟨left_corner, first, first_restricted⟩ := restricted left left_mem
  obtain ⟨right_corner, second, second_restricted⟩ := restricted right right_mem
  exact ⟨first, second, left, right, left_corner, right_corner, different,
    first_restricted, second_restricted⟩

end Family
end SquarePackingArchive.BentzThirteen
