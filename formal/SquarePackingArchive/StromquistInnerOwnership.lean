import SquarePackingArchive.StromquistOwnership

namespace SquarePackingArchive.Stromquist.TenPoints

def swapOuter : Fin 8 → Fin 10 := ![0, 7, 6, 5, 4, 3, 2, 1]

lemma swapOuter_value (index : Fin 8) :
    points (swapOuter index) = (points index.castSucc.castSucc).swap := by
  fin_cases index <;> norm_num [swapOuter, points, Point.swap]

lemma swapOuter_outer (index : Fin 8) : (swapOuter index).val < 8 := by
  fin_cases index <;> norm_num [swapOuter]

lemma NamedFamily.inner_contains_swapped_pair
    (family : NamedFamily) {owner : Fin 10} (inner : 8 ≤ owner.val) :
    (family.squares owner).Contains (points 8).swap ∨
      (family.squares owner).Contains (points 9).swap := by
  obtain ⟨index, inside⟩ := unavoidable (family.squares owner).swap
    (((family.squares owner).swap_fits_iff side).2 (family.fits owner))
  have swapped_inside : (family.squares owner).Contains (points index).swap := by
    apply ((family.squares owner).swap_contains_iff (points index).swap).1
    simpa using inside
  by_cases outer : index.val < 8
  · let outerIndex : Fin 8 := ⟨index.val, outer⟩
    have original_inside : (family.squares owner).Contains (points (swapOuter outerIndex)) := by
      rw [swapOuter_value]
      exact swapped_inside
    have different : owner ≠ swapOuter outerIndex := by
      have bound := swapOuter_outer outerIndex
      intro equality
      have value_equality := congrArg Fin.val equality
      omega
    exact False.elim (family.excludes_other_named_point different original_inside)
  · have possibilities : index = 8 ∨ index = 9 := by
      have bound := index.isLt
      apply Or.imp (fun equality => Fin.ext equality) (fun equality => Fin.ext equality)
      norm_num
      omega
    rcases possibilities with rfl | rfl
    · exact Or.inl swapped_inside
    · exact Or.inr swapped_inside

theorem NamedFamily.owns_swapped_inner_points (family : NamedFamily) :
    ((family.squares 8).Contains (points 8).swap ∨
      (family.squares 9).Contains (points 8).swap) ∧
    ((family.squares 8).Contains (points 9).swap ∨
      (family.squares 9).Contains (points 9).swap) := by
  have first := family.inner_contains_swapped_pair (owner := 8) (by norm_num)
  have second := family.inner_contains_swapped_pair (owner := 9) (by norm_num)
  rcases first with first_lower | first_upper <;>
    rcases second with second_lower | second_upper
  · exact False.elim (family.disjoint 8 9 (by decide) _ ⟨first_lower, second_lower⟩)
  · exact ⟨Or.inl first_lower, Or.inr second_upper⟩
  · exact ⟨Or.inr second_lower, Or.inl first_upper⟩
  · exact False.elim (family.disjoint 8 9 (by decide) _ ⟨first_upper, second_upper⟩)

theorem NamedFamily.outer_excludes_swapped_inner_points
    (family : NamedFamily) {owner : Fin 10} (outer : owner.val < 8) :
    ¬ (family.squares owner).Contains (points 8).swap ∧
      ¬ (family.squares owner).Contains (points 9).swap := by
  have not_first : owner ≠ 8 := by intro equality; subst owner; norm_num at outer
  have not_second : owner ≠ 9 := by intro equality; subst owner; norm_num at outer
  obtain ⟨first, second⟩ := family.owns_swapped_inner_points
  constructor
  · rcases first with first | second
    · exact family.excludes_other not_first first
    · exact family.excludes_other not_second second
  · rcases second with first | second
    · exact family.excludes_other not_first first
    · exact family.excludes_other not_second second

end SquarePackingArchive.Stromquist.TenPoints
