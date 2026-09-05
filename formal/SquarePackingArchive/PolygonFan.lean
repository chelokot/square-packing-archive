import SquarePackingArchive.TriangleRegions

namespace SquarePackingArchive

open Fin.NatCast

lemma exists_cyclic_sign_transition {count : ℕ} [NeZero count]
    (values : Fin count → ℝ)
    (nonnegative : ∃ index, 0 ≤ values index)
    (negative : ∃ index, values index < 0) :
    ∃ index, 0 ≤ values index ∧ values (index + 1) < 0 := by
  by_contra missing
  have preserves : ∀ index, 0 ≤ values index → 0 ≤ values (index + 1) := by
    intro index current
    exact le_of_not_gt (fun next => missing ⟨index, current, next⟩)
  obtain ⟨start, start_nonnegative⟩ := nonnegative
  have all_offsets : ∀ offset : ℕ, 0 ≤ values (start + (offset : Fin count)) := by
    intro offset
    induction offset with
    | zero => simpa using start_nonnegative
    | succ offset previous =>
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using preserves _ previous
  obtain ⟨finish, finish_negative⟩ := negative
  have finish_nonnegative := all_offsets (finish - start).val
  simp only [Fin.cast_val_eq_self, add_sub_cancel] at finish_nonnegative
  exact (not_lt_of_ge finish_nonnegative) finish_negative

lemma exists_cyclic_weak_sign_transition {count : ℕ} [NeZero count]
    (values : Fin count → ℝ)
    (nonnegative : ∃ index, 0 ≤ values index)
    (nonpositive : ∃ index, values index ≤ 0) :
    ∃ index, 0 ≤ values index ∧ values (index + 1) ≤ 0 := by
  by_cases negative : ∃ index, values index < 0
  · obtain ⟨index, first, second⟩ := exists_cyclic_sign_transition values nonnegative negative
    exact ⟨index, first, second.le⟩
  · obtain ⟨finish, finish_nonpositive⟩ := nonpositive
    refine ⟨finish - 1, le_of_not_gt (fun below => negative ⟨finish - 1, below⟩), ?_⟩
    simpa only [sub_add_cancel] using finish_nonpositive

lemma Point.orientedArea_weighted_balance (first second third origin point : Point) :
    Point.orientedArea second third origin * Point.orientedArea origin first point +
      Point.orientedArea third first origin * Point.orientedArea origin second point +
      Point.orientedArea first second origin * Point.orientedArea origin third point = 0 := by
  dsimp [Point.orientedArea]
  ring

lemma Point.radial_halfplanes_have_both_signs {count : ℕ}
    (vertices : Fin count → Point) (origin point : Point)
    (first second third : Fin count)
    (first_weight : 0 < Point.orientedArea (vertices second) (vertices third) origin)
    (second_weight : 0 < Point.orientedArea (vertices third) (vertices first) origin)
    (third_weight : 0 < Point.orientedArea (vertices first) (vertices second) origin) :
    (∃ index, 0 ≤ Point.orientedArea origin (vertices index) point) ∧
      (∃ index, Point.orientedArea origin (vertices index) point ≤ 0) := by
  have balance := Point.orientedArea_weighted_balance
    (vertices first) (vertices second) (vertices third) origin point
  constructor
  · by_contra missing
    push Not at missing
    have first_negative := mul_neg_of_pos_of_neg first_weight (missing first)
    have second_negative := mul_neg_of_pos_of_neg second_weight (missing second)
    have third_negative := mul_neg_of_pos_of_neg third_weight (missing third)
    linarith
  · by_contra missing
    push Not at missing
    have first_positive := mul_pos first_weight (missing first)
    have second_positive := mul_pos second_weight (missing second)
    have third_positive := mul_pos third_weight (missing third)
    linarith

end SquarePackingArchive
