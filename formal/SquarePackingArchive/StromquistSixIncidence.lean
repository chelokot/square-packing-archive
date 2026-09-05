import SquarePackingArchive.Geometry
import Mathlib.Data.Nat.Dist

namespace SquarePackingArchive.StromquistSix

def GridAdjacent (first second : Fin 9) : Prop :=
  Nat.dist (first.val % 3) (second.val % 3) +
    Nat.dist (first.val / 3) (second.val / 3) = 1

instance (first second : Fin 9) : Decidable (GridAdjacent first second) := inferInstanceAs
  (Decidable (Nat.dist (first.val % 3) (second.val % 3) +
    Nat.dist (first.val / 3) (second.val / 3) = 1))

def IndependentPerimeter (points : Finset (Fin 9)) : Prop :=
  4 ∉ points ∧ ∀ first ∈ points, ∀ second ∈ points, ¬ GridAdjacent first second

instance (points : Finset (Fin 9)) : Decidable (IndependentPerimeter points) :=
  inferInstanceAs (Decidable (4 ∉ points ∧
    ∀ first ∈ points, ∀ second ∈ points, ¬ GridAdjacent first second))

set_option maxRecDepth 8192 in
theorem independent_perimeter_classification :
    ∀ points : Finset (Fin 9), IndependentPerimeter points → points.card ≤ 4 ∧
      (points.card = 4 → points = {0, 2, 6, 8} ∨ points = {1, 3, 5, 7}) := by
  decide

theorem independent_four_remaining_edges_meet_center :
    ∀ points : Finset (Fin 9), IndependentPerimeter points → points.card = 4 →
      ∀ first second, first ∉ points → second ∉ points → GridAdjacent first second →
        first = 4 ∨ second = 4 := by
  intro points independent cardinality first second first_outside second_outside adjacent
  rcases (independent_perimeter_classification points independent).2 cardinality with same | same
  all_goals
    subst points
    revert first second
    decide

theorem gridAdjacent_symm {first second : Fin 9} (adjacent : GridAdjacent first second) :
    GridAdjacent second first := by
  simpa only [GridAdjacent, Nat.dist_comm] using adjacent

theorem gridAdjacent_ne {first second : Fin 9} (adjacent : GridAdjacent first second) :
    first ≠ second := by
  intro same
  subst second
  simp [GridAdjacent] at adjacent

theorem gridAdjacent_center_iff (neighbor : Fin 9) : GridAdjacent 4 neighbor ↔
    neighbor = 1 ∨ neighbor = 3 ∨ neighbor = 5 ∨ neighbor = 7 := by
  fin_cases neighbor <;> decide

theorem six_point_sets_have_center_pair
    (points : Fin 6 → Finset (Fin 9))
    (nonempty : ∀ owner, (points owner).Nonempty)
    (disjoint : Pairwise fun first second => Disjoint (points first) (points second))
    (singleton_not_center : ∀ owner point, points owner = {point} → point ≠ 4)
    (singleton_nonadjacent : ∀ first second left right, first ≠ second →
      points first = {left} → points second = {right} → ¬ GridAdjacent left right)
    (nonsingleton_pair : ∀ owner, 2 ≤ (points owner).card →
      ∃ first ∈ points owner, ∃ second ∈ points owner, GridAdjacent first second) :
    ∃ owner neighbor, GridAdjacent 4 neighbor ∧ points owner = {4, neighbor} := by
  classical
  let singles : Finset (Fin 6) := Finset.univ.filter fun owner => (points owner).card = 1
  let singletonPoints := singles.biUnion points
  have singleton_points_card : singletonPoints.card = singles.card := by
    rw [Finset.card_biUnion (fun first _ second _ different => disjoint different)]
    calc
      ∑ owner ∈ singles, (points owner).card = ∑ _owner ∈ singles, 1 := by
        apply Finset.sum_congr rfl
        intro owner member
        exact (Finset.mem_filter.mp member).2
      _ = singles.card := by simp
  have singleton_point (owner : Fin 6) (member : owner ∈ singles) :
      ∃ point, points owner = {point} := Finset.card_eq_one.mp (Finset.mem_filter.mp member).2
  have independent : IndependentPerimeter singletonPoints := by
    constructor
    · intro center_member
      obtain ⟨owner, owner_single, center_inside⟩ := Finset.mem_biUnion.mp center_member
      obtain ⟨point, point_eq⟩ := singleton_point owner owner_single
      have center_eq : (4 : Fin 9) = point := by simpa [point_eq] using center_inside
      exact singleton_not_center owner point point_eq center_eq.symm
    · intro first first_member second second_member
      obtain ⟨firstOwner, first_single, first_inside⟩ := Finset.mem_biUnion.mp first_member
      obtain ⟨secondOwner, second_single, second_inside⟩ := Finset.mem_biUnion.mp second_member
      obtain ⟨left, left_eq⟩ := singleton_point firstOwner first_single
      obtain ⟨right, right_eq⟩ := singleton_point secondOwner second_single
      have first_eq : first = left := by simpa [left_eq] using first_inside
      have second_eq : second = right := by simpa [right_eq] using second_inside
      subst left
      subst right
      by_cases same_owner : firstOwner = secondOwner
      · have same_point : first = second := by
          have same_sets := left_eq.symm.trans (same_owner ▸ right_eq)
          simpa using same_sets
        intro adjacent
        exact gridAdjacent_ne adjacent same_point
      · exact singleton_nonadjacent _ _ _ _ same_owner left_eq right_eq
  have singles_upper : singles.card ≤ 4 := by
    rw [← singleton_points_card]
    exact (independent_perimeter_classification _ independent).1
  have sum_bound : ∑ owner : Fin 6, (points owner).card ≤ 9 := by
    rw [← Finset.card_biUnion (fun first _ second _ different => disjoint different)]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans (by norm_num)
  have point_count_positive (owner : Fin 6) : 1 ≤ (points owner).card :=
    (nonempty owner).card_pos
  have double_nonsingle (owner : Fin 6) (not_single : owner ∉ singles) :
      2 ≤ (points owner).card := by
    have count_ne_one : (points owner).card ≠ 1 := by simpa [singles] using not_single
    have positive := point_count_positive owner
    omega
  have lower_count (owner : Fin 6) : (if owner ∈ singles then 1 else 2) ≤ (points owner).card := by
    split_ifs with single
    · exact point_count_positive owner
    · exact double_nonsingle owner single
  have indicator_sum : ∑ owner : Fin 6, (if owner ∈ singles then 1 else 2) =
      singles.card + 2 * (6 - singles.card) := by
    rw [Finset.sum_ite]
    simp [Finset.filter_notMem_eq_sdiff, Finset.card_sdiff]
    omega
  have singles_lower : 3 ≤ singles.card := by
    have lower := Finset.sum_le_sum (fun owner (_ : owner ∈ Finset.univ) => lower_count owner)
    rw [indicator_sum] at lower
    omega
  have nonsingle_avoids (owner : Fin 6) (not_single : owner ∉ singles)
      (point : Fin 9) (inside : point ∈ points owner) : point ∉ singletonPoints := by
    intro singleton_inside
    obtain ⟨other, other_single, other_inside⟩ := Finset.mem_biUnion.mp singleton_inside
    have different : owner ≠ other := by intro same; exact not_single (same ▸ other_single)
    exact Finset.disjoint_left.mp (disjoint different) inside other_inside
  have singles_card : singles.card = 3 := by
    by_contra not_three
    have singles_four : singles.card = 4 := by omega
    have remaining_card : (Finset.univ \ singles).card = 2 := by simp [Finset.card_sdiff, singles_four]
    obtain ⟨first, first_member, second, second_member, different⟩ :=
      Finset.one_lt_card.mp (show 1 < (Finset.univ \ singles).card by omega)
    have first_not_single := (Finset.mem_sdiff.mp first_member).2
    have second_not_single := (Finset.mem_sdiff.mp second_member).2
    have center_inside (owner : Fin 6) (not_single : owner ∉ singles) : 4 ∈ points owner := by
      obtain ⟨left, left_inside, right, right_inside, adjacent⟩ :=
        nonsingleton_pair owner (double_nonsingle owner not_single)
      have meets_center := independent_four_remaining_edges_meet_center singletonPoints independent
        (singleton_points_card.trans singles_four) left right
        (nonsingle_avoids owner not_single left left_inside)
        (nonsingle_avoids owner not_single right right_inside) adjacent
      rcases meets_center with same | same
      · simpa only [same] using left_inside
      · simpa only [same] using right_inside
    exact Finset.disjoint_left.mp (disjoint different)
      (center_inside first first_not_single) (center_inside second second_not_single)
  have minimum_sum : ∑ owner : Fin 6, (if owner ∈ singles then 1 else 2) = 9 := by
    rw [indicator_sum, singles_card]
  have total_sum : ∑ owner : Fin 6, (points owner).card = 9 := by
    apply le_antisymm sum_bound
    calc
      9 = ∑ owner : Fin 6, (if owner ∈ singles then 1 else 2) := minimum_sum.symm
      _ ≤ ∑ owner : Fin 6, (points owner).card :=
        Finset.sum_le_sum (fun owner _ => lower_count owner)
  have exact_count (owner : Fin 6) :
      (if owner ∈ singles then 1 else 2) = (points owner).card :=
    (Finset.sum_eq_sum_iff_of_le (fun owner (_ : owner ∈ Finset.univ) => lower_count owner)).1
      (minimum_sum.trans total_sum.symm) owner (Finset.mem_univ owner)
  have covered : Finset.univ.biUnion points = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_biUnion (fun first _ second _ different => disjoint different), total_sum]
    rfl
  obtain ⟨owner, _, center_inside⟩ := Finset.mem_biUnion.mp
    (show (4 : Fin 9) ∈ Finset.univ.biUnion points by rw [covered]; exact Finset.mem_univ _)
  have owner_not_single : owner ∉ singles := by
    intro single
    exact independent.1 (Finset.mem_biUnion.mpr ⟨owner, single, center_inside⟩)
  have owner_card : (points owner).card = 2 := by
    simpa only [if_neg owner_not_single] using (exact_count owner).symm
  obtain ⟨first, first_inside, second, second_inside, adjacent⟩ :=
    nonsingleton_pair owner owner_card.ge
  have points_eq : points owner = {first, second} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · exact Finset.insert_subset first_inside (Finset.singleton_subset_iff.mpr second_inside)
    · rw [owner_card, Finset.card_pair (gridAdjacent_ne adjacent)]
  have center_cases : (4 : Fin 9) = first ∨ (4 : Fin 9) = second := by
    simpa only [points_eq, Finset.mem_insert, Finset.mem_singleton] using center_inside
  rcases center_cases with same | same
  · subst first
    exact ⟨owner, second, adjacent, points_eq⟩
  · subst second
    exact ⟨owner, first, gridAdjacent_symm adjacent, points_eq.trans (Finset.pair_comm _ _)⟩

end SquarePackingArchive.StromquistSix
