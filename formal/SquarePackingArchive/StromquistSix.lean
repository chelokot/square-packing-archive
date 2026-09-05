import SquarePackingArchive.StromquistSixPoints
import SquarePackingArchive.StromquistSixIncidence
import SquarePackingArchive.StromquistSixAdjacency
import SquarePackingArchive.StromquistSixSingletons
import SquarePackingArchive.PackingPointCapacity

namespace SquarePackingArchive.StromquistSix

def ClosedDisjointFamily (squares : Fin 6 → PlacedSquare) : Prop :=
  ∀ first second, first ≠ second → ∀ point,
    ¬ ((squares first).Contains point ∧ (squares second).Contains point)

theorem ClosedDisjointFamily.reflectY {squares : Fin 6 → PlacedSquare}
    (disjoint : ClosedDisjointFamily squares) :
    ClosedDisjointFamily (fun owner => (squares owner).reflectY 3) := by
  intro first second different point shared
  apply disjoint first second different (point.reflectY 3)
  constructor
  · exact ((squares first).reflectY_contains_iff 3 (point.reflectY 3)).1 (by simpa using shared.1)
  · exact ((squares second).reflectY_contains_iff 3 (point.reflectY 3)).1 (by simpa using shared.2)

theorem ClosedDisjointFamily.swap {squares : Fin 6 → PlacedSquare}
    (disjoint : ClosedDisjointFamily squares) :
    ClosedDisjointFamily (fun owner => (squares owner).swap) := by
  intro first second different point shared
  apply disjoint first second different point.swap
  constructor
  · exact ((squares first).swap_contains_iff point.swap).1 (by simpa using shared.1)
  · exact ((squares second).swap_contains_iff point.swap).1 (by simpa using shared.2)

theorem no_closed_family_north_pair (squares : Fin 6 → PlacedSquare)
    (fits : ∀ owner, (squares owner).Fits 3) (disjoint : ClosedDisjointFamily squares)
    (owner : Fin 6)
    (pair : ∀ index, (squares owner).Contains (keyPoints index) ↔ index = 4 ∨ index = 7) : False := by
  classical
  have center_inside := (pair 4).2 (Or.inl rfl)
  have north_inside := (pair 7).2 (Or.inr rfl)
  have extra_inside := center_pair_forces_extra_points
    (by simpa [keyPoints] using center_inside)
    (by simpa [keyPoints] using north_inside)
    (by intro inside; have := (pair 3).1 inside; norm_num [Fin.ext_iff] at this)
    (by intro inside; have := (pair 5).1 inside; norm_num [Fin.ext_iff] at this)
    (by intro inside; have := (pair 6).1 inside; norm_num [Fin.ext_iff] at this)
    (by intro inside; have := (pair 8).1 inside; norm_num [Fin.ext_iff] at this)
  let points (selected : Fin 6) : Finset (Fin 8) :=
    Finset.univ.filter fun index => (squares selected).Contains (extraPoints index)
  have pointsets_disjoint : Pairwise fun first second => Disjoint (points first) (points second) := by
    intro first second different
    apply Finset.disjoint_left.mpr
    intro index first_mem second_mem
    exact disjoint first second different (extraPoints index)
      ⟨(Finset.mem_filter.mp first_mem).2, (Finset.mem_filter.mp second_mem).2⟩
  have all_positive (selected : Fin 6) : 1 ≤ (points selected).card := by
    obtain ⟨index, inside⟩ := extraPoints_unavoidable (squares selected) (fits selected)
    exact Finset.card_pos.mpr ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, inside⟩⟩
  have owner_four : 4 ≤ (points owner).card := by
    have subset : ({1, 3, 4, 5} : Finset (Fin 8)) ⊆ points owner := by
      intro index member
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [extraPoints, keyPoints] using north_inside
      · simpa [extraPoints] using extra_inside.1
      · simpa [extraPoints] using extra_inside.2
      · simpa [extraPoints, keyPoints] using center_inside
    have cardinality := Finset.card_le_card subset
    exact cardinality
  have upper : ∑ selected : Fin 6, (points selected).card ≤ 8 := by
    rw [← Finset.card_biUnion (fun first _ second _ different => pointsets_disjoint different)]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans (by norm_num)
  have lower : 9 ≤ ∑ selected : Fin 6, (points selected).card := by
    calc
      9 = ∑ selected : Fin 6, (if selected = owner then 4 else 1) := by
        simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
      _ ≤ ∑ selected : Fin 6, (points selected).card := by
        apply Finset.sum_le_sum
        intro selected _
        split_ifs with same
        · simpa only [same] using owner_four
        · exact all_positive selected
  omega

theorem reflected_key_mem (square : PlacedSquare) (index : Fin 9) :
    (square.reflectY 3).Contains (keyPoints index) ↔ square.Contains (keyPoints (keyReflectY index)) := by
  rw [keyPoints_reflectY]
  simpa using square.reflectY_contains_iff 3 ((keyPoints index).reflectY 3)

theorem swapped_key_mem (square : PlacedSquare) (index : Fin 9) :
    square.swap.Contains (keyPoints index) ↔ square.Contains (keyPoints (keySwap index)) := by
  rw [keyPoints_swap]
  simpa using square.swap_contains_iff (keyPoints index).swap

theorem no_closed_family_vertical_pair (squares : Fin 6 → PlacedSquare)
    (fits : ∀ owner, (squares owner).Fits 3) (disjoint : ClosedDisjointFamily squares)
    (owner : Fin 6) (neighbor : Fin 9) (vertical : neighbor = 1 ∨ neighbor = 7)
    (pair : ∀ index, (squares owner).Contains (keyPoints index) ↔ index = 4 ∨ index = neighbor) : False := by
  rcases vertical with rfl | rfl
  · apply no_closed_family_north_pair (fun selected => (squares selected).reflectY 3)
      (fun selected => ((squares selected).reflectY_fits_iff 3).2 (fits selected)) disjoint.reflectY owner
    intro index
    rw [reflected_key_mem, pair]
    fin_cases index <;> norm_num [keyReflectY, Fin.ext_iff]
  · exact no_closed_family_north_pair squares fits disjoint owner pair

theorem no_closed_family_center_pair (squares : Fin 6 → PlacedSquare)
    (fits : ∀ owner, (squares owner).Fits 3) (disjoint : ClosedDisjointFamily squares)
    (owner : Fin 6) (neighbor : Fin 9) (adjacent : GridAdjacent 4 neighbor)
    (pair : ∀ index, (squares owner).Contains (keyPoints index) ↔ index = 4 ∨ index = neighbor) : False := by
  rcases (gridAdjacent_center_iff neighbor).1 adjacent with rfl | rfl | rfl | rfl
  · exact no_closed_family_vertical_pair squares fits disjoint owner 1 (Or.inl rfl) pair
  · apply no_closed_family_vertical_pair (fun selected => (squares selected).swap)
      (fun selected => ((squares selected).swap_fits_iff 3).2 (fits selected)) disjoint.swap owner 1 (Or.inl rfl)
    intro index
    rw [swapped_key_mem, pair]
    fin_cases index <;> norm_num [keySwap, Fin.ext_iff]
  · apply no_closed_family_vertical_pair (fun selected => (squares selected).swap)
      (fun selected => ((squares selected).swap_fits_iff 3).2 (fits selected)) disjoint.swap owner 7 (Or.inr rfl)
    intro index
    rw [swapped_key_mem, pair]
    fin_cases index <;> norm_num [keySwap, Fin.ext_iff]
  · exact no_closed_family_vertical_pair squares fits disjoint owner 7 (Or.inr rfl) pair

theorem no_closed_family
    (squares : Fin 6 → PlacedSquare) (fits : ∀ owner, (squares owner).Fits 3)
    (disjoint : ClosedDisjointFamily squares) : False := by
  classical
  let points (owner : Fin 6) : Finset (Fin 9) :=
    Finset.univ.filter fun index => (squares owner).Contains (keyPoints index)
  have point_mem (owner : Fin 6) (index : Fin 9) :
      index ∈ points owner ↔ (squares owner).Contains (keyPoints index) := by simp [points]
  have singleton_mem (owner : Fin 6) (point : Fin 9) (singleton : points owner = {point}) :
      ∀ index, (squares owner).Contains (keyPoints index) ↔ index = point := by
    intro index
    rw [← point_mem, singleton, Finset.mem_singleton]
  have singleton_not_center (owner : Fin 6) (point : Fin 9) (singleton : points owner = {point}) :
      point ≠ 4 := by
    obtain ⟨index, not_center, inside⟩ := perimeter_unavoidable (fits owner)
    have same := (singleton_mem owner point singleton index).1 inside
    exact same ▸ not_center
  obtain ⟨owner, neighbor, adjacent, pair_eq⟩ := six_point_sets_have_center_pair points
    (by
      intro owner
      obtain ⟨index, _, inside⟩ := perimeter_unavoidable (fits owner)
      exact ⟨index, (point_mem owner index).2 inside⟩)
    (by
      intro first second different
      apply Finset.disjoint_left.mpr
      intro index first_inside second_inside
      exact disjoint first second different (keyPoints index)
        ⟨(point_mem _ _).1 first_inside, (point_mem _ _).1 second_inside⟩)
    singleton_not_center
    (by
      intro first second left right different first_single second_single adjacent
      obtain ⟨point, shared⟩ := adjacent_singleton_keyPoints_intersect (squares first) (squares second)
        (fits first) (fits second) left right
        (singleton_not_center first left first_single) (singleton_not_center second right second_single)
        (singleton_mem first left first_single) (singleton_mem second right second_single) adjacent
      exact disjoint first second different point shared)
    (by
      intro owner cardinality
      obtain ⟨first, first_inside, second, second_inside, different⟩ :=
        Finset.one_lt_card.mp (show 1 < (points owner).card by omega)
      obtain ⟨left, right, left_inside, right_inside, adjacent⟩ := contains_adjacent_keyPoints different
        ((point_mem owner first).1 first_inside) ((point_mem owner second).1 second_inside)
      exact ⟨left, (point_mem _ _).2 left_inside, right, (point_mem _ _).2 right_inside, adjacent⟩)
  apply no_closed_family_center_pair squares fits disjoint owner neighbor adjacent
  intro index
  rw [← point_mem, pair_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]

end SquarePackingArchive.StromquistSix
