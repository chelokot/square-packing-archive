import SquarePackingArchive.BentzThirteenAdjacentPrefix
import SquarePackingArchive.BentzAdjacentR3Data
import SquarePackingArchive.BentzAdjacentR4Data
import SquarePackingArchive.BentzRectangleMidpoints
import SquarePackingArchive.BentzThirteenChordCases

namespace SquarePackingArchive.BentzThirteen

theorem contradiction_of_adjacent_r3
    (unavoidable : Unavoidable adjacentR3Points 4)
    {family : Family} (pair : AdjacentPair family) (third : Fin 13)
    (third_first : third ≠ pair.first) (third_second : third ≠ pair.second)
    (center : adjacentInitialCriticalRegion 2 (family.squares third).center)
    (missing : ∀ index, ¬ (family.squares third).Contains (adjacentInitialPoints index)) : False := by
  have corners_missing : ∀ column row : Fin 2,
      ¬ (family.squares third).Contains ⟨2 + column, 91 / 50 + (27 / 50) * row⟩ := by
    intro column row
    fin_cases column <;> fin_cases row
    · convert missing 12 using 1; norm_num [adjacentInitialPoints]
    · convert missing 15 using 1; norm_num [adjacentInitialPoints]
    · convert missing 13 using 1; norm_num [adjacentInitialPoints]
    · convert missing 16 using 1; norm_num [adjacentInitialPoints]
  have midpoints := Bentz.both_midpoints_of_missed_rectangle_corners (family.squares third)
    (left := 2) (bottom := 91 / 50) (height := 27 / 50)
    (by norm_num) (by norm_num) center.1 (by linarith [center.2.1]) center.2.2.1
    (by linarith [center.2.2.2]) corners_missing
  have side_points := Bentz.short_rectangle_forces_both_side_points (family.squares third)
    center.1 (by linarith [center.2.1]) center.2.2.1
    (by linarith [center.2.2.2]) corners_missing
  have additional := Bentz.short_rectangle_forces_additional_side_point (family.squares third)
    center.1 (by linarith [center.2.1]) center.2.2.1
    (by linarith [center.2.2.2]) corners_missing
  norm_num at midpoints side_points additional
  have corner_cards := pair.prefix_cards adjacentR3Points (by norm_num) (by
    intro index
    fin_cases index <;> rfl)
  apply pair.capacity_contradiction adjacentR3Points unavoidable (selected := 4)
    (by norm_num) (by norm_num) third third_first third_second corner_cards.1 corner_cards.2
  rcases additional with left_point | right_point
  · have bound := family.covered_card_lower adjacentR3Points third {10, 11, 12, 18} (by
      intro index member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact midpoints.1
      · exact midpoints.2
      · exact side_points.2
      · exact left_point)
    exact bound
  · have bound := family.covered_card_lower adjacentR3Points third {10, 11, 12, 16} (by
      intro index member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact midpoints.1
      · exact midpoints.2
      · exact side_points.2
      · exact right_point)
    exact bound

theorem contradiction_of_adjacent_r4
    (unavoidable : Unavoidable adjacentR4Points 4)
    {family : Family} (pair : AdjacentPair family) (third : Fin 13)
    (third_first : third ≠ pair.first) (third_second : third ≠ pair.second)
    (center : adjacentInitialCriticalRegion 3 (family.squares third).center)
    (missing : ∀ index, ¬ (family.squares third).Contains (adjacentInitialPoints index)) : False := by
  have corners_missing : ∀ column row : Fin 2,
      ¬ (family.squares third).Contains ⟨1 + column, 91 / 50 + (27 / 50) * row⟩ := by
    intro column row
    fin_cases column <;> fin_cases row
    · convert missing 8 using 1; norm_num [adjacentInitialPoints]
    · convert missing 14 using 1; norm_num [adjacentInitialPoints]
    · convert missing 12 using 1; norm_num [adjacentInitialPoints]
    · convert missing 15 using 1; norm_num [adjacentInitialPoints]
  have midpoints := Bentz.both_midpoints_of_missed_rectangle_corners (family.squares third)
    (left := 1) (bottom := 91 / 50) (height := 27 / 50)
    (by norm_num) (by norm_num) center.1 (by linarith [center.2.1]) center.2.2.1
    (by linarith [center.2.2.2]) corners_missing
  have side_points := Bentz.short_rectangle_forces_both_side_points (family.squares third)
    center.1 (by linarith [center.2.1]) center.2.2.1
    (by linarith [center.2.2.2]) corners_missing
  norm_num at midpoints side_points
  have corner_cards := pair.prefix_cards adjacentR4Points (by norm_num) (by
    intro index
    fin_cases index <;> rfl)
  apply pair.capacity_contradiction adjacentR4Points unavoidable (selected := 4)
    (by norm_num) (by norm_num) third third_first third_second corner_cards.1 corner_cards.2
  have bound := family.covered_card_lower adjacentR4Points third {10, 11, 12, 13} (by
    intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact midpoints.1
    · exact midpoints.2
    · exact side_points.1
    · exact side_points.2)
  exact bound

end SquarePackingArchive.BentzThirteen
