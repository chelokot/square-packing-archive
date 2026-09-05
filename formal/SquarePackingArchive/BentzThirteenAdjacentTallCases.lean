import SquarePackingArchive.BentzThirteenAdjacentPrefix
import SquarePackingArchive.BentzThirteenChordCases
import SquarePackingArchive.BentzRectangleMidpoints
import SquarePackingArchive.BentzAdjacentR2LeftData
import SquarePackingArchive.BentzAdjacentR2RightData

namespace SquarePackingArchive.BentzThirteen

theorem contradiction_of_adjacent_r2
    (left_unavoidable : Unavoidable adjacentR2LeftPoints 4)
    (right_unavoidable : Unavoidable adjacentR2RightPoints 4)
    {family : Family} (pair : AdjacentPair family) (third : Fin 13)
    (third_first : third ≠ pair.first) (third_second : third ≠ pair.second)
    (center : adjacentInitialCriticalRegion 1 (family.squares third).center)
    (missing : ∀ index, ¬ (family.squares third).Contains (adjacentInitialPoints index)) : False := by
  have center_bounds : 2 ≤ (family.squares third).center.x ∧ (family.squares third).center.x ≤ 3 ∧
      59 / 25 ≤ (family.squares third).center.y ∧ (family.squares third).center.y ≤ 309 / 100 := center
  have corners_missing : ∀ column row : Fin 2,
      ¬ (family.squares third).Contains ⟨2 + column, 59 / 25 + (73 / 100) * row⟩ := by
    intro column row
    fin_cases column <;> fin_cases row
    · simpa [adjacentInitialPoints] using missing 15
    · convert missing 18 using 1; norm_num [adjacentInitialPoints]
    · convert missing 16 using 1; norm_num [adjacentInitialPoints]
    · convert missing 19 using 1; norm_num [adjacentInitialPoints]
  have midpoints := Bentz.both_midpoints_of_missed_rectangle_corners (family.squares third)
    (left := 2) (bottom := 59 / 25) (height := 73 / 100) (by norm_num) (by norm_num)
    center_bounds.1 (by linarith [center_bounds.2.1]) center_bounds.2.2.1
    (by linarith [center_bounds.2.2.2]) corners_missing
  have midpoint_lower : (family.squares third).Contains ⟨5 / 2, 59 / 25⟩ := by
    convert midpoints.1 using 1; norm_num
  have midpoint_upper : (family.squares third).Contains ⟨5 / 2, 309 / 100⟩ := by
    convert midpoints.2 using 1; norm_num
  by_cases left_inside : (family.squares third).Contains ⟨2, 68 / 25⟩
  · have prefix_counts := pair.prefix_cards adjacentR2LeftPoints (by norm_num) (by
      intro index; fin_cases index <;> rfl)
    apply pair.capacity_contradiction adjacentR2LeftPoints left_unavoidable
      (selected := 3) (by norm_num) (by norm_num) third third_first third_second prefix_counts.1 prefix_counts.2
    have bound := family.covered_card_lower adjacentR2LeftPoints third {10, 11, 12} (by
      intro index member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · exact midpoint_lower
      · exact midpoint_upper
      · exact left_inside)
    exact bound
  · have right_inside := Bentz.tall_rectangle_missing_left_forces_right (family.squares third)
      (left := 2) (bottom := 59 / 25) center_bounds.1 (by linarith [center_bounds.2.1])
      center_bounds.2.2.1 (by linarith [center_bounds.2.2.2]) corners_missing
      (by convert left_inside using 1; norm_num)
    have right_point : (family.squares third).Contains ⟨3, 66 / 25⟩ := by
      convert right_inside using 1; norm_num
    have prefix_counts := pair.prefix_cards adjacentR2RightPoints (by norm_num) (by
      intro index; fin_cases index <;> rfl)
    apply pair.capacity_contradiction adjacentR2RightPoints right_unavoidable
      (selected := 3) (by norm_num) (by norm_num) third third_first third_second prefix_counts.1 prefix_counts.2
    have bound := family.covered_card_lower adjacentR2RightPoints third {10, 11, 12} (by
      intro index member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · exact midpoint_lower
      · exact midpoint_upper
      · exact right_point)
    exact bound

end SquarePackingArchive.BentzThirteen
