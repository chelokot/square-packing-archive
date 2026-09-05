import SquarePackingArchive.BentzThirteenAdjacentPrefix
import SquarePackingArchive.BentzThirteenChordCases
import SquarePackingArchive.BentzRectangleMidpoints
import SquarePackingArchive.BentzAdjacentR100Data
import SquarePackingArchive.BentzAdjacentR101Data
import SquarePackingArchive.BentzAdjacentR102Data
import SquarePackingArchive.BentzAdjacentR103Data
import SquarePackingArchive.BentzAdjacentR104Data
import SquarePackingArchive.BentzAdjacentR105Data
import SquarePackingArchive.BentzAdjacentR106Data
import SquarePackingArchive.BentzAdjacentR107Data

namespace SquarePackingArchive.BentzThirteen

noncomputable def r1Configuration (choice : Fin 8) : Σ count : ℕ, Fin count → Point :=
  match choice.val with
  | 0 => ⟨22, adjacentR100Points⟩
  | 1 => ⟨22, adjacentR101Points⟩
  | 2 => ⟨22, adjacentR102Points⟩
  | 3 => ⟨22, adjacentR103Points⟩
  | 4 => ⟨22, adjacentR104Points⟩
  | 5 => ⟨22, adjacentR105Points⟩
  | 6 => ⟨22, adjacentR106Points⟩
  | _ => ⟨22, adjacentR107Points⟩

theorem r1Configuration_size (choice : Fin 8) :
    13 ≤ (r1Configuration choice).1 ∧ (r1Configuration choice).1 < 23 := by
  fin_cases choice <;> decide

theorem contradiction_of_adjacent_r1
    (unavoidable : ∀ choice, Unavoidable (r1Configuration choice).2 4)
    {family : Family} (pair : AdjacentPair family) (third : Fin 13)
    (third_first : third ≠ pair.first) (third_second : third ≠ pair.second)
    (center : adjacentInitialCriticalRegion 0 (family.squares third).center)
    (missing : ∀ index, ¬ (family.squares third).Contains (adjacentInitialPoints index)) : False := by
  have center_bounds : 1 ≤ (family.squares third).center.x ∧ (family.squares third).center.x ≤ 2 ∧
      59 / 25 ≤ (family.squares third).center.y ∧ (family.squares third).center.y ≤ 309 / 100 := center
  have corners_missing : ∀ column row : Fin 2,
      ¬ (family.squares third).Contains ⟨1 + column, 59 / 25 + (73 / 100) * row⟩ := by
    intro column row
    fin_cases column <;> fin_cases row
    · simpa [adjacentInitialPoints] using missing 14
    · convert missing 17 using 1; norm_num [adjacentInitialPoints]
    · convert missing 15 using 1; norm_num [adjacentInitialPoints]
    · convert missing 18 using 1; norm_num [adjacentInitialPoints]
  have midpoints := Bentz.both_midpoints_of_missed_rectangle_corners (family.squares third)
    (left := 1) (bottom := 59 / 25) (height := 73 / 100) (by norm_num) (by norm_num)
    center_bounds.1 (by linarith [center_bounds.2.1]) center_bounds.2.2.1
    (by linarith [center_bounds.2.2.2]) corners_missing
  obtain ⟨choice, grid_inside⟩ := Bentz.tall_rectangle_forces_left_grid_point (family.squares third)
    (left := 1) (bottom := 59 / 25) center_bounds.1 (by linarith [center_bounds.2.1])
    center_bounds.2.2.1 (by linarith [center_bounds.2.2.2]) corners_missing
  have size := r1Configuration_size choice
  have prefix_counts := pair.prefix_cards (r1Configuration choice).2 (by omega) (by
    intro index
    fin_cases choice <;> fin_cases index <;> rfl)
  apply pair.capacity_contradiction (r1Configuration choice).2 (unavoidable choice)
    (selected := 3) (by simpa using size.2) (by norm_num)
    third third_first third_second prefix_counts.1 prefix_counts.2
  let lowerIndex : Fin (r1Configuration choice).1 := ⟨10, by omega⟩
  let upperIndex : Fin (r1Configuration choice).1 := ⟨11, by omega⟩
  let gridIndex : Fin (r1Configuration choice).1 := ⟨12, by omega⟩
  have lower_point : (r1Configuration choice).2 lowerIndex = ⟨1 + 1 / 2, 59 / 25⟩ := by
    fin_cases choice <;> change (⟨3 / 2, 59 / 25⟩ : Point) = _ <;> norm_num
  have upper_point : (r1Configuration choice).2 upperIndex = ⟨1 + 1 / 2, 59 / 25 + 73 / 100⟩ := by
    fin_cases choice <;> change (⟨3 / 2, 309 / 100⟩ : Point) = _ <;> norm_num
  have grid_point : (r1Configuration choice).2 gridIndex = ⟨1, 59 / 25 + (2 / 25) * (choice + 1)⟩ := by
    fin_cases choice
    · change (⟨1, 61 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 63 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 13 / 5⟩ : Point) = _; norm_num
    · change (⟨1, 67 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 69 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 71 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 73 / 25⟩ : Point) = _; norm_num
    · change (⟨1, 3⟩ : Point) = _; norm_num
  have bound := family.covered_card_lower (r1Configuration choice).2 third
    {lowerIndex, upperIndex, gridIndex} (by
      intro index member
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · rw [lower_point]; exact midpoints.1
      · rw [upper_point]; exact midpoints.2
      · rw [grid_point]; exact grid_inside)
  simpa [lowerIndex, upperIndex, gridIndex, Fin.ext_iff] using bound

end SquarePackingArchive.BentzThirteen
