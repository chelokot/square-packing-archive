import SquarePackingArchive.NagamochiFiniteChain
import SquarePackingArchive.NagamochiInitialDebt
import SquarePackingArchive.NagamochiAdjacentMarks
import SquarePackingArchive.NagamochiBadCornerLocation

namespace SquarePackingArchive

open MeasureTheory Set

theorem Packing.squareMinusTwo_not_adjacent_bottom_marks
    {size coordinate : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 1 (size - 2))
    (owner : Fin (size * size - 2)) :
    ¬(![(coordinate : ℝ), 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor ∧
      ![(coordinate : ℝ) + 1, 9 / 10] ∈ (packing.squares owner).dilatedInteriorRegion factor) := by
  rintro ⟨first_mem, second_mem⟩
  by_cases first : coordinate = 1
  · apply packing.squareMinusTwo_not_adjacent_bottom_corner_and_edge size_lower
      factor_gt_one factor_at_most scaled_side_le owner
    subst coordinate
    norm_num at first_mem second_mem
    exact ⟨first_mem, second_mem⟩
  by_cases last : coordinate = size - 2
  · apply packing.squareMinusTwo_not_adjacent_right_bottom_corner_and_edge size_lower
      factor_gt_one factor_at_most scaled_side_le owner
    have coordinate_real : (coordinate : ℝ) = (size : ℝ) - 2 := by
      rw [last, Nat.cast_sub (by omega)]
      norm_num
    rw [coordinate_real] at first_mem second_mem
    exact ⟨by convert second_mem using 1; congr 1; ring, first_mem⟩
  · apply packing.squareMinusTwo_not_two_bottom_points (coordinate := coordinate) (by omega) factor_gt_one
      factor_at_most scaled_side_le (by simp only [Finset.mem_Icc] at coordinate_mem; omega)
      (by simp only [Finset.mem_Icc] at coordinate_mem; omega) owner
    exact ⟨first_mem, by simpa using second_mem⟩

theorem Nagamochi.bottom_left_bad_owner_reaches_weighted_terminal
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (origin : Fin (size * size - 2))
    (corner_mem : ![(1 : ℝ), 9 / 10] ∈ (packing.squares origin).dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) ≤ 1) :
    ∃ coordinate ∈ Finset.Icc 2 (size - 1), ∃ owner height,
      height ∈ Icc (9 / 10 : ℝ) 1 ∧
      ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      Nagamochi.BoundaryChainTerminal (packing.squares owner) factor coordinate height ∧
      ENNReal.ofReal ((1 + height) / 2) <
        NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) := by
  have inside := (packing.squares origin).dilatedInteriorRegion_subset_containerRegion
    (packing.fits origin) (zero_lt_one.trans factor_gt_one).le scaled_side_le
  obtain ⟨center_horizontal, center_below⟩ := Nagamochi.bottom_strip_of_bad_left_bottom_corner
    (packing.squares origin) (packing.fits origin) size_lower factor_gt_one factor_at_most
    inside corner_mem bad
  obtain ⟨initialHeight, initial_height_mem, initial_crossing, initial_budget⟩ :=
    Nagamochi.bottom_bad_square_starts_weighted_chain (packing.squares origin)
      (packing.fits origin) size_lower factor_gt_one factor_at_most
      inside
      center_horizontal center_below corner_mem bad
  rcases Nagamochi.finite_bottom_owner_chain_reaches_terminal_or_shared_owner packing
    (by omega) factor_gt_one factor_at_most scaled_side_le origin corner_mem
    initial_crossing initial_height_mem with terminal | shared
  · obtain ⟨coordinate, coordinate_mem, owner, height, height_mem, anchor, terminal⟩ := terminal
    exact ⟨coordinate, coordinate_mem, owner, height,
      ⟨height_mem.1, height_mem.2.trans initial_height_mem.2⟩, anchor, terminal,
      (ENNReal.ofReal_le_ofReal (by linarith [height_mem.2])).trans_lt initial_budget⟩
  · obtain ⟨coordinate, coordinate_mem, owner, first_mem, second_mem⟩ := shared
    exact False.elim (packing.squareMinusTwo_not_adjacent_bottom_marks size_lower factor_gt_one
      factor_at_most scaled_side_le coordinate_mem owner ⟨first_mem, second_mem⟩)

end SquarePackingArchive
