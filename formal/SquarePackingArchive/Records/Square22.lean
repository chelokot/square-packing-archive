import SquarePackingArchive.BentzFiveRowsContradiction
import SquarePackingArchive.BentzFiveRowsWitnesses
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square22

theorem no_packing_near_five {side : ℝ} (packing : Packing 22 side)
    (side_lower : 4999 / 1000 ≤ side) (side_lt_five : side < 5) : False := by
  have oriented_contradiction (candidate : Packing 22 side)
      (left_unique : BentzFiveRows.BlueLeftUnique candidate) : False := by
    obtain ⟨owners, exception, half_inside, one_inside, left_inside, right_missing⟩ :=
      BentzFiveRows.five_row_witnesses candidate side_lower side_lt_five left_unique
    exact BentzFiveRows.contradiction_of_row_witnesses candidate side_lower side_lt_five
      owners exception half_inside one_inside left_inside right_missing
  rcases BentzFiveRows.blue_left_unique_or_reflected packing side_lower side_lt_five with
    left_unique | reflected_unique
  · exact oriented_contradiction packing left_unique
  · exact oriented_contradiction packing.reflectX reflected_unique

theorem s22_lower_bound : IsLowerBound 22 5 := by
  intro side has_packing
  by_contra! side_lt_five
  let enlarged := has_packing.some.enlarge (le_max_left side (4999 / 1000))
  exact no_packing_near_five enlarged (le_max_right _ _)
    (max_lt side_lt_five (by norm_num))

theorem s22_eq_five : IsMinimumSide 22 5 :=
  ⟨SquareNumbers.s25_eq_five.1.mono (by norm_num), s22_lower_bound⟩

end SquarePackingArchive.Records.Square22
