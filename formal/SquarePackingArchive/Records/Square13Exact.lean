import SquarePackingArchive.BentzThirteenVerifiedCovers
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square13

theorem s13_lower_bound : IsLowerBound 13 4 := by
  intro side has_packing
  by_contra! side_lt_four
  obtain ⟨squares, fits, disjoint⟩ :=
    has_packing.some.exists_closed_disjoint_family_in_larger_container (by norm_num) side_lt_four
  exact BentzThirteen.no_closed_family ⟨squares, fits, disjoint⟩

theorem s13_eq_four : IsMinimumSide 13 4 :=
  ⟨SquareNumbers.s16_eq_four.1.mono (by norm_num), s13_lower_bound⟩

end SquarePackingArchive.Records.Square13
