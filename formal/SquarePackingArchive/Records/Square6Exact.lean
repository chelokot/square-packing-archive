import SquarePackingArchive.StromquistSix
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square6

theorem s6_lower_bound : IsLowerBound 6 3 := by
  intro side has_packing
  by_contra! side_lt_three
  obtain ⟨squares, fits, disjoint⟩ :=
    has_packing.some.exists_closed_disjoint_family_in_larger_container (by norm_num) side_lt_three
  exact StromquistSix.no_closed_family squares fits disjoint

theorem s6_eq_three : IsMinimumSide 6 3 :=
  ⟨SquareNumbers.s9_eq_three.1.mono (by norm_num), s6_lower_bound⟩

end SquarePackingArchive.Records.Square6
