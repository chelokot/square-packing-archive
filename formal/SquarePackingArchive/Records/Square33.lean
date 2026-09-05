import SquarePackingArchive.BentzSixRowsCombine
import SquarePackingArchive.BentzSixRowsEndpoint
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square33

theorem s33_lower_bound : IsLowerBound 33 6 := by
  intro side has_packing
  by_contra! side_lt_six
  let packing := has_packing.some
  have side_positive := packing.side_positive (by norm_num)
  exact BentzSixRows.contradiction_of_row_endpoints packing side_positive side_lt_six
    (fun candidate selected owner inside =>
      BentzSixRows.odd_row_endpoint_same_owner candidate side_positive side_lt_six selected owner inside)

theorem s33_eq_six : IsMinimumSide 33 6 :=
  ⟨SquareNumbers.s36_eq_six.1.mono (by norm_num), s33_lower_bound⟩

end SquarePackingArchive.Records.Square33
