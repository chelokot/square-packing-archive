import SquarePackingArchive.StromquistTenSegments
import SquarePackingArchive.StromquistRingExterior
import SquarePackingArchive.Records.Square10

namespace SquarePackingArchive.Records.Square10

theorem s10_lower_bound : IsLowerBound 10 (3 + Real.sqrt 2 / 2) := by
  intro candidateSide has_packing
  by_contra! smaller
  have smaller_than_stromquist : candidateSide < Stromquist.TenPoints.side := by
    dsimp [Stromquist.TenPoints.side, Stromquist.TenPoints.gap, Square5.diagonal]
    linarith
  obtain ⟨family⟩ := Stromquist.TenPoints.exists_namedFamily_of_packing_below
    has_packing.some smaller_than_stromquist
  exact Stromquist.TenPoints.false_of_namedFamily_of_ring_unavoidable
    Stromquist.TenPoints.ring_unavoidable family

theorem s10_eq_goebel : IsMinimumSide 10 (3 + Real.sqrt 2 / 2) :=
  ⟨s10_le_goebel, s10_lower_bound⟩

end SquarePackingArchive.Records.Square10
