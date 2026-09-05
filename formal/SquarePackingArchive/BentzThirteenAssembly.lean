import SquarePackingArchive.BentzThirteenNonadjacentCount
import SquarePackingArchive.BentzThirteenAdjacentTallCases
import SquarePackingArchive.BentzThirteenAdjacentShortCases
import SquarePackingArchive.BentzThirteenAdjacentR1

namespace SquarePackingArchive.BentzThirteen

structure CoverCertificates : Prop where
  nonadjacent_initial : ∀ choices (square : PlacedSquare), square.Fits 4 →
    (∃ index, square.Contains (Nonadjacent.initialPoints choices index)) ∨ Nonadjacent.Hole square.center
  nonadjacent_final : ∀ choices, Unavoidable (Nonadjacent.finalPoints choices) 4
  adjacent_initial : ∀ square : PlacedSquare, square.Fits 4 → adjacentInitialOutcome square
  adjacent_r1 : ∀ choice, Unavoidable (r1Configuration choice).2 4
  adjacent_r2_left : Unavoidable adjacentR2LeftPoints 4
  adjacent_r2_right : Unavoidable adjacentR2RightPoints 4
  adjacent_r3 : Unavoidable adjacentR3Points 4
  adjacent_r4 : Unavoidable adjacentR4Points 4

theorem no_adjacent_pair_of_covers (certificates : CoverCertificates)
    {family : Family} (pair : AdjacentPair family) : False := by
  obtain ⟨third, third_first, third_second, missing⟩ := pair.initial_uncovered
  obtain hit | ⟨region, center⟩ := certificates.adjacent_initial (family.squares third) (family.fits third)
  · obtain ⟨index, inside⟩ := hit
    exact missing index inside
  · fin_cases region
    · exact contradiction_of_adjacent_r1 certificates.adjacent_r1 pair third third_first third_second center missing
    · exact contradiction_of_adjacent_r2 certificates.adjacent_r2_left certificates.adjacent_r2_right
        pair third third_first third_second center missing
    · exact contradiction_of_adjacent_r3 certificates.adjacent_r3 pair third third_first third_second center missing
    · exact contradiction_of_adjacent_r4 certificates.adjacent_r4 pair third third_first third_second center missing

theorem no_closed_family_of_covers (certificates : CoverCertificates) (family : Family) : False := by
  obtain ⟨oriented, first, second, other, corner_bound, other_nonzero,
    first_restricted, second_restricted⟩ := family.normalized_restricted_corners
  by_cases adjacent : other = 1
  · subst other
    obtain ⟨normalized, ⟨pair⟩⟩ := adjacent_pair_exists oriented first second first_restricted second_restricted
    exact no_adjacent_pair_of_covers certificates pair
  · apply Nonadjacent.contradiction_of_normalized_nonadjacent certificates.nonadjacent_initial
      certificates.nonadjacent_final first_restricted second_restricted (by omega) corner_bound

end SquarePackingArchive.BentzThirteen
