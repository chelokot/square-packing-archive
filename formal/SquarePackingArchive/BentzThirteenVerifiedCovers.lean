import SquarePackingArchive.BentzThirteenAssembly
import SquarePackingArchive.BentzThirteenNonadjacent
import SquarePackingArchive.BentzAdjacentInitialCover
import SquarePackingArchive.BentzAdjacentR100Cover
import SquarePackingArchive.BentzAdjacentR101Cover
import SquarePackingArchive.BentzAdjacentR102Cover
import SquarePackingArchive.BentzAdjacentR103Cover
import SquarePackingArchive.BentzAdjacentR104Cover
import SquarePackingArchive.BentzAdjacentR105Cover
import SquarePackingArchive.BentzAdjacentR106Cover
import SquarePackingArchive.BentzAdjacentR107Cover
import SquarePackingArchive.BentzAdjacentR2LeftCover
import SquarePackingArchive.BentzAdjacentR2RightCover
import SquarePackingArchive.BentzAdjacentR3Cover
import SquarePackingArchive.BentzAdjacentR4Cover

namespace SquarePackingArchive.BentzThirteen

theorem verifiedCovers : CoverCertificates where
  nonadjacent_initial := Nonadjacent.initial_cover
  nonadjacent_final := Nonadjacent.final_unavoidable
  adjacent_initial := adjacentInitial_unavoidable
  adjacent_r1 := by
    intro choice
    fin_cases choice
    · exact adjacentR100_unavoidable
    · exact adjacentR101_unavoidable
    · exact adjacentR102_unavoidable
    · exact adjacentR103_unavoidable
    · exact adjacentR104_unavoidable
    · exact adjacentR105_unavoidable
    · exact adjacentR106_unavoidable
    · exact adjacentR107_unavoidable
  adjacent_r2_left := adjacentR2Left_unavoidable
  adjacent_r2_right := adjacentR2Right_unavoidable
  adjacent_r3 := adjacentR3_unavoidable
  adjacent_r4 := adjacentR4_unavoidable

theorem no_closed_family (family : Family) : False :=
  no_closed_family_of_covers verifiedCovers family

end SquarePackingArchive.BentzThirteen
