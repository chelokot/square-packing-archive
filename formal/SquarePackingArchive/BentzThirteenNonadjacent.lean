import SquarePackingArchive.BentzThirteenNonadjacent.Initial00
import SquarePackingArchive.BentzThirteenNonadjacent.Initial01
import SquarePackingArchive.BentzThirteenNonadjacent.Initial02
import SquarePackingArchive.BentzThirteenNonadjacent.Initial03
import SquarePackingArchive.BentzThirteenNonadjacent.Initial04
import SquarePackingArchive.BentzThirteenNonadjacent.Initial05
import SquarePackingArchive.BentzThirteenNonadjacent.Initial06
import SquarePackingArchive.BentzThirteenNonadjacent.Initial07
import SquarePackingArchive.BentzThirteenNonadjacent.Initial08
import SquarePackingArchive.BentzThirteenNonadjacent.Initial09
import SquarePackingArchive.BentzThirteenNonadjacent.Initial10
import SquarePackingArchive.BentzThirteenNonadjacent.Initial11
import SquarePackingArchive.BentzThirteenNonadjacent.Initial12
import SquarePackingArchive.BentzThirteenNonadjacent.Initial13
import SquarePackingArchive.BentzThirteenNonadjacent.Initial14
import SquarePackingArchive.BentzThirteenNonadjacent.Initial15
import SquarePackingArchive.BentzThirteenNonadjacent.Final00
import SquarePackingArchive.BentzThirteenNonadjacent.Final01
import SquarePackingArchive.BentzThirteenNonadjacent.Final02
import SquarePackingArchive.BentzThirteenNonadjacent.Final03
import SquarePackingArchive.BentzThirteenNonadjacent.Final04
import SquarePackingArchive.BentzThirteenNonadjacent.Final05
import SquarePackingArchive.BentzThirteenNonadjacent.Final06
import SquarePackingArchive.BentzThirteenNonadjacent.Final07
import SquarePackingArchive.BentzThirteenNonadjacent.Final08
import SquarePackingArchive.BentzThirteenNonadjacent.Final09
import SquarePackingArchive.BentzThirteenNonadjacent.Final10
import SquarePackingArchive.BentzThirteenNonadjacent.Final11
import SquarePackingArchive.BentzThirteenNonadjacent.Final12
import SquarePackingArchive.BentzThirteenNonadjacent.Final13
import SquarePackingArchive.BentzThirteenNonadjacent.Final14
import SquarePackingArchive.BentzThirteenNonadjacent.Final15

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

theorem initial_cover (choices : Fin 4 → Bool) (square : PlacedSquare) (fits : square.Fits 4) :
    (∃ index, square.Contains (initialPoints choices index)) ∨ Hole square.center := by
  obtain ⟨choice, rfl⟩ := choicePattern_exhaustive choices
  fin_cases choice
  · exact initial00_cover square fits
  · exact initial01_cover square fits
  · exact initial02_cover square fits
  · exact initial03_cover square fits
  · exact initial04_cover square fits
  · exact initial05_cover square fits
  · exact initial06_cover square fits
  · exact initial07_cover square fits
  · exact initial08_cover square fits
  · exact initial09_cover square fits
  · exact initial10_cover square fits
  · exact initial11_cover square fits
  · exact initial12_cover square fits
  · exact initial13_cover square fits
  · exact initial14_cover square fits
  · exact initial15_cover square fits

theorem final_unavoidable (choices : Fin 4 → Bool) : Unavoidable (finalPoints choices) 4 := by
  obtain ⟨choice, rfl⟩ := choicePattern_exhaustive choices
  fin_cases choice
  · exact final00_cover
  · exact final01_cover
  · exact final02_cover
  · exact final03_cover
  · exact final04_cover
  · exact final05_cover
  · exact final06_cover
  · exact final07_cover
  · exact final08_cover
  · exact final09_cover
  · exact final10_cover
  · exact final11_cover
  · exact final12_cover
  · exact final13_cover
  · exact final14_cover
  · exact final15_cover

end SquarePackingArchive.BentzThirteen.Nonadjacent
