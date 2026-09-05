import SquarePackingArchive.BentzThirteenNonadjacent
import SquarePackingArchive.BentzThirteenNonadjacentCount

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

theorem normalized_nonadjacent_impossible
    {family : Family} {first second : Fin 13} {other : Fin 16}
    (first_restricted : family.Restricted first 0)
    (second_restricted : family.Restricted second other)
    (other_lower : 2 ≤ other.val) (other_upper : other.val < 8) : False :=
  contradiction_of_normalized_nonadjacent initial_cover final_unavoidable
    first_restricted second_restricted other_lower other_upper

end SquarePackingArchive.BentzThirteen.Nonadjacent
