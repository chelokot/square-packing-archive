import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.GridBounds

theorem grid_hasPacking {count side : ℕ} (capacity : count ≤ side * side) :
    HasPacking count side :=
  (SquareNumbers.squareNumber_hasPacking side).mono capacity

end SquarePackingArchive.Records.GridBounds
