import SquarePackingArchive.BentzThirteenCoverGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

noncomputable def adjacentR4Points (index : Fin 23) : Point :=
  match index.val with
  | 0 => ⟨(1 : ℝ), (457 / 500 : ℝ)⟩
  | 1 => ⟨(113 / 100 : ℝ), (1 : ℝ)⟩
  | 2 => ⟨(7 / 5 : ℝ), (1 : ℝ)⟩
  | 3 => ⟨(3 / 2 : ℝ), (1 : ℝ)⟩
  | 4 => ⟨(87 / 50 : ℝ), (1 : ℝ)⟩
  | 5 => ⟨(187 / 100 : ℝ), (19 / 25 : ℝ)⟩
  | 6 => ⟨(457 / 500 : ℝ), (1 : ℝ)⟩
  | 7 => ⟨(1 : ℝ), (113 / 100 : ℝ)⟩
  | 8 => ⟨(1 : ℝ), (91 / 50 : ℝ)⟩
  | 9 => ⟨(19 / 25 : ℝ), (49 / 25 : ℝ)⟩
  | 10 => ⟨(3 / 2 : ℝ), (91 / 50 : ℝ)⟩
  | 11 => ⟨(3 / 2 : ℝ), (59 / 25 : ℝ)⟩
  | 12 => ⟨(1 : ℝ), (21 / 10 : ℝ)⟩
  | 13 => ⟨(2 : ℝ), (21 / 10 : ℝ)⟩
  | 14 => ⟨(5 / 2 : ℝ), (1 : ℝ)⟩
  | 15 => ⟨(31 / 10 : ℝ), (1 : ℝ)⟩
  | 16 => ⟨(12 / 5 : ℝ), (8 / 5 : ℝ)⟩
  | 17 => ⟨(31 / 10 : ℝ), (2 : ℝ)⟩
  | 18 => ⟨(12 / 5 : ℝ), (5 / 2 : ℝ)⟩
  | 19 => ⟨(9 / 10 : ℝ), (3 : ℝ)⟩
  | 20 => ⟨(17 / 10 : ℝ), (3 : ℝ)⟩
  | 21 => ⟨(5 / 2 : ℝ), (3 : ℝ)⟩
  | _ => ⟨(31 / 10 : ℝ), (3 : ℝ)⟩

def adjacentR4Outcome (square : PlacedSquare) : Prop :=
  (∃ index, square.Contains (adjacentR4Points index))

end SquarePackingArchive.BentzThirteen
