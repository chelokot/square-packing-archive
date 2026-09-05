import SquarePackingArchive.BentzThirteenCoverGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

noncomputable def adjacentR3Points (index : Fin 23) : Point :=
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
  | 10 => ⟨(5 / 2 : ℝ), (91 / 50 : ℝ)⟩
  | 11 => ⟨(5 / 2 : ℝ), (59 / 25 : ℝ)⟩
  | 12 => ⟨(3 : ℝ), (21 / 10 : ℝ)⟩
  | 13 => ⟨(23 / 10 : ℝ), (1 : ℝ)⟩
  | 14 => ⟨(61 / 20 : ℝ), (1 : ℝ)⟩
  | 15 => ⟨(9 / 5 : ℝ), (9 / 5 : ℝ)⟩
  | 16 => ⟨(3 : ℝ), (93 / 50 : ℝ)⟩
  | 17 => ⟨(1 : ℝ), (107 / 50 : ℝ)⟩
  | 18 => ⟨(2 : ℝ), (107 / 50 : ℝ)⟩
  | 19 => ⟨(19 / 20 : ℝ), (3 : ℝ)⟩
  | 20 => ⟨(3 / 2 : ℝ), (3 : ℝ)⟩
  | 21 => ⟨(23 / 10 : ℝ), (3 : ℝ)⟩
  | _ => ⟨(31 / 10 : ℝ), (3 : ℝ)⟩

def adjacentR3Outcome (square : PlacedSquare) : Prop :=
  (∃ index, square.Contains (adjacentR3Points index))

end SquarePackingArchive.BentzThirteen
