import SquarePackingArchive.BentzThirteenCoverGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

noncomputable def adjacentR2RightPoints (index : Fin 22) : Point :=
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
  | 10 => ⟨(5 / 2 : ℝ), (59 / 25 : ℝ)⟩
  | 11 => ⟨(5 / 2 : ℝ), (309 / 100 : ℝ)⟩
  | 12 => ⟨(3 : ℝ), (66 / 25 : ℝ)⟩
  | 13 => ⟨(5 / 2 : ℝ), (1 : ℝ)⟩
  | 14 => ⟨(3 : ℝ), (1 : ℝ)⟩
  | 15 => ⟨(2 : ℝ), (91 / 50 : ℝ)⟩
  | 16 => ⟨(3 : ℝ), (91 / 50 : ℝ)⟩
  | 17 => ⟨(1 : ℝ), (59 / 25 : ℝ)⟩
  | 18 => ⟨(3 / 2 : ℝ), (59 / 25 : ℝ)⟩
  | 19 => ⟨(1 : ℝ), (3 : ℝ)⟩
  | 20 => ⟨(9 / 5 : ℝ), (3 : ℝ)⟩
  | _ => ⟨(3 : ℝ), (3 : ℝ)⟩

def adjacentR2RightOutcome (square : PlacedSquare) : Prop :=
  (∃ index, square.Contains (adjacentR2RightPoints index))

end SquarePackingArchive.BentzThirteen
