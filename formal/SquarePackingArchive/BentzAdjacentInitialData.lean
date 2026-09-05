import SquarePackingArchive.BentzThirteenCoverGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

noncomputable def adjacentInitialPoints (index : Fin 20) : Point :=
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
  | 10 => ⟨(5 / 2 : ℝ), (1 : ℝ)⟩
  | 11 => ⟨(3 : ℝ), (1 : ℝ)⟩
  | 12 => ⟨(2 : ℝ), (91 / 50 : ℝ)⟩
  | 13 => ⟨(3 : ℝ), (91 / 50 : ℝ)⟩
  | 14 => ⟨(1 : ℝ), (59 / 25 : ℝ)⟩
  | 15 => ⟨(2 : ℝ), (59 / 25 : ℝ)⟩
  | 16 => ⟨(3 : ℝ), (59 / 25 : ℝ)⟩
  | 17 => ⟨(1 : ℝ), (309 / 100 : ℝ)⟩
  | 18 => ⟨(2 : ℝ), (309 / 100 : ℝ)⟩
  | _ => ⟨(3 : ℝ), (309 / 100 : ℝ)⟩

def adjacentInitialCriticalRegion (index : Fin 4) (center : Point) : Prop :=
  match index.val with
  | 0 => (1 : ℝ) ≤ center.x ∧ center.x ≤ (2 : ℝ) ∧ (59 / 25 : ℝ) ≤ center.y ∧ center.y ≤ (309 / 100 : ℝ)
  | 1 => (2 : ℝ) ≤ center.x ∧ center.x ≤ (3 : ℝ) ∧ (59 / 25 : ℝ) ≤ center.y ∧ center.y ≤ (309 / 100 : ℝ)
  | 2 => (2 : ℝ) ≤ center.x ∧ center.x ≤ (3 : ℝ) ∧ (91 / 50 : ℝ) ≤ center.y ∧ center.y ≤ (59 / 25 : ℝ)
  | _ => (1 : ℝ) ≤ center.x ∧ center.x ≤ (2 : ℝ) ∧ (91 / 50 : ℝ) ≤ center.y ∧ center.y ≤ (59 / 25 : ℝ)

def adjacentInitialOutcome (square : PlacedSquare) : Prop :=
  (∃ index, square.Contains (adjacentInitialPoints index)) ∨ ∃ region, adjacentInitialCriticalRegion region square.center

end SquarePackingArchive.BentzThirteen
