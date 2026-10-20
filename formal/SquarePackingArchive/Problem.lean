import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace SquarePackingArchive

structure Point where
  x : ℝ
  y : ℝ

structure Frame where
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1

def Frame.place (frame : Frame) (localX localY : ℝ) : Point :=
  ⟨localX * frame.cosine - localY * frame.sine,
    localX * frame.sine + localY * frame.cosine⟩

structure PlacedSquare where
  center : Point
  frame : Frame

def PlacedSquare.point (square : PlacedSquare) (localX localY : ℝ) : Point :=
  let offset := square.frame.place localX localY
  ⟨square.center.x + offset.x, square.center.y + offset.y⟩

def PlacedSquare.Contains (square : PlacedSquare) (point : Point) : Prop :=
  ∃ localX localY : ℝ,
    |localX| ≤ 1 / 2 ∧
      |localY| ≤ 1 / 2 ∧
        point = square.point localX localY

def PlacedSquare.InteriorContains (square : PlacedSquare) (point : Point) : Prop :=
  ∃ localX localY : ℝ,
    |localX| < 1 / 2 ∧
      |localY| < 1 / 2 ∧
        point = square.point localX localY

def Container.Contains (side : ℝ) (point : Point) : Prop :=
  0 ≤ point.x ∧ point.x ≤ side ∧ 0 ≤ point.y ∧ point.y ≤ side

def PlacedSquare.Fits (square : PlacedSquare) (side : ℝ) : Prop :=
  ∀ ⦃point⦄, square.Contains point → Container.Contains side point

def PlacedSquare.InteriorDisjoint (left right : PlacedSquare) : Prop :=
  ∀ point, ¬(left.InteriorContains point ∧ right.InteriorContains point)

structure Packing (squareCount : ℕ) (side : ℝ) where
  squares : Fin squareCount → PlacedSquare
  side_nonnegative : 0 ≤ side
  fits : ∀ index, (squares index).Fits side
  disjoint : ∀ left right, left ≠ right →
    (squares left).InteriorDisjoint (squares right)

def HasPacking (squareCount : ℕ) (side : ℝ) : Prop :=
  Nonempty (Packing squareCount side)

def IsLowerBound (squareCount : ℕ) (side : ℝ) : Prop :=
  ∀ candidateSide, HasPacking squareCount candidateSide → side ≤ candidateSide

def IsMinimumSide (squareCount : ℕ) (side : ℝ) : Prop :=
  HasPacking squareCount side ∧
    IsLowerBound squareCount side

end SquarePackingArchive
